(* This file is part of the Kind 2 model checker.

   Copyright (c) 2026 by the Board of Trustees of the University of Iowa

   Licensed under the Apache License, Version 2.0 (the "License"); you
   may not use this file except in compliance with the License.  You
   may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing
   permissions and limitations under the License.

*)

(* LLM-based invariant generation engine (LLMINV).

  For each property that is still unknown, ask the model for candidate
  invariants, record the exchange, then parse, check and broadcast only
  sound candidates. Multi-round feedback remains future work.

   All the state of the engine is local to [main]: an engine abandoned
   at the end of an analysis may still be running when the next
   analysis starts its own LLMINV. *)

module Client = LlmClient
module Prompt = LlmPrompt
module Lsd = LockStepDriver

let on_exit _ = ()

(* Create [dir] and its missing parents. *)
let rec mkdir_p dir =
  if not (Sys.file_exists dir) then (
    let parent = Filename.dirname dir in
    if parent <> dir then mkdir_p parent ;
    try Sys.mkdir dir 0o755 with Sys_error _ when Sys.file_exists dir -> ()
  )

let sanitize s =
  let s = String.map (fun c ->
    match c with
    | 'a'..'z' | 'A'..'Z' | '0'..'9' | '-' | '_' -> c
    | _ -> '_') s
  in
  if String.length s > 60 then String.sub s 0 60 else s

let timestamp () =
  let t = Unix.gettimeofday () in
  let tm = Unix.localtime t in
  Printf.sprintf "%04d%02d%02d-%02d%02d%02d-%03d"
    (tm.Unix.tm_year + 1900) (tm.Unix.tm_mon + 1) tm.Unix.tm_mday
    tm.Unix.tm_hour tm.Unix.tm_min tm.Unix.tm_sec
    (int_of_float (Float.rem t 1.0 *. 1000.))

let opt_int = function Some i -> string_of_int i | None -> "?"

(* Write one exchange as Markdown, and the raw answer as JSON next to
   it. Returns the path of the Markdown file. *)
let record ~dir ~prop ~(prompt : Prompt.t) result =
  mkdir_p dir ;
  let base =
    Filename.concat dir
      (Printf.sprintf "%s-%s" (timestamp ()) (sanitize prop))
  in
  let md = base ^ ".md" in
  Out_channel.with_open_bin md (fun oc ->
    let p fmt = Printf.fprintf oc fmt in
    p "# LLMINV exchange: %s\n\n" prop ;
    p "- input: %s\n" (Flags.input_file ()) ;
    p "- model: %s at %s\n" (Flags.Llm.model ()) (Flags.Llm.endpoint ()) ;
    p "- num_ctx: %d, estimated prompt tokens: %d\n"
      (Flags.Llm.num_ctx ()) prompt.approx_tokens ;
    ( match result with
      | Ok (r : Client.response) ->
        p "- prompt tokens seen by the model: %s\n" (opt_int r.prompt_tokens) ;
        p "- generated tokens: %s\n" (opt_int r.completion_tokens) ;
        p "- stop reason: %s\n"
          (match r.done_reason with Some s -> s | None -> "?") ;
        p "- wall time: %.1f s\n" r.wall_seconds
      | Error msg -> p "- error: %s\n" msg ) ;
    p "\n## System prompt\n\n%s\n\n## User prompt\n\n%s\n"
      prompt.system prompt.user ;
    ( match result with
      | Ok r ->
        ( match r.thinking with
          | Some t -> p "\n## Model thinking\n\n%s\n" t
          | None -> () ) ;
        p "\n## Model answer\n\n%s\n" r.content
      | Error _ -> () )
  ) ;
  ( match result with
    | Ok r ->
      Out_channel.with_open_bin (base ^ ".json") (fun oc ->
        output_string oc r.raw)
    | Error _ -> () ) ;
  md

(* Properties still worth asking about. *)
let unknown_props sys =
  TransSys.get_real_properties sys
  |> List.filter (fun p ->
    not (Property.prop_status_known (Property.get_prop_status p)))

exception Server_unavailable

(* Write to the standard error, outside of the log: kmoxi turns the log
   off to keep its standard output a clean SMT-LIB response, so
   [--llm_print] is the only way to watch the engine there. One write per
   message, so that messages of other domains do not interleave. *)
let eprint fmt =
  Format.kasprintf (fun s -> prerr_string s ; flush stderr) fmt

let print_level () = Flags.Llm.print ()

(* Log [msg], and also print it on the standard error under
   [--llm_print]. *)
let say level msg =
  KEvent.log level "%s" msg ;
  if print_level () <> `None then eprint "%s\n" msg

let section title body =
  Printf.sprintf "----- %s -----\n%s\n" title (String.trim body)

let print_exchange ~name ~(prompt : Prompt.t) ~path result =
  match print_level () with
  | `None -> ()
  | level ->
    let all = level = `All in
    let prompts =
      if all then
        section "system prompt" prompt.system
        ^ section "user prompt" prompt.user
      else ""
    in
    let body =
      match result with
      | Ok (r : Client.response) ->
        let thinking =
          match r.thinking with
          | Some t when all -> section "model thinking" t
          | _ -> ""
        in
        let answer =
          if String.trim r.content = "" then "(empty)" else r.content
        in
        thinking ^ section "model answer" answer
      | Error msg -> section "request failed" msg
    in
    let record =
      match path with Some p -> "full record: " ^ p ^ "\n" | None -> ""
    in
    eprint "\n===== LLMINV: %s =====\n%s%s%s\n" name prompts body record

let check_candidates in_sys sys prop rendered answer =
  let parsed = LlmCandidate.parse rendered sys answer in
  List.iter (fun (text, reason) ->
    KEvent.log L_debug "LLMINV: rejected candidate %S: %s" text reason
  ) parsed.rejected ;
  KEvent.log L_note "LLMINV: parsed %d candidates, rejected %d"
    (List.length parsed.terms) (List.length parsed.rejected) ;
  match parsed.terms with
  | [] -> ()
  | candidates ->
    let base_holds term =
      let base = Lsd.mk_base_checker in_sys sys Numeral.zero in
      Fun.protect
        ~finally:(fun () -> Lsd.kill_base base)
        (fun () -> Lsd.query_base in_sys base [term] = None)
    in
    let base_candidates =
      List.filter (fun term ->
        try base_holds term with error ->
          KEvent.log L_debug "LLMINV: base check rejected candidate: %s"
            (Printexc.to_string error) ;
          false
      ) candidates
    in
    if base_candidates = [] then (
      KEvent.log L_note "LLMINV: no candidate holds in every initial state"
    ) else (
      let prop_term = prop.Property.prop_term in
      let prop_base =
        try base_holds prop_term with error ->
          KEvent.log L_warn "LLMINV: cannot check initial property: %s"
            (Printexc.to_string error) ;
          false
      in
      let candidates =
        if prop_base then base_candidates @ [prop_term] else base_candidates
      in
      let base = Lsd.mk_base_checker in_sys sys Numeral.zero in
      let step =
        try Lsd.to_step base with error ->
          Lsd.kill_base base ;
          raise error
      in
      Fun.protect
        ~finally:(fun () -> Lsd.kill_step step)
        (fun () ->
          let survivors =
            Lsd.query_step false in_sys step
              (List.map (fun term -> term, ()) candidates)
            |> List.map fst
          in
          let property_survives =
            prop_base && List.exists (Term.equal prop_term) survivors
          in
          let invariant_terms =
            if property_survives then survivors
            else List.filter (fun term -> not (Term.equal term prop_term)) survivors
          in
          match invariant_terms with
          | [] -> KEvent.log L_note "LLMINV: no inductive candidate survived"
          | terms ->
            let invariant = Term.mk_and terms in
            let cert = Lsd.step_cert step, invariant in
            let pruning = Lsd.mk_pruning_checker in_sys sys in
            let nontrivial =
              Fun.protect
                ~finally:(fun () -> Lsd.kill_pruning pruning)
                (fun () ->
                  let nontrivial, _ =
                    Lsd.query_pruning in_sys pruning [invariant]
                  in
                  nontrivial <> [])
            in
            if nontrivial then (
              let invariant =
                TransSys.add_invariant sys invariant cert false
              in
              KEvent.invariant
                (TransSys.scope_of_trans_sys sys) invariant cert false ;
              KEvent.log L_note "LLMINV: broadcast %d checked candidate(s)"
                (List.length terms)
            ) else
              KEvent.log L_note "LLMINV: surviving conjunction is transition-trivial" ;
            if property_survives then (
              ignore (KEvent.prop_invariant sys prop.Property.prop_name cert) ;
              KEvent.log L_info "LLMINV: proved %s with checked candidates"
                prop.Property.prop_name
            )
        )
    )

let main in_sys param sys =

  (* Keep the local system up to date and react to termination. Called
     between requests and every 100 ms while waiting for an answer. *)
  let poll () =
    KEvent.check_termination () ;
    KEvent.recv () |> KEvent.update_trans_sys in_sys param sys |> ignore
  in

  let ask analysis prop =
    let name = prop.Property.prop_name in
    let prompt = Prompt.mk in_sys analysis sys prop in
    if Flags.Llm.print_ts () = `Normal then
      eprint "\n===== LLMINV: %s =====\n%s\n" name prompt.user ;
    let num_ctx = Flags.Llm.num_ctx () in
    if prompt.approx_tokens > num_ctx then
      Printf.sprintf
        "LLMINV: the prompt for %s is about %d tokens, more than \
         --llm_num_ctx %d; the model will not see its beginning."
        name prompt.approx_tokens num_ctx
      |> say L_warn ;
    Printf.sprintf "LLMINV: asking %s about %s (about %d tokens)"
      (Flags.Llm.model ()) name prompt.approx_tokens
    |> say L_note ;
    let result =
      try
        Ok (match Flags.Llm.replay () with
          | Some path -> Client.replay path
          | None ->
            Client.chat ~poll
              ~endpoint:(Flags.Llm.endpoint ()) ~model:(Flags.Llm.model ())
              ~num_ctx ~max_tokens:(Flags.Llm.max_tokens ())
              ~think:(Flags.Llm.think ())
              ~timeout:(Flags.Llm.timeout ())
              ~system:prompt.system ~user:prompt.user)
      with Client.Error msg -> Error msg
    in
    let dir = Flags.Llm.log_dir () in
    let path =
      try Some (record ~dir ~prop:name ~prompt result)
      with Sys_error msg ->
        KEvent.log L_warn "LLMINV: cannot write to %s: %s" dir msg ;
        None
    in
    let where = match path with Some p -> ", recorded in " ^ p | None -> "" in
    match result with
    | Ok r ->
      (try check_candidates in_sys sys prop prompt.rendered r.content with
       | KEvent.Terminate as error -> raise error
       | error ->
         say L_warn ("LLMINV: candidate checking failed: "
                     ^ Printexc.to_string error)) ;
      Printf.sprintf
        "LLMINV: answer for %s after %.1f s (%s prompt tokens, %s \
         generated)%s"
        name r.wall_seconds (opt_int r.prompt_tokens)
        (opt_int r.completion_tokens) where
      |> say L_note ;
      ( match r.prompt_tokens with
        | Some n when n >= num_ctx ->
          Printf.sprintf
            "LLMINV: the model saw %d prompt tokens, the whole context: \
             the prompt was probably truncated." n
          |> say L_warn
        | _ -> () ) ;
      let answer_state () =
        if String.trim r.content = "" then "empty" else "cut short"
      in
      ( match r.done_reason with
        | Some "length" ->
          Printf.sprintf
            "LLMINV: the model ran out of tokens after %s prompt and %s \
             generated tokens, so its answer is %s. Raise --llm_max_tokens \
             or --llm_num_ctx, or try --llm_think false."
            (opt_int r.prompt_tokens) (opt_int r.completion_tokens)
            (answer_state ())
          |> say L_warn
        | Some "timeout" ->
          Printf.sprintf
            "LLMINV: the model ran out of time after %.0f s, so its answer \
             is %s. Raise --llm_timeout, lower --llm_max_tokens, or try \
             --llm_think false."
            r.wall_seconds (answer_state ())
          |> say L_warn
        | _ -> () ) ;
      KEvent.log L_info "@[<v>LLMINV: answer for %s:@,%s@]" name r.content ;
      print_exchange ~name ~prompt ~path result
    | Error msg ->
      Printf.sprintf "LLMINV: request for %s failed: %s%s" name msg where
      |> say L_warn ;
      print_exchange ~name ~prompt ~path result ;
      raise Server_unavailable
  in

  let rec loop analysis = function
    | [] -> ()
    | prop :: rest ->
      poll () ;
      (* Skip properties settled by other engines in the meantime. *)
      let name = prop.Property.prop_name in
      if Property.prop_status_known (TransSys.get_prop_status sys name)
      then loop analysis rest
      else (ask analysis prop ; loop analysis rest)
  in

  let check analysis =
    if Flags.Llm.check_ts () then
      let msg =
        match LlmTransSys.check analysis with
        | LlmTransSys.Equivalent ->
          "LLMINV: check of the transition system: equivalent"
        | LlmTransSys.Different what ->
          "LLMINV: check of the transition system: DIFFERENT " ^ what
        | LlmTransSys.Inconclusive what ->
          "LLMINV: check of the transition system: inconclusive on " ^ what
      in
      eprint "%s\n" msg
  in

  if Flags.Llm.print_ts () = `Raw then
    eprint "%a@." (TransSys.pp_print_subsystems true) sys ;

  match unknown_props sys with
  | [] -> KEvent.log L_info "LLMINV: no unknown property."
  | props ->
    (* The analysis must never depend on this engine: a failure, of the
       model server or to read the system, only ends the engine. *)
    try
      let analysis = LlmTransSys.analyze sys in
      check analysis ;
      loop analysis props
    with
    | Server_unavailable -> ()
    | KEvent.Terminate as e -> raise e
    | e when not (EngineDomains.is_terminating ()) ->
      say L_warn ("LLMINV: giving up: " ^ Printexc.to_string e)
