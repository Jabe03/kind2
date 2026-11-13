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

(* Candidates checked while the model is still writing.

   A model that thinks writes the invariant it is after long before its
   answer, and often runs out of tokens before giving one. So the thinking and
   the answer are read as they arrive, and every new candidate is checked
   without waiting for the end. The property proved, the request ends.

   Models repeat themselves: in recorded traces, about two thirds of the
   candidates written are repeats. Nothing is sent to a solver twice:

   - a line already seen, up to white space, is not even parsed;
   - a term already seen is not checked again;
   - a term false in an initial state is never looked at again;
   - a term that holds initially but is not inductive yet stays in a pool,
     since a later candidate may make it inductive: the pool is checked again
     only together with new candidates.

   Candidates are checked in batches, at most once every [interval] seconds,
   on solvers kept for the whole request. *)

module Lsd = LockStepDriver
module TH = Term.TermHashtbl

type 'a t = {
  in_sys : 'a InputSystem.t ;
  sys : TransSys.t ;
  prop : Property.t ;
  rendered : LlmTransSys.rendered ;
  interval : float ;
  start : float ;

  (* Text not yet cut into lines *)
  thinking_buf : Buffer.t ;
  content_buf : Buffer.t ;

  seen_lines : (string, unit) Hashtbl.t ;
  seen_fragments : (string, unit) Hashtbl.t ;
  (* Each term seen, with where it was first found *)
  seen_terms : string TH.t ;
  (* Number of distinct terms by where they were found *)
  sources : (string, int) Hashtbl.t ;

  (* Candidates not checked yet, latest first *)
  mutable fresh : Term.t list ;
  (* Candidates true initially, not inductive so far *)
  mutable pool : Term.t list ;
  (* Candidates proved and broadcast *)
  proven : unit TH.t ;

  mutable last_check : float ;
  mutable base : Lsd.base option ;
  mutable step : Lsd.step option ;
  mutable pruning : Lsd.pruning option ;
  mutable prop_base : bool option ;

  (* Statistics *)
  mutable lines : int ;
  mutable line_repeats : int ;
  mutable terms : int ;
  mutable term_repeats : int ;
  mutable rejected : int ;
  mutable base_false : int ;
  mutable base_queries : int ;
  mutable batches : int ;
  mutable broadcast : int ;
  mutable errors : int ;
  mutable first_candidate_at : float option ;
  mutable proved_at : float option ;
  mutable timeline : string list ;
}

let create ~interval in_sys sys prop rendered =
  let now = Unix.gettimeofday () in
  {
    in_sys ; sys ; prop ; rendered ; interval ; start = now ;
    thinking_buf = Buffer.create 4096 ; content_buf = Buffer.create 1024 ;
    seen_lines = Hashtbl.create 97 ; seen_fragments = Hashtbl.create 97 ;
    seen_terms = TH.create 97 ; sources = Hashtbl.create 3 ;
    fresh = [] ; pool = [] ; proven = TH.create 17 ;
    last_check = now ;
    base = None ; step = None ; pruning = None ; prop_base = None ;
    lines = 0 ; line_repeats = 0 ;
    terms = 0 ; term_repeats = 0 ;
    rejected = 0 ; base_false = 0 ; base_queries = 0 ; batches = 0 ;
    broadcast = 0 ; errors = 0 ;
    first_candidate_at = None ; proved_at = None ; timeline = [] ;
  }

let elapsed s = Unix.gettimeofday () -. s.start

let note s fmt =
  Format.kasprintf (fun m ->
    s.timeline <- Printf.sprintf "%6.1f s  %s" (elapsed s) m :: s.timeline)
    fmt

let proved s = s.proved_at <> None

(* {1 Solvers} *)

let kill_base s =
  Option.iter (fun b -> try Lsd.kill_base b with _ -> ()) s.base ;
  s.base <- None

let kill_step s =
  Option.iter (fun st -> try Lsd.kill_step st with _ -> ()) s.step ;
  s.step <- None

let close s =
  kill_base s ;
  kill_step s ;
  Option.iter (fun p -> try Lsd.kill_pruning p with _ -> ()) s.pruning ;
  s.pruning <- None

let base s =
  match s.base with
  | Some b -> b
  | None ->
    let b = Lsd.mk_base_checker s.in_sys s.sys Numeral.zero in
    s.base <- Some b ;
    b

let step s =
  match s.step with
  | Some st -> st
  | None ->
    let b = Lsd.mk_base_checker s.in_sys s.sys Numeral.zero in
    let st =
      try Lsd.to_step b with e -> (try Lsd.kill_base b with _ -> ()) ; raise e
    in
    s.step <- Some st ;
    st

let pruning s =
  match s.pruning with
  | Some p -> p
  | None ->
    let p = Lsd.mk_pruning_checker s.in_sys s.sys in
    s.pruning <- Some p ;
    p

(* Whether a term holds in every initial state. A term the solver rejects,
   for instance one outside the logic of the system, does not, and the base
   checker it broke is replaced. *)
let holds_initially s term =
  s.base_queries <- s.base_queries + 1 ;
  try Lsd.query_base s.in_sys (base s) [ term ] = None
  with
  | KEvent.Terminate as e -> raise e
  | e ->
    s.errors <- s.errors + 1 ;
    note s "solver rejected a candidate: %s" (Printexc.to_string e) ;
    kill_base s ;
    false

(* {1 Reading the stream} *)

let normalize line = String.concat " " (String.split_on_char ' ' line
  |> List.concat_map (String.split_on_char '\t')
  |> List.filter (fun w -> w <> ""))

let pp_term = Format.asprintf "%a" Term.pp_print_term

(* The terms written in backquotes in a line of prose. Models write their
   candidates inside sentences long before they put one on a line of its
   own: on llm_inv_hard.lus, at 39% of the reasoning rather than at 99%. *)
let quoted_terms line =
  String.split_on_char '`' line
  |> List.filteri (fun i _ -> i mod 2 = 1)
  |> List.map String.trim
  |> List.filter (fun t -> String.length t > 1 && t.[0] = '(')

(* Candidates of a line, each with where it was found: a term in
   backquotes, or a line that is only a term. *)
let fragments_of_line key =
  let quoted = List.map (fun t -> t, "backquotes") (quoted_terms key) in
  let whole =
    let bare =
      String.concat "" (String.split_on_char '`' key)
      |> LlmCandidate.clean_line
    in
    if bare <> "" && (bare.[0] = '(' || not (String.contains bare ' '))
    then [ bare, "line" ] else []
  in
  (* A line that is only a quoted term gives it twice: once is enough *)
  quoted
  @ List.filter (fun (t, _) ->
      not (List.exists (fun (q, _) -> normalize q = normalize t) quoted))
      whole

let take_term s source term =
  s.terms <- s.terms + 1 ;
  if Term.equal term Term.t_true || TH.mem s.seen_terms term then
    s.term_repeats <- s.term_repeats + 1
  else (
    TH.add s.seen_terms term source ;
    Hashtbl.replace s.sources source
      (1 + Option.value ~default:0 (Hashtbl.find_opt s.sources source)) ;
    if s.first_candidate_at = None then
      s.first_candidate_at <- Some (elapsed s) ;
    note s "new candidate (%s): %s" source (pp_term term) ;
    s.fresh <- term :: s.fresh
  )

let take_line s line =
  let key = normalize (String.trim line) in
  if key <> "" then (
    s.lines <- s.lines + 1 ;
    if Hashtbl.mem s.seen_lines key then s.line_repeats <- s.line_repeats + 1
    else (
      Hashtbl.add s.seen_lines key () ;
      List.iter (fun (fragment, source) ->
        let fkey = normalize fragment in
        (* The same fragment in another line: already parsed *)
        if not (Hashtbl.mem s.seen_fragments fkey) then (
          Hashtbl.add s.seen_fragments fkey () ;
          let parsed = LlmCandidate.parse s.rendered s.sys fragment in
          s.rejected <- s.rejected + List.length parsed.rejected ;
          List.iter (take_term s source) parsed.terms
        )) (fragments_of_line key)
    )
  )

(* The complete lines of a buffer, the rest kept for later *)
let complete_lines buf =
  let text = Buffer.contents buf in
  match String.rindex_opt text '\n' with
  | None -> []
  | Some i ->
    Buffer.clear buf ;
    Buffer.add_string buf (String.sub text (i + 1) (String.length text - i - 1)) ;
    String.split_on_char '\n' (String.sub text 0 i)

let feed s ~thinking ~content =
  Buffer.add_string s.thinking_buf thinking ;
  Buffer.add_string s.content_buf content ;
  List.iter (take_line s) (complete_lines s.thinking_buf) ;
  List.iter (take_line s) (complete_lines s.content_buf)

(* What remains once the stream is over *)
let flush s =
  let rest buf =
    let text = Buffer.contents buf in
    Buffer.clear buf ;
    if text <> "" then take_line s text
  in
  rest s.thinking_buf ;
  rest s.content_buf

(* {1 Checking} *)

(* [terms] are proved together, [count] of them invariants the model
   proposed, the others are the property *)
let broadcast s ~count terms cert =
  let invariant = Term.mk_and terms in
  let nontrivial =
    try
      let nontrivial, _ = Lsd.query_pruning s.in_sys (pruning s) [ invariant ] in
      nontrivial <> []
    with
    | KEvent.Terminate as e -> raise e
    | _ -> true
  in
  if nontrivial then (
    let invariant = TransSys.add_invariant s.sys invariant cert false in
    KEvent.invariant (TransSys.scope_of_trans_sys s.sys) invariant cert false ;
    (* Known from now on, in the checks to come *)
    Option.iter (fun st -> Lsd.step_add_invariants st false [ invariant ]) s.step ;
    Option.iter (fun b -> Lsd.base_add_invariants b false [ invariant ]) s.base ;
    s.broadcast <- s.broadcast + count ;
    note s "broadcast %d invariant(s) as one: %s" count
      (String.concat " " (List.map pp_term terms))
  )
  else note s "surviving candidates are implied by the transition relation"

let check s =
  let batch = List.rev s.fresh in
  s.fresh <- [] ;
  s.last_check <- Unix.gettimeofday () ;
  s.batches <- s.batches + 1 ;
  let initial = List.filter (holds_initially s) batch in
  s.base_false <- s.base_false + List.length batch - List.length initial ;
  let pool = s.pool @ initial in
  if pool <> [] then (
    let prop_term = s.prop.Property.prop_term in
    let prop_base =
      match s.prop_base with
      | Some b -> b
      | None ->
        let b = holds_initially s prop_term in
        s.prop_base <- Some b ;
        b
    in
    let candidates = if prop_base then pool @ [ prop_term ] else pool in
    match
      Lsd.query_step false s.in_sys (step s)
        (List.map (fun t -> t, ()) candidates)
    with
    | exception (KEvent.Terminate as e) -> raise e
    | exception e ->
      (* The pool is kept for the next batch, on new solvers *)
      s.errors <- s.errors + 1 ;
      note s "step check failed: %s" (Printexc.to_string e) ;
      s.pool <- pool ;
      kill_step s
    | survivors ->
      let survivors = List.map fst survivors in
      let prop_survives = prop_base && List.exists (Term.equal prop_term) survivors in
      let is_prop t = Term.equal t prop_term in
      let inv_terms = List.filter (fun t -> not (is_prop t)) survivors in
      let new_terms = List.filter (fun t -> not (TH.mem s.proven t)) inv_terms in
      s.pool <-
        List.filter (fun t ->
          not (List.exists (Term.equal t) survivors)) pool ;
      note s "batch %d: %d new, %d initially false, %d in pool, %d inductive"
        s.batches (List.length batch)
        (List.length batch - List.length initial)
        (List.length s.pool) (List.length inv_terms) ;
      if new_terms <> [] || prop_survives then (
        let st = step s in
        let terms = if prop_survives then survivors else inv_terms in
        let cert = Lsd.step_cert st, Term.mk_and terms in
        if new_terms <> [] then
          broadcast s ~count:(List.length new_terms) terms cert ;
        List.iter (fun t -> TH.replace s.proven t ()) inv_terms ;
        if prop_survives then (
          ignore (KEvent.prop_invariant s.sys s.prop.Property.prop_name cert) ;
          LlmUse.record_proved ~prop:s.prop.Property.prop_name ~terms:inv_terms ;
          s.proved_at <- Some (elapsed s) ;
          note s "proved %s" s.prop.Property.prop_name ;
          raise LlmClient.Stop
        )
      )
  )

(* Check the pending candidates if it is time, or now with [~force]. Raises
   [LlmClient.Stop] once the property is proved. *)
let maybe_check ?(force = false) s =
  if (not (proved s)) && s.fresh <> []
  && (force || Unix.gettimeofday () -. s.last_check >= s.interval)
  then check s

(* {1 Report} *)

let summary s =
  let opt = function Some t -> Printf.sprintf "%.1f s" t | None -> "-" in
  String.concat "\n" (
    [
      Printf.sprintf "- lines read: %d, of which repeated: %d" s.lines s.line_repeats ;
      Printf.sprintf "- distinct candidates by where they were found: %s"
        (match Hashtbl.fold (fun k v acc -> Printf.sprintf "%s %d" k v :: acc)
                 s.sources [] with
         | [] -> "none"
         | l -> String.concat ", " (List.sort compare l)) ;
      Printf.sprintf "- candidate terms: %d, of which repeated: %d; rejected by the parser: %d"
        s.terms s.term_repeats s.rejected ;
      Printf.sprintf "- distinct candidates checked: %d, false initially: %d, still in the pool: %d"
        (TH.length s.seen_terms) s.base_false (List.length s.pool) ;
      Printf.sprintf "- solver work: %d base queries, %d step batches, %d errors"
        s.base_queries s.batches s.errors ;
      Printf.sprintf "- invariants broadcast: %d" s.broadcast ;
      Printf.sprintf "- first candidate after %s, property proved after %s"
        (opt s.first_candidate_at) (opt s.proved_at) ;
      "" ; "Timeline:" ; "" ;
    ]
    @ List.rev_map (fun l -> "    " ^ l) s.timeline)
