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

(* Minimal client for the chat API of an Ollama server.

   The request is sent over a plain socket, and the answer is awaited
   with [Unix.select] in short slices, calling [poll] in between: an
   engine runs in a domain that cannot be killed, so it must keep
   checking for termination while the model generates. Closing the
   socket makes Ollama stop generating.

   HTTP/1.0 is used on purpose: the server then neither chunks the
   answer nor keeps the connection open, so the body is everything
   after the headers up to the end of the stream.

   The answer is streamed, as one JSON object per line: a request that
   times out still has what the model produced so far, which tells where
   the time went. *)

module J = Yojson.Safe
module U = Yojson.Safe.Util

exception Error of string

let error fmt = Format.kasprintf (fun s -> raise (Error s)) fmt

type response = {
  content : string ;
  thinking : string option ;
  prompt_tokens : int option ;      (* Tokens of the prompt the model saw *)
  completion_tokens : int option ;
  done_reason : string option ;
  (* "stop", "length" when the token budget ran out, or "timeout" *)
  server_seconds : float option ;   (* Time the server reports *)
  wall_seconds : float ;            (* Time we waited *)
  raw : string ;                    (* Body of the HTTP response *)
}

(* Split ["http://host:port/prefix"] into host, port and path prefix. *)
let parse_endpoint url =
  let prefix = "http://" in
  let pl = String.length prefix in
  if String.length url < pl || String.sub url 0 pl <> prefix then
    error "only http:// endpoints are supported, got %s" url ;
  let rest = String.sub url pl (String.length url - pl) in
  let authority, path =
    match String.index_opt rest '/' with
    | None -> rest, ""
    | Some i -> String.sub rest 0 i, String.sub rest i (String.length rest - i)
  in
  let path =
    if path <> "" && path.[String.length path - 1] = '/'
    then String.sub path 0 (String.length path - 1) else path
  in
  let host, port =
    match String.rindex_opt authority ':' with
    | None -> authority, 80
    | Some i ->
      let p = String.sub authority (i + 1) (String.length authority - i - 1) in
      ( match int_of_string_opt p with
        | Some p -> String.sub authority 0 i, p
        | None -> error "bad port in endpoint %s" url )
  in
  host, port, path

let request_body ~model ~num_ctx ~max_tokens ~think ~system ~user =
  let think = match think with
    | None -> []
    | Some b -> [ "think", `Bool b ]
  in
  `Assoc ([
    "model", `String model ;
    "messages", `List [
      `Assoc [ "role", `String "system" ; "content", `String system ] ;
      `Assoc [ "role", `String "user" ; "content", `String user ] ;
    ] ;
    "stream", `Bool true ;
    "options", `Assoc [ "num_ctx", `Int num_ctx ; "num_predict", `Int max_tokens ] ;
  ] @ think)
  |> J.to_string

let connect host port =
  let addrs =
    try
      Unix.getaddrinfo host (string_of_int port)
        [ Unix.AI_SOCKTYPE Unix.SOCK_STREAM ]
    with Unix.Unix_error (e, _, _) ->
      error "cannot resolve %s: %s" host (String.trim (Unix.error_message e))
  in
  let rec try_addrs last_err = function
    | [] ->
      error "cannot connect to %s:%d: %s" host port last_err
    | a :: rest ->
      let fd = Unix.socket a.Unix.ai_family a.Unix.ai_socktype 0 in
      ( try Unix.connect fd a.Unix.ai_addr ; fd
        with Unix.Unix_error (e, _, _) ->
          (try Unix.close fd with _ -> ()) ;
          try_addrs (String.trim (Unix.error_message e)) rest )
  in
  try_addrs "no address" addrs

let send_all fd s =
  let b = Bytes.unsafe_of_string s in
  let len = Bytes.length b in
  let rec loop off =
    if off < len then
      let n = Unix.send fd b off (len - off) [] in
      loop (off + n)
  in
  loop 0

(* Read until the server closes the connection or the deadline, and tell
   which. [poll] is called about every [slice] seconds; it may raise to
   abandon the request. *)
let recv_all ~poll ~deadline fd =
  let buf = Buffer.create 65536 in
  let chunk = Bytes.create 65536 in
  let slice = 0.1 in
  let rec loop () =
    poll () ;
    if Unix.gettimeofday () > deadline then true
    else
      match Unix.select [ fd ] [] [] slice with
      | [], _, _ -> loop ()
      | _ ->
        let n = Unix.recv fd chunk 0 (Bytes.length chunk) [] in
        if n > 0 then (Buffer.add_subbytes buf chunk 0 n ; loop ())
        else false
      | exception Unix.Unix_error (Unix.EINTR, _, _) -> loop ()
  in
  let timed_out = loop () in
  Buffer.contents buf, timed_out

let split_http_response resp =
  let sep = "\r\n\r\n" in
  let rec find i =
    if i + 4 > String.length resp then None
    else if String.sub resp i 4 = sep then Some i
    else find (i + 1)
  in
  match find 0 with
  | None -> error "malformed HTTP response (%d bytes)" (String.length resp)
  | Some i ->
    let head = String.sub resp 0 i in
    let body = String.sub resp (i + 4) (String.length resp - i - 4) in
    let status_line =
      match String.index_opt head '\r' with
      | Some j -> String.sub head 0 j
      | None -> head
    in
    let status =
      match String.split_on_char ' ' status_line with
      | _ :: code :: _ -> int_of_string_opt code
      | _ -> None
    in
    status, body

(* The answer from its lines: the text of the lines adds up, and the last
   one has the statistics. A last line cut by a timeout is ignored. *)
let parse_body ~wall_seconds ~timed_out body =
  let opt f x = try f x with U.Type_error _ -> None in
  let lines =
    String.split_on_char '\n' body
    |> List.filter_map (fun l ->
      if String.trim l = "" then None
      else try Some (J.from_string l) with Yojson.Json_error _ -> None)
  in
  if lines = [] then
    error (if timed_out then "request timed out before any answer"
           else "answer is not JSON") ;
  let content = Buffer.create 1024 and thinking = Buffer.create 4096 in
  List.iter (fun json ->
    let message = U.member "message" json in
    let add buf key =
      match opt U.to_string_option (U.member key message) with
      | Some t -> Buffer.add_string buf t
      | None -> ()
    in
    add content "content" ;
    add thinking "thinking") lines ;
  let last = List.nth lines (List.length lines - 1) in
  let server_seconds =
    opt U.to_number_option (U.member "total_duration" last)
    |> Option.map (fun ns -> ns /. 1e9)
  in
  {
    content = Buffer.contents content ;
    thinking =
      if Buffer.length thinking = 0 then None
      else Some (Buffer.contents thinking) ;
    prompt_tokens = opt U.to_int_option (U.member "prompt_eval_count" last) ;
    completion_tokens = opt U.to_int_option (U.member "eval_count" last) ;
    done_reason =
      if timed_out then Some "timeout"
      else opt U.to_string_option (U.member "done_reason" last) ;
    server_seconds ; wall_seconds ; raw = body ;
  }

(* Send one chat request and wait for the answer. A timeout gives what the
   model produced so far. Raises [Error] on any other failure; exceptions
   raised by [poll] (termination) go through, and in every case the socket
   is closed. *)
let chat ~poll ~endpoint ~model ~num_ctx ~max_tokens ~think ~timeout
    ~system ~user =
  let host, port, prefix = parse_endpoint endpoint in
  let body = request_body ~model ~num_ctx ~max_tokens ~think ~system ~user in
  let request =
    Printf.sprintf
      "POST %s/api/chat HTTP/1.0\r\n\
       Host: %s:%d\r\n\
       Content-Type: application/json\r\n\
       Content-Length: %d\r\n\
       Connection: close\r\n\
       \r\n%s"
      prefix host port (String.length body) body
  in
  let start = Unix.gettimeofday () in
  let fd = connect host port in
  let resp, timed_out =
    Fun.protect ~finally:(fun () -> try Unix.close fd with _ -> ())
      (fun () ->
        try
          send_all fd request ;
          recv_all ~poll ~deadline:(start +. timeout) fd
        with Unix.Unix_error (e, f, _) ->
          error "%s: %s" f (String.trim (Unix.error_message e)))
  in
  let wall_seconds = Unix.gettimeofday () -. start in
  match split_http_response resp with
  | Some 200, body -> parse_body ~wall_seconds ~timed_out body
  | status, body ->
    let msg =
      try J.from_string body |> U.member "error" |> U.to_string
      with _ -> body
    in
    error "server answered %s: %s"
      (match status with Some s -> string_of_int s | None -> "?") msg
