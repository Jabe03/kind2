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

(** Minimal client for the chat API of an Ollama server.

    @author Kind 2 development team *)

(** Failure of a request: server unreachable, timeout, HTTP error or
    malformed answer. *)
exception Error of string

(** Answer to a chat request. *)
type response = {
  content : string ;
  (** Text of the answer *)
  thinking : string option ;
  (** Reasoning trace, for models that think *)
  prompt_tokens : int option ;
  (** Number of prompt tokens the model processed. When equal to the
      context size, the prompt was probably truncated. *)
  completion_tokens : int option ;
  (** Number of generated tokens *)
  done_reason : string option ;
  (** Why generation stopped: ["stop"] when the model finished, ["length"]
      when it ran out of context or token budget, ["timeout"] when the time
      ran out. In the last two cases the answer is cut short or empty. *)
  server_seconds : float option ;
  (** Total time reported by the server *)
  wall_seconds : float ;
  (** Time spent waiting for the answer *)
  raw : string ;
  (** Body of the HTTP response *)
}

(** [chat ~poll ~endpoint ~model ~num_ctx ~max_tokens ~think ~timeout ~system
    ~user] sends one request to [endpoint/api/chat] and waits for the answer,
    calling [poll] about every 100 ms. After [timeout] seconds it returns what
    the model produced so far. An exception raised by
    [poll] abandons the request and closes the connection, which stops
    the generation on the server.

    @raise Error on any failure of the request. *)
val chat :
  poll:(unit -> unit) ->
  endpoint:string ->
  model:string ->
  num_ctx:int ->
  max_tokens:int ->
  think:bool option ->
  timeout:float ->
  system:string ->
  user:string ->
  response
