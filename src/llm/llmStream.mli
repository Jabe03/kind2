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

(** Candidates checked while the model is still writing, without ever
    checking the same one twice.

    @author Kind 2 development team *)

(** The candidates of one request for one property, and the solvers that
    check them. *)
type 'a t

(** [create ~interval in_sys sys prop rendered]: candidates are checked at
    most once every [interval] seconds. [rendered] gives the meaning of the
    names the model was told of. *)
val create :
  interval:float -> 'a InputSystem.t -> TransSys.t -> Property.t ->
  LlmTransSys.rendered -> 'a t

(** Read new pieces of the thinking and of the answer. Complete lines are
    parsed into candidates; partial lines wait for the rest. *)
val feed : 'a t -> thinking:string -> content:string -> unit

(** Read the last, incomplete lines, once the stream is over. *)
val flush : 'a t -> unit

(** Check the new candidates, if the interval has passed or with [~force].
    Candidates that are proved together are broadcast. Raises
    {!LlmClient.Stop} when the property is proved. *)
val maybe_check : ?force:bool -> 'a t -> unit

(** Whether the property was proved. *)
val proved : 'a t -> bool

(** Release the solvers. *)
val close : 'a t -> unit

(** Statistics and timeline, as Markdown. *)
val summary : 'a t -> string
