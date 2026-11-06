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

(** Prompts asking a language model for candidate invariants of a transition
    system.

    @author Kind 2 development team *)

(** A prompt: system message, user message, and a rough estimate of its
    size in tokens. *)
type t = {
  system : string ;
  user : string ;
  approx_tokens : int ;
}

(** [mk in_sys analysis sys prop] is the prompt asking for invariants that
    help prove [prop] of the top-level system [sys], [analysis] being the
    analysis of [sys]. *)
val mk :
  'a InputSystem.t -> LlmTransSys.analysis -> TransSys.t -> Property.t -> t
