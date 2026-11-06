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

(** LLM-based invariant generation engine (LLMINV).

    Currently a skeleton: it asks the model about each unknown property
    and records the exchange, without using the answer.

    @author Kind 2 development team *)

(** Entry point of the engine. *)
val main : 'a InputSystem.t -> Analysis.param -> TransSys.t -> unit

(** Cleanup before exit. *)
val on_exit : TransSys.t option -> unit
