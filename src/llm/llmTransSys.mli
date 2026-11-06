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

(** A readable normal form of a transition system, for a language model.

    @author Kind 2 development team *)

(** The structure recovered from a transition system: subsystems inlined,
    intermediate inputs eliminated, the relation split into what holds at
    every step and a choice between guarded transitions. *)
type analysis

(** The analysis of a system. The work is shared by all its properties. *)
val analyze : TransSys.t -> analysis

(** A system as text, restricted to what a property depends on. *)
type rendered = {
  text : string ;
  (** The system: variables, locations, initial states, transitions *)
  goal_text : string ;
  (** The property as a condition on the state *)
  symbols : (string * Term.t) list ;
  (** Unquoted names printed for state variables and locations, resolved to
      their current-state terms. Duplicate names are retained as ambiguous. *)
  state_count : int ;
  (** Number of state variables printed *)
  omitted_count : int ;
  (** Number of state variables the property does not depend on *)
}

(** Print a system for a property of it. *)
val render : 'a InputSystem.t -> analysis -> Property.t -> rendered

(** Result of {!check}. *)
type check_result =
  | Equivalent
  | Different of string
  (** What differs: the initial states or the transition relation *)
  | Inconclusive of string
  (** What the solver could not decide *)

(** Have a solver check that the structure is equivalent to the system,
    up to the inputs it eliminated. Uses the SMT solver selected for the
    analysis, which must support quantifiers if inputs were eliminated. *)
val check : analysis -> check_result
