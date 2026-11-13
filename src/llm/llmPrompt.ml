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

(* Prompts for candidate invariants, at the level of the transition system:
   the model is told of the system as Kind 2 reasons on it (see
   {!LlmTransSys}), whatever the input language, and answers with terms over
   its state variables.

   Not there yet: the counterexample to induction, and the invariants
   already known. *)

type t = {
  system : string ;
  user : string ;
  approx_tokens : int ;
  rendered : LlmTransSys.rendered ;
}

(* Rough, deliberately high count: plain code averages 3 to 4 characters
   per token, but generated SMT-LIB only about 2. An estimate that runs low
   would hide truncation. *)
let approx_tokens s = String.length s / 2

(* The syntax of the theories of the system, as the model tends to make up
   operators that do not exist. *)
let theory_notes sys =
  let types =
    List.map StateVar.type_of_state_var (TransSys.state_vars sys)
  in
  let has p = List.exists p types in
  let is_bv t = Type.is_bitvector t || Type.is_ubitvector t in
  List.concat [
    [ "Use prefix SMT-LIB syntax: (=> a b), (and a b), (or a b), (not a), \
       (= a b), (ite c a b). Infix forms such as a -> b do not exist." ] ;
    if has is_bv then
      [ "Bit vectors are compared with bvult, bvule, bvugt, bvuge (unsigned) \
         and bvslt, bvsle, bvsgt, bvsge (signed), never with < or <=. Other \
         operators are bvadd, bvsub, bvmul, bvand, bvor, bvxor, bvnot, \
         concat and (_ extract i j). Constants are #x (4 bits per digit) or \
         #b (1 bit per digit), and both sides of an operator have the same \
         width." ]
    else [] ;
    if has (fun t -> Type.is_int t || Type.is_int_range t || Type.is_real t)
    then
      [ "Arithmetic uses +, -, *, div, mod, <, <=, >, >=. (mod e k) with a \
         constant k > 0 is always between 0 and k-1, also when e is \
         negative." ]
    else [] ;
    if has Type.is_array then
      [ "Arrays are read with (select a i)." ]
    else [] ;
  ]

(* Whether [sub] occurs in [s] *)
let contains s sub =
  let n = String.length s and m = String.length sub in
  let rec at i = i + m <= n && (String.sub s i m = sub || at (i + 1)) in
  at 0

(* The instructions only mention what the system has: models spend their
   reasoning on whatever the prompt mentions, relevant or not. They also
   settle in advance the questions models otherwise keep asking themselves
   (how many candidates, whether an operator exists, what the rules mean),
   which can use up the whole token budget before any answer. *)
let system_prompt sys (r : LlmTransSys.rendered) =
  let has_locations = contains r.text "## Control locations" in
  let has_inputs = contains r.text "## Inputs" in
  let only_if c l = if c then l else [] in
  let allowed =
    Printf.sprintf
      "A candidate may only mention state variables, in their current \
       value%s. It never mentions next values (v'), %sabbreviations such as \
       _e1, or quantifiers."
      (if has_locations then ", and location names" else "")
      (if has_inputs then "inputs, " else "")
  in
  String.concat " " (List.concat [
    [ "You help the Kind 2 model checker prove that a property holds in \
       every reachable state of a transition system." ;
      "The system has an initial condition and a transition relation over \
       its state variables. For a variable v, v is its value in the current \
       state and v' its value in the next state." ] ;
    only_if has_inputs [
      "Inputs take an arbitrary value at each step, which a transition reads \
       as v'. They are not part of the state." ] ;
    [ "Kind 2 tries k-induction, which fails when the property is true but \
       not inductive: some unreachable state satisfies the property and yet \
       can step to a state violating it. An invariant that is true of all \
       reachable states and excludes such states makes the proof go \
       through." ;
      "A candidate must hold in all the initial states and be preserved by \
       every transition, possibly with the help of the property and of the \
       other candidates. Reason on what each transition does to the values \
       of the variables." ] ;
    only_if has_locations [
      "With control locations, reason on what holds at each location, \
       typically as (=> L3 ...)." ] ;
    [ "Every candidate is checked by a solver, and one that is false or \
       malformed is simply discarded: do not spend time re-checking the \
       rules or the syntax. As soon as you have candidates that hold \
       initially and are preserved by every transition, give your answer." ;
      "Answer with 1 to 5 distinct candidate invariants, one per line, each \
       a Boolean SMT-LIB term, with no explanation and no numbering. A \
       single strong candidate is enough." ;
      allowed ] ;
    theory_notes sys ;
  ])

let mk in_sys analysis sys prop =
  let r = LlmTransSys.render in_sys analysis prop in
  let system = system_prompt sys r in
  let omitted =
    if r.omitted_count = 0 then ""
    else
      "State variables that cannot affect the goal are not shown.\n\n"
  in
  let user =
    String.concat "" [
      "# Transition system\n\n" ;
      omitted ;
      r.text ;
      "# Goal\n\n" ;
      "Prove that every reachable state satisfies:\n\n" ;
      r.goal_text ;
      "\n\nThis is not inductive on its own.\n\n" ;
      "# Request\n\n" ;
      "Give 1 to 5 distinct candidate invariants that strengthen it, one per \
       line." ;
    ]
  in
  { system ; user ; approx_tokens = approx_tokens system + approx_tokens user ;
    rendered = r }
