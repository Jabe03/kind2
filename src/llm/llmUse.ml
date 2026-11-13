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

type proof = {
  prop : string ;
  terms : Term.t list ;
}

let lock = Mutex.create ()
let proofs = ref []

let reset () =
  Mutex.protect lock (fun () -> proofs := [])

let record_proved ~prop ~terms =
  if terms <> [] then
    Mutex.protect lock (fun () -> proofs := { prop ; terms } :: !proofs)

let pp_terms terms =
  terms
  |> List.map (Format.asprintf "%a" Term.pp_print_term)
  |> String.concat ", "

let report_one sys { prop ; terms } =
  let terms = List.map Term.import terms in
  let property = TransSys.property_of_name sys prop in
  let prop_term = property.Property.prop_term in
  let k, useful =
    CertifChecker.minimize_invariants sys (Some [prop_term]) None
  in
  let llm_useful =
    List.filter
      (fun candidate -> List.exists (Term.equal candidate) useful)
      terms
  in
  if llm_useful = [] then
    KEvent.log L_note
      "LLMINV usefulness for %s: no LLM candidate was needed in the minimized proof (k=%d)"
      prop k
  else
    KEvent.log L_note
      "LLMINV usefulness for %s: %d/%d LLM candidate(s) are in the minimized proof (k=%d): %s"
      prop (List.length llm_useful) (List.length terms) k (pp_terms llm_useful)

let report sys =
  if Flags.Llm.usefulness () then (
    let proofs = Mutex.protect lock (fun () -> List.rev !proofs) in
    if not (Flags.Smt.check_sat_assume ()) then
      KEvent.log L_warn
        "LLMINV usefulness is inconclusive: --smt_check_sat_assume is disabled"
    else
      List.iter (fun proof ->
        try report_one sys proof with
        | CertifChecker.CouldNotProve message ->
          KEvent.log L_warn "LLMINV usefulness for %s is inconclusive: %t"
            proof.prop message
        | error ->
          KEvent.log L_warn "LLMINV usefulness for %s is inconclusive: %s"
            proof.prop (Printexc.to_string error)
      ) proofs
  )