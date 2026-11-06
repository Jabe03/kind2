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

module D = GenericSMTLIBDriver

type result = {
  terms : Term.t list ;
  rejected : (string * string) list ;
}

let starts_with prefix text =
  String.length text >= String.length prefix
  && String.sub text 0 (String.length prefix) = prefix

let clean_line line =
  let line = String.trim line in
  let line =
    let length = String.length line in
    let rec digits i =
      if i < length && line.[i] >= '0' && line.[i] <= '9'
      then digits (i + 1) else i
    in
    let n = digits 0 in
    if n > 0 && n < length && (line.[n] = '.' || line.[n] = ')') then
      String.sub line (n + 1) (length - n - 1) |> String.trim
    else if starts_with "- " line || starts_with "* " line then
      String.sub line 2 (length - 2) |> String.trim
    else line
  in
  if String.length line >= 2 && line.[0] = '`' && line.[String.length line - 1] = '`'
  then String.sub line 1 (String.length line - 2) |> String.trim
  else line

let balance text =
  let depth = ref 0 and quoted = ref false and in_string = ref false in
  let rec scan i =
    if i < String.length text then
      match text.[i] with
      | '"' when not !quoted ->
        if !in_string && i + 1 < String.length text && text.[i + 1] = '"' then
          scan (i + 2)
        else (in_string := not !in_string ; scan (i + 1))
      | '|' when not !in_string -> quoted := not !quoted ; scan (i + 1)
      | '(' when not !quoted && not !in_string -> incr depth ; scan (i + 1)
      | ')' when not !quoted && not !in_string -> decr depth ; scan (i + 1)
      | _ -> scan (i + 1)
  in
  scan 0 ;
  !depth

let fragments text =
  let lines =
    String.split_on_char '\n' text
    |> List.filter (fun line -> not (starts_with "```" (String.trim line)))
    |> List.map clean_line
    |> List.filter (fun line -> line <> "")
  in
  let rec collect acc pending depth = function
    | [] -> List.rev (if pending = "" then acc else pending :: acc)
    | line :: rest ->
      let joined = if pending = "" then line else pending ^ " " ^ line in
      let depth = depth + balance line in
      if depth > 0 then collect acc joined depth rest
      else collect (joined :: acc) "" 0 rest
  in
  collect [] "" 0 lines

let parse_sexp text =
  match SExprParser.sexps SExprLexer.main (Lexing.from_string text) with
  | [ sexp ] -> sexp
  | [] -> failwith "empty candidate"
  | _ -> failwith "more than one term on a line"

let term_of_sexp rendered sys sexp =
  let names = Hashtbl.create (List.length rendered.LlmTransSys.symbols) in
  List.iter (fun (name, term) ->
    let prior = Option.value ~default:[] (Hashtbl.find_opt names name) in
    Hashtbl.replace names name (term :: prior)) rendered.symbols ;
  let const_of_atom bound atom =
    let name = Lib.unquote_smtlib_symbol (HString.string_of_hstring atom) in
    match Hashtbl.find_opt names name with
    | Some [ term ] -> term
    | Some _ -> failwith ("ambiguous symbol: " ^ name)
    | None ->
      D.smtlib_string_sexpr_conv.const_of_atom bound atom
  in
  let base = D.smtlib_string_sexpr_conv in
  let conv = { base with const_of_atom } in
  let term = D.gen_expr_of_string_sexpr conv sexp in
  if Term.has_quantifier term then failwith "quantifiers are not allowed" ;
  if not (Type.is_bool (Term.type_of_term term)) then
    failwith "candidate is not Boolean" ;
  let allowed =
    List.fold_left (fun set (_, symbol) ->
      Var.VarSet.union set (Term.vars_of_term symbol)) Var.VarSet.empty
      rendered.symbols
  in
  let system_vars = TransSys.state_vars sys in
  Var.VarSet.iter (fun variable ->
    if Var.is_const_state_var variable then (
      let sv = Var.state_var_of_state_var_instance variable in
      if not (List.exists (StateVar.equal_state_vars sv) system_vars) then
        failwith "a constant from another system" ;
      if not (Var.VarSet.exists (fun allowed_var ->
        StateVar.equal_state_vars
          (Var.state_var_of_state_var_instance allowed_var) sv) allowed)
      then failwith "a variable not shown to the model"
    ) else if Var.is_state_var_instance variable then (
      let sv = Var.state_var_of_state_var_instance variable in
      if not (List.exists (StateVar.equal_state_vars sv) system_vars) then
        failwith "a variable from another system" ;
      if StateVar.is_input sv then
        failwith ("an input: " ^ StateVar.name_of_state_var sv) ;
      if not (Numeral.equal (Var.offset_of_state_var_instance variable)
                Numeral.zero) then failwith "a non-current state value" ;
      if not (Var.VarSet.exists (fun allowed_var ->
        StateVar.equal_state_vars
          (Var.state_var_of_state_var_instance allowed_var) sv) allowed)
      then failwith "a variable not shown to the model"
    ) else failwith "a variable that is not a state variable")
    (Term.vars_of_term term) ;
  term

let parse rendered sys text =
  let terms, rejected =
    List.fold_left (fun (terms, rejected) text ->
      try
        let term = parse_sexp text |> term_of_sexp rendered sys in
        if List.exists (Term.equal term) terms then terms, rejected
        else term :: terms, rejected
      with
      | Failure reason | Invalid_argument reason ->
        terms, (text, reason) :: rejected
      | Not_found -> terms, (text, "unknown symbol") :: rejected
      | error -> terms, (text, Printexc.to_string error) :: rejected
    ) ([], []) (fragments text)
  in
  { terms = List.rev terms ; rejected = List.rev rejected }