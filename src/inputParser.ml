(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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
open Lib

(* ====================== CSV ======================== *)

(* typing errors *)
exception Type_error of Type.t * string

let decimal_of_string s =
  match String.split_on_char '/' s with
  | [s] -> Term.mk_dec (Decimal.of_string s)
  | [s1; s2] ->
    Decimal.(div (of_string s1) (of_string s2)) |> Term.mk_dec
  | _ -> raise (Type_error (Type.mk_real (), s))


  type lustre_type = LustreAst.lustre_type
(* Parse one value *)
let value_of_str ty s =
  try (
    match Type.node_of_type ty with
    | Type.Bool -> (
      match s with
      | "true" -> Term.t_true
      | "false" -> Term.t_false
      | _ -> raise (Type_error (ty, s))
    )
    | Type.Int ->
      Term.mk_num (Numeral.of_string s)
    | Type.Real -> decimal_of_string s
    | Type.IntRange (Some l, Some u) -> (
      let n = Numeral.of_string s in
      if (Numeral.leq l n && Numeral.leq n u) then Term.mk_num n
      else raise (Type_error (ty, s))
    )
    | Type.IntRange (Some l, None) -> (
      let n = Numeral.of_string s in
      if (Numeral.leq l n) then Term.mk_num n
      else raise (Type_error (ty, s))
    )
    | Type.IntRange (None, Some u) -> (
      let n = Numeral.of_string s in
      if (Numeral.leq n u) then Term.mk_num n
      else raise (Type_error (ty, s))
    )
    | Type.IntRange (None, None) -> raise (Type_error (ty, s))
    | Type.Enum (_, _) ->
      if Type.enum_of_constr s == ty then Term.mk_constr s
      else raise (Type_error (ty, s))
    | _ -> raise (Type_error (ty, s))
  )
  with Invalid_argument _ | Not_found ->
    raise (Type_error (ty, s))


(* Parse list of values *)
let values_of_strs ty l =
  List.rev_map (value_of_str ty) l |> List.rev 


let separator = Str.regexp " *, *"

let parse_identifier scope name =
  match String.split_on_char '.' name with
  | [] -> failwith "split_on_char returned an empty list"
  | _ :: fields -> (
    let index =
      fields |> List.map (fun f -> LustreIndex.RecordIndex f)
    in
    let index_scope = LustreIndex.mk_scope_for_index index in
    StateVar.state_var_of_string (name, scope @ index_scope)
  )

(* Parse a line *)
let parse_stream scope chan =
  let line = input_line chan |> String.trim in
  let l = Str.split separator line in
  match l with
  | [] -> raise Not_found
  | name :: stream ->
    try
      let sv = parse_identifier scope name in
      if StateVar.is_input sv then 
        (* Return state variable and its input *)
        (sv, values_of_strs (StateVar.type_of_state_var sv) stream)
      else raise Not_found
    with Not_found ->
      (* Fail *)
      KEvent.log L_fatal "State variable %s is not an input state variable" name;
      raise (Parsing.Parse_error)


let rec parse =
  let line_nb = ref 0 in
  fun scope chan acc ->
    try
      incr line_nb;
      parse scope chan (parse_stream scope chan :: acc)
    with
    | Not_found -> parse scope chan acc
    | End_of_file -> close_in chan; acc
    | Type_error (ty, s) ->
      Log.log L_fatal
        "Typing error in input values file at line %d: \
         expected value of type %a, got value %s"
        !line_nb Type.pp_print_type ty s;
      raise (Parsing.Parse_error)


(* Read in a csv file *)
let read_csv_file top_scope_index filename = 
  let chan = open_in filename in
  parse top_scope_index chan []


(* ====================== JSON ======================== *)

open Yojson.Safe.Util

type assignment_lhs = StateVar.t * (Term.t * index_type) list
and index_type = | ArrayIndex | SetMapPresenceIndex | SetMapBindingIndex
module LHS =
struct
  type t = assignment_lhs
  let compare (a,b) (a',b') =
    let compare_ele (term, _) (term', _) = Term.compare term term' in
    match StateVar.compare_state_vars a a' with
    | 0 -> List.compare compare_ele b b'
    | i -> i
end
module LHSMap = Map.Make(LHS)

exception Missing_definition of int * assignment_lhs

(* Transforms a list of list of variable assignments
  (the outer list representing the steps and the inner the different variables)
  into a list associating to each variable the list of all its successive assignments *)
let group_by_var lst =
  let steps_passed = ref 0 in
  List.fold_right
    (fun lst acc -> 
      List.fold_left (fun acc (var, term) ->
          let old = try LHSMap.find var acc with Not_found -> [] in
          let n = List.length old in
          if n < !steps_passed then raise (Missing_definition(n, var)) ;
          steps_passed := n ;
          LHSMap.add var (term::old) acc
        )
        acc lst
    ) lst LHSMap.empty
  |> LHSMap.bindings

exception Not_an_input of string
exception Type_mismatch of string



let print_got fmt = function
    | `Bool b -> Format.fprintf fmt "%b" b
    | `String s -> Format.fprintf fmt "'%s'" s
    | `Float f -> Format.fprintf fmt "%f" f
    | `Int i -> Format.fprintf fmt "%d" i
    | `Intlit s -> Format.fprintf fmt "%s" s
    | _ -> Format.fprintf fmt "complex JSON value"

let pp_print_lus_type_mismatch fmt (name, expected, got) =
 
  Format.fprintf fmt "Type mismatch for variable %s: expected %a, got %a"
    name LustreAst.pp_print_lustre_type expected print_got got

type sv_info = (
  (string) *
  (string list) *
  (bool)
)
let get_svar (svar_info: sv_info) =
let full_name,full_scope,only_inputs = svar_info in
  let sv =
      try (StateVar.state_var_of_string (full_name, full_scope))
      with Not_found -> raise (Not_an_input ("State variable not found: " ^ full_name)) in
    if (not (StateVar.is_input sv)) && only_inputs then raise (Not_an_input full_name) ;
    sv
(* Take as input a JSON element representing the value of a variable (at a given step)
   and return the associated assignments.
   It can return multiple variable assignements if the value is an array/record/tuple. *)
    
let rec read_term ?(only_inputs = true) scope name indexes (arr_indexes : (Term.t * index_type) list) json expected_type : ((sv_info * (Term.t * index_type) list) * Term.t) list=
  (* Format.printf "read_term: %a" pp_print_call_context (scope, name, indexes, arr_indexes, json, expected_type) ; *)
  match json, expected_type with
  | `Assoc lst, LustreAst.RecordType (_,_,types)->
    let seen = ref [] in
     lst |>
      List.map (
        fun (str, json) ->
        if List.exists (fun s -> s = str) !seen then raise (Not_an_input ("Duplicate field in record " ^ name)) ;
          seen := str :: !seen ;
        let lookup_ident id = 
          let rec lookup_ident' id rest = match rest with 
          |[] -> failwith "Identifier not found" 
          | (_, tid, ty) :: _ when id = tid -> ty 
          | _ :: rest -> lookup_ident' id rest
        in
        lookup_ident' id types
        in
        read_term scope name ((LustreIndex.RecordIndex str)::indexes) arr_indexes json (lookup_ident (HString.mk_hstring str))
      )
      |> List.flatten
  | `List lst, LustreAst.ArrayType (_, (ty,expr)) ->
    (* Can represent an array *)
      (match expr with
      |Const (_,(Num v)) -> 
        if HString.equal ((List.length lst) |> Int.to_string |> HString.mk_hstring) v |> not then raise (Not_an_input ("Array " ^ name ^ " has incorrect length"))
      | _ -> ());
      lst |>
      List.mapi (
      fun i json ->
      let new_index = LustreIndex.ArrayVarIndex (LustreExpr.mk_int_expr Numeral.one) in
      let arr_index = (Term.mk_num (Numeral.of_int i)) in
      read_term scope name (new_index::indexes) ((arr_index, ArrayIndex)::arr_indexes) json ty
    )
    |> List.flatten
  | `List lst, LustreAst.TupleType (_, types) ->
    (* Can represent a tuple *)
      (try (List.combine types lst) |> List.mapi (
            fun i (ty, json) ->
            read_term scope name ((LustreIndex.TupleIndex i)::indexes) arr_indexes  json ty
          )
          |> List.flatten 
      with Invalid_argument _ -> raise (Not_an_input ("Tuple " ^ name ^ " has incorrect length")))
  | `List lst, LustreAst.Map (_, key_type, value_type) ->
    (* Can represent a map *)
      let ((new_arr_indexes, presence_elements, binding_elements)) = 
        List.fold_left 
        (fun (presence_i, presence_elements, binding_elements) y -> 
          match y with 
          | `List [key;value] -> 
            let term = match (read_term scope name [] [] key key_type ) with
              | [(_, term)] -> term
              | _ -> raise (Not_an_input ("Tried to parse as map " ^ name))
            in
            if List.exists (fun t -> Term.equal t term) presence_i then raise (Not_an_input ("Multiple occurrences of key in map " ^ name)) ;

            ((term ::presence_i, (`Bool true)::presence_elements, value::binding_elements))
          | _ -> raise (Not_an_input ("Tried to parse as map " ^ name))

        ) ([], [],[]) lst  in
      let bindings_indexes = List.map (fun i -> (i, SetMapBindingIndex)) new_arr_indexes in
      let bindings = 
          (List.map2 (
          fun index json ->
          let new_index = LustreIndex.TupleIndex 1 in
          read_term scope name (new_index::indexes) (index::arr_indexes) json value_type
        ) bindings_indexes binding_elements) |> List.flatten in
      
      let presence_indexes = List.map (fun i -> (i, SetMapPresenceIndex)) new_arr_indexes in
      let presences = 
            (List.map2 (
            fun index json ->
            let new_index = LustreIndex.TupleIndex 0 in
            read_term scope name (new_index::indexes) (index::arr_indexes) json (LustreAst.Bool Lib.dummy_pos)
          ) presence_indexes presence_elements) |> List.flatten in
      
      presences @ bindings
  | `List lst, LustreAst.Set (_, ty) ->
    (* Can represent a set *)
    let ((new_arr_indexes, presence_elements)) = 
      List.fold_left 
      (fun (presence_i, presence_elements) y -> 
          let term = match (read_term scope name indexes arr_indexes y ty ) with
            | [(_, term)] -> term
            | _ -> raise (Not_an_input ("Container types as keys is not yet implemented " ^ name))
          in
          if List.exists (fun (t, _) -> Term.equal t term) presence_i then raise (Not_an_input ("Duplicate element in set " ^ name)) ;
          (((term, SetMapPresenceIndex) ::presence_i, (`Bool true)::presence_elements))
      ) ([], []) lst  in
    let presences = 
          (List.map2 (
          fun index json ->
          read_term scope name (indexes) (index::arr_indexes) json (LustreAst.Bool Lib.dummy_pos)
        ) new_arr_indexes presence_elements) |> List.flatten in
      (* Format.printf "Presences: %a@." (Lib.pp_print_list (fun fmt ((sv, tlist), t) -> Format.fprintf fmt "SV:%a  Indexes: %a Term: %a" StateVar.pp_print_state_var sv (Lib.pp_print_list Term.pp_print_term ",") tlist  Term.pp_print_term t) ",@.") presences; *)
    presences
  | (`Bool _  as json),  (Bool _ as lus_typ)
  | (`String _ as json), (Int _ as lus_typ)
  | (`String _ as json), (Real _ as lus_typ)
  | (`String _ as json), (EnumType _ as lus_typ)
  | (`Float _ as json),  (Real _ as lus_typ)
  | (`Int _ as json),    (Int _ as lus_typ)
  | (`Intlit _ as json), (Int _ as lus_typ)
  | json,                (LustreAst.RefinementType (_,_,_) as lus_typ) -> (
    let indexes = List.rev indexes in
    let arr_indexes = List.rev arr_indexes in
    let full_scope = scope @ (LustreIndex.mk_scope_for_index indexes) in
    let indexes = List.filter
        (function 
          | LustreIndex.ArrayVarIndex _ 
          | LustreIndex.ArrayIntIndex _ 
          | LustreIndex.SetMapIndex _ -> false
          | LustreIndex.RecordIndex _
          | LustreIndex.TupleIndex _
          | LustreIndex.ListIndex _
          | LustreIndex.AbstractTypeIndex _ -> true) indexes in
    let full_name =
      Format.asprintf "%s%a" name (LustreIndex.pp_print_index true) indexes
    in

    let svar_info : sv_info = (full_name, full_scope, only_inputs) in
    let name_indexes = (svar_info, arr_indexes) in
    (* Extract the type of an element of an array (and check the ranges) *)
    try (
      match lus_typ, json with

      | EnumType _, `String str ->
        [name_indexes, Term.mk_constr str]
      | Bool _ , `Bool b -> [name_indexes, Term.mk_bool b]
      | Real _, `Float f -> [name_indexes, string_of_float f |> Decimal.of_string |> Term.mk_dec]
      | Real _, `Int i -> [name_indexes, Decimal.of_int i |> Term.mk_dec]
      | Real _, `String str -> [name_indexes, decimal_of_string str]
      | Real _, `Intlit str -> [name_indexes, Decimal.of_string str |> Term.mk_dec]
      | _, `Int i -> [name_indexes, Term.mk_num_of_int i]

      | _, `Intlit str 
      | _, `String str  ->
        [name_indexes, Numeral.of_string str |> Term.mk_num]

      | _ -> raise (Type_mismatch ("Reading leaf " ^ full_name))
      )
    with | Invalid_argument _ -> raise (Type_mismatch (Format.asprintf "Invalid arg %a" pp_print_lus_type_mismatch (full_name, lus_typ, json)))
         | Not_found ->          raise (Type_mismatch (Format.asprintf "not found %a"   pp_print_lus_type_mismatch (full_name, lus_typ, json))))
    (* Error match cases *)
  | json, lus_typ ->
    (* The JSON value is not of the expected type *)
    raise (Type_mismatch (Format.asprintf "%a" pp_print_lus_type_mismatch (name, lus_typ, json)))

  (*  

      (* Is a numeral in the range of a type? *)
    let is_in_range n t =
      match Type.node_of_type t with
      | Int -> true
      | IntRange (Some l, Some u) ->
        Numeral.leq l n && Numeral.leq n u
      | IntRange (Some l, None) ->
        Numeral.leq l n
      | IntRange (None, Some u) ->
        Numeral.leq n u
      | _ -> false
    in
    (* Is an integer in the range of a type? *)
    let is_in_range_i i = is_in_range (Numeral.of_int i) in

    let sv = get_svar (full_name, full_scope, only_inputs, arr_indexes) in
    let typ = StateVar.type_of_state_var sv in
    let sv = (sv, arr_indexes) in

    (* Extract the type of an element of an array (and check the ranges) *)
    let rec extract_element_type arr_indexes typ =
      match arr_indexes, Type.node_of_type typ with
      | [], _ -> typ
      | _::arr_indexes, Array (elt, _) (*when is_in_range_i i t*)  ->
        extract_element_type arr_indexes elt
      | _, _ -> raise (Type_mismatch ("Extract_element_type:" ^ full_name))
    in
    let typ = extract_element_type arr_indexes typ in
    let ktype = Type.node_of_type typ in
    try (
      let open Type in
      match ktype, json with

      | Enum _, `String str when equal_types (enum_of_constr str) typ ->
        [sv, Term.mk_constr str]
      | Bool, `Bool b -> [sv, Term.mk_bool b]
      | Real, `Float f -> [sv, string_of_float f |> Decimal.of_string |> Term.mk_dec]
      | Real, `Int i -> [sv, Decimal.of_int i |> Term.mk_dec]
      | Real, `String str -> [sv, decimal_of_string str]
      | Real, `Intlit str -> [sv, Decimal.of_string str |> Term.mk_dec]
      | _, `Int i when is_in_range_i i typ -> [sv, Term.mk_num_of_int i]

      | _, `Intlit str 
      | _, `String str when is_in_range (Numeral.of_string str) typ ->
        [sv, Numeral.of_string str |> Term.mk_num]

      | _ -> raise (Type_mismatch ("Reading leaf " ^ full_name))
      )
    with Invalid_argument _ -> raise (Type_mismatch (Format.asprintf "%a" pp_print_type_mismatch (full_name, typ, json))))
    
    (* Error match cases *)
    | json, lus_typ ->
      (* The JSON value is not of the expected type *)
      raise (Type_mismatch (Format.asprintf "%a" pp_print_lus_type_mismatch (name, lus_typ, json)))
*)

let read_val ?(only_inputs = true) scope name indexes (arr_indexes : (Term.t*index_type) list) json sv_name_type_map =
    let expected_type : lustre_type = sv_name_type_map |> HString.HStringMap.find (HString.mk_hstring name)
  in
  read_term ~only_inputs:only_inputs scope name indexes arr_indexes json expected_type |> 
    List.map (fun ((svar_info, arr_indexes), term) -> 
      (* Need to also implement the state-var-level checks that are commented above 
      Need reftype bounds checks (This was not implemented before)
      Need enum checks (this should already be implemented at lustre type level) *)
      let sv = get_svar svar_info in
      (* Format.printf "Making sv %a with arr_indexes [%a]. Value %a@." 
        StateVar.pp_print_state_var sv 
        (Lib.pp_print_list (fun fmt (arr_idx, _) -> Format.fprintf fmt "%a" Term.pp_print_term arr_idx) ", ") arr_indexes
        Term.pp_print_term term; *)
      ((sv, arr_indexes), term)
    )  
(* Parse the assignments of a JSON object representing a step *)
let read_vars ?(only_inputs=true) scope sv_name_type_map json  =
  to_assoc json |> List.map (fun (name, json) -> read_val ~only_inputs:only_inputs scope name [] [] json sv_name_type_map)




  let rec get_string_reps_sets_maps' ?(only_inputs = true) scope name indexes (arr_indexes : (Term.t * index_type) list) (json: Yojson.Safe.t)  expected_type  : string =
  (* Format.printf "Parsing %a with expected type %a@." (Yojson.Safe.pretty_print ~std:true) json LustreAst.pp_print_lustre_type expected_type ; *)
  match json, expected_type with
  | `Assoc lst, LustreAst.RecordType (_,_,types)->
     let vals = lst |>
      List.map (
        fun (str, json) ->
        let lookup_ident id = 
          let rec lookup_ident' id rest = match rest with 
          |[] -> failwith "Identifier not found" 
          | (_, tid, ty) :: _ when id = tid -> ty 
          | _ :: rest -> lookup_ident' id rest
        in
        lookup_ident' id types
        in
        Format.asprintf "\"%s\" : \"%s\"" str (get_string_reps_sets_maps' scope name indexes arr_indexes json (lookup_ident (HString.mk_hstring str)))
      ) in
      Format.asprintf "{%a}" (Lib.pp_print_list Format.pp_print_string ", ") vals
  | `List lst, LustreAst.ArrayType (_, (ty,expr)) ->
    (* Can represent an array *)
      (match expr with
      |Const (_,(Num v)) -> 
        if HString.equal ((List.length lst) |> Int.to_string |> HString.mk_hstring) v |> not then raise (Not_an_input ("Array " ^ name ^ " has incorrect length"))
      | _ -> ());
      let vals = lst |>
        List.mapi (
        fun i json ->
        let new_index = LustreIndex.ArrayVarIndex (LustreExpr.mk_int_expr Numeral.one) in
        let arr_index = (Term.mk_num (Numeral.of_int i)) in
        get_string_reps_sets_maps' scope name (new_index::indexes) ((arr_index, ArrayIndex)::arr_indexes) json ty
        )
      in
      Format.asprintf "[%a]" (Lib.pp_print_list Format.pp_print_string ", ") vals
  | `List lst, LustreAst.TupleType (_, types) ->
    (* Can represent a tuple *)
      let vals = (try (List.combine types lst) |> List.mapi (
            fun i (ty, json) ->
            get_string_reps_sets_maps' scope name ((LustreIndex.TupleIndex i)::indexes) arr_indexes  json ty
          ) 
      with Invalid_argument _ -> raise (Not_an_input ("Tuple " ^ name ^ " has incorrect length"))) in
      Format.asprintf "(%a)" (Lib.pp_print_list Format.pp_print_string ", ") vals
  | `List lst, LustreAst.Map (_, key_type, value_type) ->
    (* Can represent a map *)
      let (keys, values) = 
        List.fold_left 
        (fun (keys, values) y -> 
          match y with 
          | `List [key;value] -> 
            let new_key =  (get_string_reps_sets_maps' scope name [] [] key key_type ) in
            let new_value = get_string_reps_sets_maps' scope name (indexes) (arr_indexes) value value_type in
            ((new_key :: keys , new_value :: values))
          | _ -> raise (Not_an_input ("Tried to parse as map " ^ name))

        ) ([], []) lst  in
      

      
      
      Format.asprintf "[%t]" (fun ppf -> (Lib.pp_print_list2i (fun ppf i k v -> Format.fprintf ppf "%s := %s" k v) "; " ppf keys values))
  | `List lst, LustreAst.Set (_, ty) ->
    (* Can represent a set *)
    let elements = 
      List.fold_left 
      (fun (elements) y -> 
          let element =  (get_string_reps_sets_maps' scope name indexes arr_indexes y ty ) in
          (element :: elements)
      ) ([]) lst  in
      Format.asprintf "{%a}" (Lib.pp_print_list Format.pp_print_string ", ") elements
  | (`Bool _  as json),  (Bool _ as lus_typ)
  | (`String _ as json), (Int _ as lus_typ)
  | (`String _ as json), (Real _ as lus_typ)
  | (`String _ as json), (EnumType _ as lus_typ)
  | (`Float _ as json),  (Real _ as lus_typ)
  | (`Int _ as json),    (Int _ as lus_typ)
  | (`Intlit _ as json), (Int _ as lus_typ)
  | json,                (LustreAst.RefinementType (_,_,_) as lus_typ) -> (
    let indexes = List.rev indexes in
    let arr_indexes = List.rev arr_indexes in
    let full_scope = scope @ (LustreIndex.mk_scope_for_index indexes) in
    let indexes = List.filter
        (function 
          | LustreIndex.ArrayVarIndex _ 
          | LustreIndex.ArrayIntIndex _ 
          | LustreIndex.SetMapIndex _ -> false
          | LustreIndex.RecordIndex _
          | LustreIndex.TupleIndex _
          | LustreIndex.ListIndex _
          | LustreIndex.AbstractTypeIndex _ -> true) indexes in
    let full_name =
      Format.asprintf "%s%a" name (LustreIndex.pp_print_index true) indexes
    in

    let svar_info : sv_info = (full_name, full_scope, only_inputs) in
    let name_indexes = (svar_info, arr_indexes) in
    (* Extract the type of an element of an array (and check the ranges) *)
    try (
      match lus_typ, json with

      | EnumType _, `String str ->
        str
      | Bool _ , `Bool b -> if b then "true" else "false"
      | Real _, `Float f -> string_of_float f
      | Real _, `Int i -> string_of_int i 
      | Real _, `String str -> str
      | Real _, `Intlit str -> str
      | _, `Int i -> string_of_int i

      | _, `Intlit str 
      | _, `String str  ->
        str

      | _ -> raise (Type_mismatch ("Reading leaf " ^ full_name))
      )
    with | Invalid_argument _ -> raise (Type_mismatch (Format.asprintf "Invalid arg %a" pp_print_lus_type_mismatch (full_name, lus_typ, json)))
         | Not_found ->          raise (Type_mismatch (Format.asprintf "not found %a"   pp_print_lus_type_mismatch (full_name, lus_typ, json))))
    (* Error match cases *)
  | json, lus_typ ->
    (* The JSON value is not of the expected type *)
    raise (Type_mismatch (Format.asprintf "%a" pp_print_lus_type_mismatch (name, lus_typ, json)))

  

  let get_str_values_of_vars ?(only_inputs=true) top_scope_index sv_name_type_map json = 
    json
    |> to_assoc
    |> List.fold_left
        (fun acc (name, json) ->
            let expected_type : lustre_type =
              sv_name_type_map
              |> HString.HStringMap.find (HString.mk_hstring name)
            in
            let value =
              get_string_reps_sets_maps' ~only_inputs top_scope_index name [] [] json expected_type
            in
            HString.HStringMap.add ( HString.mk_hstring name) value acc)
        HString.HStringMap.empty


    (* Parse a JSON input file *)
let read_json_file ?(only_inputs=true) top_scope_index filename sv_name_type_map =
  let json =
    try Yojson.Safe.from_file filename with
    | Yojson.Json_error msg ->
        failwith
          (Format.asprintf
             "Error reading %s: the file is not valid JSON.\n\n%s"
             filename msg)
  in
  let json_list = json |> to_list in
  (* Format.printf "%a" (Lib.pp_print_list Yojson.Safe.pretty_print "@.@.@.") json_list; *)
  (
  json_list |> List.map (read_vars ~only_inputs:only_inputs top_scope_index sv_name_type_map) |> List.flatten |> group_by_var,
  json_list
  |> List.map (get_str_values_of_vars ~only_inputs:only_inputs top_scope_index sv_name_type_map))

(* ====================== GENERAL ======================== *)

(* Parse a JSON or CSV input file. The format is determined from the extension. *)
let read_file ?(only_inputs=true) top_scope_index filename sv_name_type_map =
  if Filename.check_suffix filename ".json"
  then
    read_json_file ~only_inputs:only_inputs top_scope_index filename sv_name_type_map
  else
    (read_csv_file top_scope_index filename
    |> List.map (fun (sv,vs) -> ((sv,[]),vs)), [])

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
