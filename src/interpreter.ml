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

(*./kind2 --enable interpreter --debug smt --debug parse microwave.lus*)
open Lib


(* Solver instance if created *)
let ref_solver = ref None


(* Exit and terminate all processes here in case we are interrupted *)
let on_exit _ = 

  (* Delete solver instance if created *)
  (try 
     match !ref_solver with 
       | Some solver -> 
         SMTSolver.delete_instance solver;  
         ref_solver := None
       | None -> ()
   with 
     | e -> 
       KEvent.log L_error
         "Error deleting solver_init: %s" 
         (Printexc.to_string e))


(* Assert transition relation for all steps below [i] *)
let rec assert_trans solver t i =
  
  (* Instant zero is base instant *)
  if Numeral.(i < one) then () else  
    
    (

      (* Assert transition relation from [i-1] to [i] *)
      SMTSolver.assert_term solver
        (TransSys.trans_of_bound (Some (SMTSolver.declare_fun solver)) t i);
                            
      (* Continue with for [i-2] and [i-1] *)
      assert_trans solver t Numeral.(i - one)

    )
    

(* Main entry point *)
let main ?(contract_monitor=false) input_file input_sys _ trans_sys =

  KEvent.set_module `Interpreter;

  let input_scope = TransSys.scope_of_trans_sys trans_sys @
                    LustreIdent.user_scope in

  let trans_svars = TransSys.state_vars trans_sys in
  (*trans_svars |> List.iter (fun sv -> KEvent.log_uncond "%a : %a" StateVar.pp_print_state_var sv Type.pp_print_type (StateVar.type_of_state_var sv)) ; *)

  let vars_types = input_sys |> InputSystem.types_of_vars in
  (* List.iter (fun (id, ty) -> KEvent.log_uncond "Variable %a has type %a@." HString.pp_print_hstring id LustreAst.pp_print_lustre_type ty) vars; *)
  (* HString.HStringMap.iter (fun id ty -> KEvent.log_uncond "Variable %a has type %a@." HString.pp_print_hstring id LustreAst.pp_print_lustre_type ty) vars_types; *)
  (* Read inputs from file *)
  let (inputs, (inputs_str: string HString.HStringMap.t list)) =
    if input_file = "" then ([], [])
    else
      try InputParser.read_file  ~only_inputs:(not contract_monitor) input_scope input_file vars_types
      with Sys_error e -> 
        (* Output warning *)
        KEvent.log L_warn "@[<v>Error reading interpreter input file.@,%s@]" e;
        raise (Failure "main")
  in

  Format.printf "DEBUG: Inputs read as strings: @.%a@." (Lib.pp_print_list (fun ppf map -> (
    Format.fprintf ppf "[@.%a@.]" (Lib.pp_print_list (fun ppf (key, value) -> Format.fprintf ppf "%a     %s" HString.pp_print_hstring key value) "@.") (HString.HStringMap.bindings map)
  )) "@.") inputs_str;

  let nb_inputs = List.filter StateVar.is_input trans_svars |> List.length in

  (* Check that constant inputs are indeed constant. *)
  inputs |> List.iter (
    function
    | ((sv, _), (head :: tail)) when StateVar.is_const sv ->
      tail |> List.fold_left (
        fun acc value ->
          if acc != value then (
            KEvent.log L_warn
              "Input %s is constant, but input values differ: \
              got %a and, later, %a."
              (StateVar.name_of_state_var sv)
              Term.pp_print_term acc
              Term.pp_print_term value ;
            Failure "main" |> raise
          ) ;
          acc
      ) head |> ignore
    | _ -> ()
  ) ;

  (* Remove sliced inputs *)
  let inputs = List.filter (fun ((sv,_), _) ->
      List.exists (StateVar.equal_state_vars sv) trans_svars
    ) inputs
  in

  (* Minimum number of steps in input *)
  let input_length = 
    List.fold_left 
      (fun accum (_, inputs) -> 
         min (if accum = 0 then max_int else accum) (List.length inputs))
      0
      inputs
  in

  (* Check if all inputs are of the same length *)
  List.iter
    (fun ((state_var, _), inputs) -> 

       (* Is input longer than minimum? *)
       if List.length inputs > input_length then

         (* Output warning *)
         KEvent.log L_warn 
           "Input for %s is longer than other inputs"
           (StateVar.name_of_state_var state_var))

    inputs;

  (* Number of steps to simulate *)
  let steps = 
    
    match (if contract_monitor then Flags.ContractMonitor.steps else Flags.Interpreter.steps) () with 

    (* Simulate length of smallest input if number of steps not given *)
    | s when s <= 0 -> input_length

    (* Length of simulation given by user *)
    | s -> 

      (* Lenghth of simulation greater than input? *)
      if s > input_length && nb_inputs > 0 then

        KEvent.log L_warn 
          "Input is not long enough to simulate %d steps. \
           Simulation is nondeterministic." 
          input_length;

      (* Simulate for given length *)
      s

  in

  KEvent.log L_info "Interpreter running up to k=%d" steps;

  (* Determine logic for the SMT solver *)
  let logic = TransSys.get_logic trans_sys in

  (* Create solver instance *)
  let solver = 
    Flags.Smt.solver ()
    |> SMTSolver.create_instance ~produce_models:true logic
  in

  (* Create a reference for the solver. Only used in on_exit. *)
  ref_solver := Some solver;

  (* Defining uf's and declaring variables. *)
  TransSys.define_and_declare_of_bounds
    trans_sys
    (SMTSolver.define_fun solver)
    (SMTSolver.declare_fun solver)
    (SMTSolver.declare_sort solver)
    Numeral.(~- one) Numeral.(of_int steps) ;

  TransSys.assert_global_constraints trans_sys (SMTSolver.assert_term solver) ;

  (* Assert initial state constraint *)
    SMTSolver.assert_term solver
      (TransSys.init_of_bound (Some (SMTSolver.declare_fun solver))
         trans_sys Numeral.zero);

  (* Assert transition relation up to number of steps *)
  assert_trans solver trans_sys (Numeral.of_int steps);
  let module IntMap = Map.Make(Int) in
  let defined_indexes : (((Term.t list list) StateVar.StateVarMap.t) IntMap.t )ref = ref IntMap.empty in
  let add_defined_index instant state_var indexes = 
      let instant_map = try IntMap.find instant !defined_indexes with Not_found -> StateVar.StateVarMap.empty in
      let old_idxs = try StateVar.StateVarMap.find state_var instant_map with Not_found -> [] in
      let new_idxs = StateVar.StateVarMap.add state_var (indexes :: old_idxs) instant_map in
      defined_indexes := IntMap.add instant new_idxs !defined_indexes
  in
  (* Assert equation of state variable and its value at each
     instant *)
  List.iter

    (fun ((state_var, indexes), values) ->

       List.iteri 
         (fun instant instant_value ->

            (* Only assert up to the maximum number of steps *)
            if instant < steps then
            (
              (* Create variable at instant *)
              let var = 
                Var.mk_state_var_instance 
                  state_var 
                  (Numeral.of_int instant)
                |> Term.mk_var
              in

              (* Select index of instance variable *)
              (* Constrain variable to its value at instant *)
              let idxs_seen = ref [] in
              let var = List.fold_left (
                fun acc (i, idx_ty) ->
                   if idx_ty = InputParser.SetMapPresenceIndex then idxs_seen := i :: !idxs_seen; 
                Term.mk_select acc (i)
                (* Records tuern into multidimensional array, where each index is a field
                    { x: int; y: real} -->
                      [
                      (x_index): [1,2,3,4](map/set values),
                      (y_index): [2.2, 3.4.5.5]
                      ]
                *)
              ) var indexes |> Term.convert_select in
              if !idxs_seen != [] then add_defined_index instant state_var !idxs_seen;
              (* Constrain variable to its value at instant *)
              let equation = 
                Term.mk_eq [var; instant_value] 
              in
              
              (* Assert equation *)
              SMTSolver.assert_term solver equation
            )
          )
         values)

    inputs;

  (* Assert set and map presence *)
  IntMap.iter (fun instant (state_var_map: Term.t list list StateVar.StateVarMap.t) ->
    StateVar.StateVarMap.iter (fun state_var (indexes : Term.t list list) -> (
      (* Format.printf  "Making forall for: %a: %a@." StateVar.pp_print_state_var state_var
          (Lib.pp_print_list (
            fun ppf i -> Format.fprintf ppf "%a" Term.pp_print_term i
          ) ", ") indexes ; *)
      let idx_vars = match indexes with 
        | idx :: _ -> List.map (fun _ -> Var.mk_fresh_var (Type.mk_int ())) idx 
        | _ -> assert false 
      in
      let mk_forall tm = Term.mk_forall idx_vars tm in
      
      let var = Var.mk_state_var_instance 
                  state_var 
                  (Numeral.of_int instant)
                |> Term.mk_var
      in
      let var = List.fold_left (
        fun acc idx_var ->
        Term.mk_select acc (Term.mk_var idx_var)
      ) var idx_vars |> Term.convert_select in
                
        (* Format.printf "Var created: %a@." Term.pp_print_term var; *)
        let equation = 
          Term.mk_eq [var; Term.mk_false ()] 
        in
        let mk_index_equalities idx_vars indexes = 
          (* Format.printf "Making index inequalities for [%a] and [%a]" (Lib.pp_print_list Var.pp_print_var ", ") idx_vars (Lib.pp_print_list Term.pp_print_term ", ") indexes; *)
          List.map2 (fun idx_var index -> Term.mk_eq [(Term.mk_var idx_var); index]) idx_vars indexes in
        let ands =  (List.map (fun indexes -> Term.mk_and (mk_index_equalities idx_vars (List.rev indexes))) indexes) in
        (* Format.printf "ANDS: %a@." (Lib.pp_print_list Term.pp_print_term ",") ands; *)
        let body = Term.mk_or (equation :: 
        ands ) in
            let equation = mk_forall body in
            (* Format.printf "Asserting equation for %a: %a.@."
                      StateVar.pp_print_state_var state_var
                      Term.pp_print_term equation; *)
            SMTSolver.assert_term solver equation
        )) state_var_map ) !defined_indexes;
        KEvent.log L_info 
          "Parsing interpreter input file %s"
          (Flags.input_file ()); 

  (* Run the system *)
  if (SMTSolver.check_sat solver) then
    (

      (* Extract execution path from model *)
      let path = 
        Model.path_from_model 
          (TransSys.state_vars trans_sys)
            (* (SMTSolver.get_model solver) *)
            (SMTSolver.get_var_values solver
               (TransSys.get_state_var_bounds trans_sys)
               (TransSys.vars_of_bounds trans_sys
                  Numeral.zero (Numeral.of_int steps)))
          Numeral.(pred (of_int steps))
      in
      let path = Model.path_to_list path in
        (* Format.printf "Statevars %a@." (Lib.pp_print_list (fun ppf (sv, vals) ->
         Format.fprintf ppf "%a, %a;" StateVar.pp_print_state_var sv (Lib.pp_print_list Model.pp_print_value "@,") vals) ",@.") merged_paths; *)

      (* Output execution path *)
      KEvent.execution_path
        ~full_contract:contract_monitor
        input_sys
        trans_sys 
        path
    )

  else

    (* Transition relation must be satisfiable *)
    KEvent.log L_error "Transition relation not satisfiable"


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
