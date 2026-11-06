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

(* A readable normal form of a transition system, for a language model.

   Whatever the input language, Kind 2 reasons on a transition system: an
   initial predicate and a transition relation over state variables, the
   relation applying the predicates of the subsystems. As stored, these
   terms are far from readable: the relation of a program compiled to MoXI
   has a few hundred distinct subterms, but millions of nodes once written
   as a tree, because each branch of the program repeats the path that
   leads to it. The steps below recover the structure:

   - [mk_inline] unfolds lets and the predicates of the subsystems, so that
     everything is over the state variables of the top system;

   - [mk_normal] pushes negations to the literals, flattens conjunctions
     and disjunctions, and factors [(or (and A X) (and B X))] into
     [(and X (or A B))]: this is what undoes the repetition of the paths.
     [(or (and c (= x e1)) (and (not c) (= x e2)))] then reads
     [(= x (ite c e1 e2))], and comparisons of zero-extended bit vectors
     lose their extension;

   - [eliminate] substitutes the inputs that a transition only uses as
     names for intermediate values, as a program compiled to single
     assignments has many of;

   - [analyze] splits the relation into what holds at every step and a
     choice between transitions, each made of a guard, assignments, and
     variables left unchanged. Boolean variables with a fixed value before
     and after each transition are the control location;

   - [render] keeps what the property depends on, and prints the rest with
     the subterms used several times named once.

   All but the last step give an equivalent system, up to the eliminated
   inputs. The model only learns of the system what this module prints, so
   [check] has a solver confirm it. *)

module TH = Term.TermHashtbl
module VS = Var.VarSet
module SVS = StateVar.StateVarSet

(* {1 Access to terms} *)

let app_of t =
  match Term.destruct t with
  | exception _ -> None
  | Term.T.App (s, args) -> Some (Symbol.node_of_symbol s, args)
  | _ -> None

let var_of t =
  match Term.destruct t with
  | exception _ -> None
  | Term.T.Var v -> Some v
  | _ -> None

let conjuncts t =
  match app_of t with Some (`AND, args) -> args | _ -> [ t ]

let disjuncts t =
  match app_of t with Some (`OR, args) -> args | _ -> [ t ]

let is_true t = Term.equal t Term.t_true
let is_false t = Term.equal t Term.t_false

(* The functions of [Term] on negations do not accept a quantified term *)
let negate t =
  try Term.negate_simplify t with Invalid_argument _ -> Term.mk_not t

let is_negated t = try Term.is_negated t with Invalid_argument _ -> false

let unnegate t = try Term.unnegate t with Invalid_argument _ -> t

let is_bool_term t = Type.is_bool (Term.type_of_term t)

(* The state variable of a variable, also for a constant one *)
let state_var_of v =
  if Var.is_state_var_instance v || Var.is_const_state_var v
  then Some (Var.state_var_of_state_var_instance v)
  else None

(* Free variables of terms, memoized: the terms are small as graphs but
   not as trees. *)
let mk_vars_of () =
  let memo = TH.create 1024 in
  let rec vars t =
    match TH.find_opt memo t with
    | Some s -> s
    | None ->
      let s =
        match Term.destruct t with
        | exception _ -> Term.vars_of_term t
        | Term.T.Var v -> VS.singleton v
        | Term.T.Const _ -> VS.empty
        | Term.T.App (_, args) ->
          List.fold_left (fun acc a -> VS.union acc (vars a)) VS.empty args
      in
      TH.add memo t s ;
      s
  in
  vars

(* Replace subterms, memoized *)
let subst pairs =
  let memo = TH.create 256 in
  List.iter (fun (a, b) -> TH.replace memo a b) pairs ;
  let rec go t =
    match TH.find_opt memo t with
    | Some r -> r
    | None ->
      let r =
        match Term.destruct t with
        | exception _ -> t
        | Term.T.App (s, args) -> Term.mk_app s (List.map go args)
        | _ -> t
      in
      TH.add memo t r ;
      r
  in
  go

(* {1 Inlining} *)

(* [term] with lets unfolded and the predicates of [uf_defs] inlined. A
   subterm with a quantifier is left as it is. *)
let mk_inline uf_defs =
  let memo = TH.create 1024 in
  let rec inline term =
    match TH.find_opt memo term with
    | Some t -> t
    | None ->
      let t =
        if Term.has_quantifier term then term
        else
          Term.eval_t (fun flat args ->
            match flat with
            | Term.T.Var v -> Term.mk_var v
            | Term.T.Const s -> Term.mk_const s
            | Term.T.App (s, _) -> (
              match Symbol.node_of_symbol s with
              | `UF uf when List.mem_assq uf uf_defs ->
                let vars, def = List.assq uf uf_defs in
                inline (Term.apply_subst (List.combine vars args) def)
              | _ -> Term.mk_app s args))
            term
      in
      TH.add memo term t ;
      t
  in
  inline

(* {1 Normal form} *)

(* A conjunction or disjunction, flat and without duplicates, simplified
   with the constants and with complementary arguments. *)
let mk_nary ~unit ~zero ~is_same ~mk args =
  let seen = TH.create 7 in
  let rec add acc t =
    if Term.equal t unit then acc
    else
      match app_of t with
      | Some (node, args') when is_same node -> List.fold_left add acc args'
      | _ ->
        if TH.mem seen t then acc
        else ( TH.add seen t () ; t :: acc )
  in
  let flat = List.rev (List.fold_left add [] args) in
  if List.exists (Term.equal zero) flat then zero
  else if List.exists (fun t -> TH.mem seen (negate t)) flat then zero
  else mk flat

let mk_conj =
  mk_nary ~unit:Term.t_true ~zero:Term.t_false
    ~is_same:(function `AND -> true | _ -> false) ~mk:Term.mk_and

let mk_disj =
  mk_nary ~unit:Term.t_false ~zero:Term.t_true
    ~is_same:(function `OR -> true | _ -> false) ~mk:Term.mk_or

(* {2 Bit vectors} *)

let is_bv_const t =
  try Term.is_bitvector t || Term.is_ubitvector t
  with Invalid_argument _ -> false

let is_bv t =
  let ty = Term.type_of_term t in
  Type.is_bitvector ty || Type.is_ubitvector ty

let bv_size t = Type.bitvectorsize (Term.type_of_term t)

(* The same kind of constant as [c], with the bits [b] *)
let const_like c b = if Term.is_ubitvector c then Term.mk_ubv b else Term.mk_bv b

(* The bits [hi] to [lo] of a constant *)
let const_slice hi lo c =
  const_like c (Bitvector.bvextract hi lo (Term.bitvector_of_term c))

let const_is_zero c =
  let b = Term.bitvector_of_term c in
  Bitvector.equal b (Bitvector.zero (Bitvector.length_of_bitvector b))

(* [Some (z, x)] if [t] is [x] extended with the zeros [z] *)
let zext_of t =
  match app_of t with
  | Some (`BVCONCAT, [ z; x ]) when is_bv_const z && const_is_zero z ->
    Some (z, x)
  | _ -> None

(* The [w] low bits of a term, when that does not need an extraction *)
let low_bits w t =
  if not (is_bv t) then None
  else
    let n = bv_size t in
    if n = w then Some t
    else if n < w then None
    else if is_bv_const t then Some (const_slice (w - 1) 0 t)
    else
      match zext_of t with
      | None -> None
      | Some (z, x) ->
        let m = bv_size x in
        if m = w then Some x
        else if m > w then None
        else
          Some (Term.mk_bvconcat (const_like z (Bitvector.zero (w - m))) x)

(* [a] and [b] without a common extension with zeros: the comparison is
   then the same, and the sign bit of both sides was zero *)
let unextended a b =
  let of_const x c =
    let w = bv_size x and n = bv_size c in
    if const_is_zero (const_slice (n - 1) w c)
    then Some (const_slice (w - 1) 0 c) else None
  in
  match zext_of a, zext_of b with
  | Some (_, x), Some (_, y) when bv_size x = bv_size y -> Some (x, y)
  | Some (_, x), None when is_bv_const b ->
    Option.map (fun c -> x, c) (of_const x b)
  | None, Some (_, y) when is_bv_const a ->
    Option.map (fun c -> c, y) (of_const y a)
  | _ -> None

(* Remove what compiling integer promotions leaves in a term, which is
   only noise to read. *)
let peephole term =
  let fold_add args =
    if List.for_all is_bv_const args then
      match args with
      | a :: tl ->
        let add x y =
          const_like x
            (Bitvector.ubv_add
               (Term.bitvector_of_term x) (Term.bitvector_of_term y))
        in
        Some (List.fold_left add a tl)
      | [] -> None
    else None
  in
  let compare_with mk a b =
    match unextended a b with
    | Some (x, y) -> mk [ x; y ]
    | None -> term
  in
  match app_of term with
  | Some (`BVADD, args) -> (
    match fold_add args with Some c -> c | None -> term)
  | Some (`EQ, [ a; b ]) when is_bv a -> compare_with Term.mk_eq a b
  | Some ((`BVSLT | `BVULT), [ a; b ]) -> compare_with Term.mk_bvult a b
  | Some ((`BVSLE | `BVULE), [ a; b ]) -> compare_with Term.mk_bvule a b
  | Some ((`BVSGT | `BVUGT), [ a; b ]) -> compare_with Term.mk_bvugt a b
  | Some ((`BVSGE | `BVUGE), [ a; b ]) -> compare_with Term.mk_bvuge a b
  | Some (`BVEXTRACT (hi, lo), [ a ]) when Numeral.(equal lo zero) -> (
    let w = Numeral.to_int hi + 1 in
    match low_bits w a with
    | Some x -> x
    | None -> (
      (* The low bits of these operations only depend on the low bits of
         their arguments *)
      match Term.destruct a with
      | exception _ -> term
      | Term.T.App (s, args) -> (
        match Symbol.node_of_symbol s with
        | `BVADD | `BVSUB | `BVMUL | `BVAND | `BVOR | `BVXOR ->
          let low = List.map (low_bits w) args in
          if List.for_all Option.is_some low then
            Term.mk_app s (List.map Option.get low)
          else term
        | _ -> term)
      | _ -> term))
  | _ -> term

(* {2 Canonical symbols} *)

(* [Symbol.mk_symbol] returns a new symbol at each call for the bit-vector
   operators without parameters, whose equality in [Symbol] is always
   false. Two terms built by [Term.mk_bvult] are then different, however
   equal they read, and factoring cannot see what they have in common. The
   terms here all use the first symbol seen of each operator. *)
let canonical_key =
  Domain.DLS.new_key (fun () -> (Hashtbl.create 31 : (int, Symbol.t) Hashtbl.t))

let canonical_symbol s =
  let key =
    match Symbol.node_of_symbol s with
    | `BVNOT -> 1 | `BVNEG -> 2 | `BVAND -> 3 | `BVOR -> 4 | `BVXOR -> 5
    | `BVADD -> 6 | `BVSUB -> 7 | `BVMUL -> 8 | `BVUDIV -> 9 | `BVSDIV -> 10
    | `BVUREM -> 11 | `BVSREM -> 12 | `BVSMOD -> 13 | `BVSHL -> 14
    | `BVLSHR -> 15 | `BVASHR -> 16 | `BVULT -> 17 | `BVULE -> 18
    | `BVUGT -> 19 | `BVUGE -> 20 | `BVSLT -> 21 | `BVSLE -> 22
    | `BVSGT -> 23 | `BVSGE -> 24 | `BVCONCAT -> 25
    | _ -> 0
  in
  if key = 0 then s
  else
    let table = Domain.DLS.get canonical_key in
    match Hashtbl.find_opt table key with
    | Some s' -> s'
    | None -> Hashtbl.add table key s ; s

(* The term with the canonical symbol at its top *)
let canonical_top t =
  match Term.destruct t with
  | exception _ -> t
  | Term.T.App (s, args) ->
    let s' = canonical_symbol s in
    if s' == s then t else Term.mk_app s' args
  | _ -> t

(* {2 Normalization} *)

(* The sides of an equation with a variable on the left, a literal over a
   Boolean variable counting as an equation with a constant. *)
let oriented t =
  let is_var a = Option.is_some (var_of a) in
  match app_of t with
  | Some (`EQ, [ a; b ]) ->
    (if is_var a then [ (a, b) ] else [])
    @ (if is_var b then [ (b, a) ] else [])
  | Some (`NOT, [ a ]) when is_var a -> [ (a, Term.t_false) ]
  | _ -> if is_var t then [ (t, Term.t_true) ] else []

(* A constant, of which two different ones have different values *)
let is_value t =
  is_bv_const t
  || (try Term.is_numeral t with Invalid_argument _ -> false)

(* [(= (ite c k1 k2) k)] over constants, as a condition, through nested
   ites *)
let constant_ite a k =
  let rec go a =
    match app_of a with
    | Some (`ITE, [ c; a1; a2 ]) -> (
      match go a1, go a2 with
      | Some e1, Some e2 -> Some (Term.mk_ite c e1 e2)
      | _ -> None)
    | _ ->
      if is_value a
      then Some (if Term.equal a k then Term.t_true else Term.t_false)
      else None
  in
  if is_value k && (match app_of a with Some (`ITE, _) -> true | _ -> false)
  then go a
  else None

type normal = {
  nf : Term.t -> Term.t ;
  or_smart : Term.t list -> Term.t ;
}

let mk_normal () =
  let memo_p = TH.create 1024
  and memo_n = TH.create 1024
  and memo_i = TH.create 1024 in
  let neg_if pol t = if pol then t else negate t in
  let rec nf pol term =
    let memo = if pol then memo_p else memo_n in
    match TH.find_opt memo term with
    | Some t -> t
    | None ->
      let t = nf' pol term in
      TH.add memo term t ;
      t
  and nf' pol term =
    match app_of term with
    | None -> neg_if pol term
    | Some (node, args) -> (
      match node, args with
      | `NOT, [ a ] -> nf (not pol) a
      | `AND, _ ->
        let args = List.map (nf pol) args in
        if pol then mk_conj args else or_smart args
      | `OR, _ ->
        let args = List.map (nf pol) args in
        if pol then or_smart args else mk_conj args
      | `IMPLIES, _ -> (
        match List.rev args with
        | [] -> neg_if pol Term.t_true
        | c :: rev_hyps ->
          let hyps = List.rev_map (nf (not pol)) rev_hyps in
          let c = nf pol c in
          if pol then or_smart (hyps @ [ c ]) else mk_conj (hyps @ [ c ]))
      | `EQ, [ a; b ] when Term.equal a b -> neg_if pol Term.t_true
      | `EQ, [ a; b ] when is_value a && is_value b ->
        (* Different constants, or they would be the same term *)
        neg_if pol Term.t_false
      | `EQ, [ a; b ] when is_true a -> nf pol b
      | `EQ, [ a; b ] when is_true b -> nf pol a
      | `EQ, [ a; b ] when is_false a -> nf (not pol) b
      | `EQ, [ a; b ] when is_false b -> nf (not pol) a
      | `EQ, [ a; b ] when constant_ite a b <> None -> (
        match constant_ite a b with
        | Some r -> nf pol r
        | None -> assert false)
      | `EQ, [ a; b ] when constant_ite b a <> None -> (
        match constant_ite b a with
        | Some r -> nf pol r
        | None -> assert false)
      | `ITE, [ c; a; b ] when is_bool_term term ->
        let c = nf true c in
        let a = nf pol a and b = nf pol b in
        if is_true c then a
        else if is_false c then b
        else if Term.equal a b then a
        else if is_true a then or_smart [ c; b ]
        else if is_false a then mk_conj [ negate c; b ]
        else if is_true b then or_smart [ negate c; a ]
        else if is_false b then mk_conj [ c; a ]
        else if is_negated c then Term.mk_ite (negate c) b a
        else Term.mk_ite c a b
      | _ -> neg_if pol (rebuild term))
  (* Below the Boolean structure *)
  and rebuild term =
    match Term.destruct term with
    | exception _ -> term
    | Term.T.App (s, args) ->
      let t = Term.mk_app (canonical_symbol s) (List.map inner args) in
      canonical_top (peephole t)
    | _ -> term
  and inner t =
    if is_bool_term t then nf true t
    else
      match TH.find_opt memo_i t with
      | Some r -> r
      | None ->
        let r =
          match app_of t with
          | Some (`ITE, [ c; a; b ]) ->
            let c = nf true c and a = inner a and b = inner b in
            if is_true c then a
            else if is_false c then b
            else if Term.equal a b then a
            else if is_negated c then Term.mk_ite (negate c) b a
            else Term.mk_ite c a b
          | _ -> rebuild t
        in
        TH.add memo_i t r ;
        r
  (* A disjunction, factored *)
  and or_smart args =
    let t = mk_disj args in
    match app_of t with
    | Some (`OR, ds) -> (
      let parts = List.map conjuncts ds in
      let sets =
        List.map (fun p ->
          let s = TH.create 7 in
          List.iter (fun c -> TH.replace s c ()) p ;
          s) parts
      in
      let common =
        List.filter (fun c -> List.for_all (fun s -> TH.mem s c) sets)
          (List.hd parts)
      in
      if common <> [] then (
        let is_common c = List.exists (Term.equal c) common in
        let rest =
          List.map (fun p ->
            mk_conj (List.filter (fun c -> not (is_common c)) p)) parts
        in
        mk_conj (common @ [ or_smart rest ])
      )
      else
        match ds with
        | [ a; b ] -> (
          match merge_branches a b with Some r -> r | None -> t)
        | _ -> t)
    | _ -> t
  (* [(or (and c (= x e1)) (and (not c) (= x e2)))] as
     [(= x (ite c e1 e2))], for all the variables the two sides assign *)
  and merge_branches a b =
    let pa = conjuncts a and pb = conjuncts b in
    let in_b c = List.exists (Term.equal c) pb in
    match List.find_opt (fun c -> in_b (negate c)) pa with
    | None -> None
    | Some c ->
      let nc = negate c in
      let xs = List.filter (fun t -> not (Term.equal t c)) pa
      and ys = List.filter (fun t -> not (Term.equal t nc)) pb in
      if List.length xs <> List.length ys || xs = [] then None
      else
        let rec pair acc ys = function
          | [] -> if ys = [] then Some (List.rev acc) else None
          | x :: xs -> (
            let found =
              List.find_map (fun (v, e1) ->
                List.find_map (fun y ->
                  List.find_map (fun (v', e2) ->
                    if Term.equal v v' then Some (y, v, e1, e2) else None)
                    (oriented y)) ys)
                (oriented x)
            in
            match found with
            | None -> None
            | Some (y, v, e1, e2) ->
              let ys = List.filter (fun y' -> not (Term.equal y y')) ys in
              pair ((v, e1, e2) :: acc) ys xs)
        in
        match pair [] ys xs with
        | None -> None
        | Some eqs ->
          Some (
            mk_conj (List.map (fun (v, e1, e2) ->
              nf true (Term.mk_eq [ v; Term.mk_ite c e1 e2 ])) eqs))
  in
  { nf = nf true ; or_smart }

(* {2 Elimination of intermediate inputs} *)

(* Substitute away the variables of [aux] that a conjunction defines, as
   long as they do not occur outside of the conjunction: the definition can
   then be dropped, a variable of [aux] being free at each step. Each
   disjunct of a disjunction has its own choice of such a variable, since
   an existential quantification distributes over the disjunction. *)
let eliminate { nf ; or_smart } vars aux term =
  let eliminable outside v = VS.mem v aux && not (VS.mem v outside) in
  (* A definition among the conjuncts, with the other conjuncts *)
  let definition outside cs =
    let try_side a b =
      match var_of a with
      | Some v when eliminable outside v && not (VS.mem v (vars b)) ->
        Some (a, b)
      | _ -> None
    in
    let rec go before = function
      | [] -> None
      | c :: tl -> (
        let def =
          match app_of c with
          | Some (`EQ, [ a; b ]) -> (
            match try_side a b with
            | Some d -> Some d
            | None -> try_side b a)
          | _ -> None
        in
        match def with
        | Some (a, b) -> Some (a, b, List.rev_append before tl)
        | None -> go (c :: before) tl)
    in
    go [] cs
  in
  let rec elim fuel outside t =
    if fuel = 0 then t
    else
      match app_of t with
      | Some (`AND, cs) -> (
        match definition outside cs with
        | Some (a, b, rest) ->
          let s = subst [ (a, b) ] in
          elim (fuel - 1) outside (nf (mk_conj (List.map s rest)))
        | None ->
          let others c =
            List.fold_left (fun acc c' ->
              if Term.equal c c' then acc else VS.union acc (vars c'))
              outside cs
          in
          let cs' =
            List.map (fun c ->
              match app_of c with
              | Some (`OR, _) -> elim (fuel - 1) (others c) c
              | _ -> c) cs
          in
          if List.for_all2 Term.equal cs cs' then t
          else elim (fuel - 1) outside (nf (mk_conj cs')))
      | Some (`OR, ds) ->
        let ds' = List.map (elim (fuel - 1) outside) ds in
        if List.for_all2 Term.equal ds ds' then t else or_smart ds'
      | _ -> t
  in
  elim 256 VS.empty term

(* {2 Simplification under literals} *)

let is_literal t =
  match app_of (unnegate t) with
  | Some ((`AND | `OR | `ITE), _) -> false
  | _ -> true

(* Replace the atoms that [facts] decides in the Boolean structure *)
let assume_facts facts t =
  let memo = TH.create 64 in
  let rec go t =
    match TH.find_opt memo t with
    | Some r -> r
    | None ->
      let r =
        match TH.find_opt facts t with
        | Some b -> if b then Term.t_true else Term.t_false
        | None -> (
          match app_of t with
          | Some (`AND, args) -> mk_conj (List.map go args)
          | Some (`OR, args) -> mk_disj (List.map go args)
          | Some (`NOT, [ a ]) ->
            let a' = go a in
            if is_true a' then Term.t_false
            else if is_false a' then Term.t_true
            else negate a'
          | _ -> t)
      in
      TH.add memo t r ;
      r
  in
  go t

(* Simplify the other conjuncts under the literals of a conjunction, and
   the other disjuncts under the negated literals of a disjunction. *)
let mk_simplify { nf ; _ } =
  let memo = TH.create 1024 in
  let rec simp t =
    match TH.find_opt memo t with
    | Some r -> r
    | None ->
      let r =
        match app_of t with
        | Some (`AND, args) -> under true args
        | Some (`OR, args) -> under false args
        | _ -> t
      in
      TH.add memo t r ;
      r
  and under is_conj args =
    let args = List.map simp args in
    let mk = if is_conj then mk_conj else mk_disj in
    let lits, rest = List.partition is_literal args in
    if rest = [] || lits = [] then nf (mk args)
    else
      let facts = TH.create 7 in
      List.iter (fun l ->
        let positive = not (is_negated l) in
        TH.replace facts (unnegate l)
          (if is_conj then positive else not positive)) lits ;
      let rest' = List.map (assume_facts facts) rest in
      let t = nf (mk (lits @ rest')) in
      if List.for_all2 Term.equal rest rest' then t else simp t
  in
  simp

(* {1 Structure} *)

(* What a part of the relation does to the next state *)
type step = {
  guards : Term.t list ;
  (* Conjuncts that are not assignments *)
  assigns : (StateVar.t * Term.t) list ;
  (* The next value of the variable *)
  unchanged : StateVar.t list ;
  (* The next value of the variable is the current one *)
}

type transition = {
  src : int option ;
  dst : int option ;
  (* Control location before and after *)
  loc_literals : Term.t list ;
  (* The literals over the location bits, [src] and [dst] as terms *)
  step : step ;
}

type analysis = {
  sys : TransSys.t ;
  orig_init : Term.t ;
  orig_trans : Term.t ;
  aux : VS.t ;
  (* The inputs that may have been eliminated *)
  init : Term.t list ;
  always : Term.t list ;
  (* What both the initial states and every step impose on a state *)
  first_flags : StateVar.t list ;
  (* Variables true in the initial state and false in the others *)
  common : step ;
  transitions : transition list ;
  loc_bits : StateVar.t list ;
  normal : normal ;
  vars : Term.t -> VS.t ;
  inline : Term.t -> Term.t ;
}

let state_var_at off v =
  if Var.is_state_var_instance v
  && Numeral.equal (Var.offset_of_state_var_instance v) off
  then Some (Var.state_var_of_state_var_instance v)
  else None

(* The state variable of the next value of a variable of the state *)
let next_state_var v =
  match state_var_at Numeral.one v with
  | Some sv when not (StateVar.is_input sv) -> Some sv
  | _ -> None

let var_at sv off = Var.mk_state_var_instance sv off

let term_at sv off = Term.mk_var (var_at sv off)

let same_sv = StateVar.equal_state_vars

(* Split conjuncts into assignments, frame conditions and the rest. A
   variable with several equations gets the one that computes its value as
   assignment, the ones with a constant reading as conditions on it: with
   [(= x' (bvadd x y))] and [(= x' #x1e)], [x] is updated and then tested. *)
let classify vars cs =
  let computes c =
    match oriented c with
    | (_, e) :: _ -> not (is_value e || is_true e || is_false e)
    | [] -> false
  in
  let computing, others = List.partition computes cs in
  let cs = computing @ others in
  let assigned = ref SVS.empty in
  let try_assign v e =
    match next_state_var v with
    | Some sv
      when not (SVS.mem sv !assigned)
        && not (VS.mem (var_at sv Numeral.one) (vars e)) -> Some (sv, e)
    | _ -> None
  in
  let rec go g a u = function
    | [] ->
      { guards = List.rev g ; assigns = List.rev a ; unchanged = List.rev u }
    | c :: tl -> (
      let assign =
        List.find_map (fun (l, e) ->
          match var_of l with Some v -> try_assign v e | None -> None)
          (oriented c)
      in
      match assign with
      | None -> go (c :: g) a u tl
      | Some (sv, e) ->
        assigned := SVS.add sv !assigned ;
        if Term.equal e (term_at sv Numeral.zero)
        then go g a (sv :: u) tl
        else go g ((sv, e) :: a) u tl)
  in
  go [] [] [] cs

let step_conjuncts { guards ; assigns ; unchanged } =
  guards
  @ List.map (fun (sv, e) -> Term.mk_eq [ term_at sv Numeral.one ; e ]) assigns
  @ List.map (fun sv ->
      Term.mk_eq [ term_at sv Numeral.one ; term_at sv Numeral.zero ]) unchanged

(* The Boolean variable and value of a literal at an offset *)
let literal_at off t =
  let of_var t =
    match var_of t with
    | Some v -> state_var_at off v
    | None -> None
  in
  match app_of t with
  | Some (`NOT, [ a ]) -> Option.map (fun sv -> sv, false) (of_var a)
  | _ -> Option.map (fun sv -> sv, true) (of_var t)

(* The Boolean variables with a known value before and after every
   transition, sorted by name *)
let location_bits = function
  | [] | [ _ ] -> []
  | first :: rest ->
    let bits_of cs off =
      List.filter_map (fun c -> Option.map fst (literal_at off c)) cs
      |> SVS.of_list
    in
    let both cs = SVS.inter (bits_of cs Numeral.zero) (bits_of cs Numeral.one) in
    List.fold_left (fun acc cs -> SVS.inter acc (both cs)) (both first) rest
    |> SVS.elements
    |> List.sort (fun a b ->
        compare (StateVar.name_of_state_var a) (StateVar.name_of_state_var b))

(* The number of a location: the bit of the smallest name is the lowest *)
let location_value bits values =
  let rec go i acc = function
    | [] -> Some acc
    | b :: tl -> (
      match List.find_opt (fun (sv, _) -> same_sv sv b) values with
      | None -> None
      | Some (_, v) -> go (i + 1) (if v then acc + (1 lsl i) else acc) tl)
  in
  if bits = [] then None else go 0 0 bits

let is_location_literal bits off t =
  match literal_at off t with
  | Some (sv, _) -> List.exists (same_sv sv) bits
  | None -> false

let analyze sys =
  let inline = mk_inline (TransSys.uf_defs sys) in
  let normal = mk_normal () in
  let vars = mk_vars_of () in
  let simplify = mk_simplify normal in
  let orig_init = TransSys.init_of_bound None sys Numeral.zero |> inline in
  let orig_trans = TransSys.trans_of_bound None sys Numeral.one |> inline in
  let init = normal.nf orig_init in
  let trans = normal.nf orig_trans in
  (* The inputs that are free at each step: used at one offset, and neither
     in the initial states, which share their first value with the first
     step, nor in a property *)
  let aux =
    let in_trans = vars trans in
    let in_props =
      List.fold_left (fun acc p ->
        VS.union acc (vars (inline p.Property.prop_term)))
        (vars init) (TransSys.get_properties sys)
    in
    let mentions sv s =
      VS.exists (fun v ->
        match state_var_of v with
        | Some sv' -> same_sv sv sv'
        | None -> false) s
    in
    VS.filter (fun v ->
      match state_var_at Numeral.zero v, state_var_at Numeral.one v with
      | Some sv, None | None, Some sv ->
        StateVar.is_input sv
        && not (VS.mem (var_at sv Numeral.zero) in_trans
                && VS.mem (var_at sv Numeral.one) in_trans)
        && not (mentions sv in_props)
      | _ -> false) in_trans
  in
  (* The state variables that are only ever written: their current value is
     only used to be kept, by a frame condition. They say nothing of the
     rest of the state, so they are as good as inputs. *)
  let write_only =
    let reads = ref SVS.empty in
    let seen = TH.create 1024 in
    let frame_of t =
      match app_of t with
      | Some (`EQ, [ a; b ]) -> (
        match var_of a, var_of b with
        | Some va, Some vb -> (
          match next_state_var va, state_var_at Numeral.zero vb,
                next_state_var vb, state_var_at Numeral.zero va with
          | Some x, Some y, _, _ when same_sv x y -> true
          | _, _, Some x, Some y when same_sv x y -> true
          | _ -> false)
        | _ -> false)
      | _ -> false
    in
    let rec go t =
      if not (TH.mem seen t) then (
        TH.add seen t () ;
        if not (frame_of t) then
          match Term.destruct t with
          | exception _ ->
            VS.iter (fun v ->
              Option.iter (fun sv -> reads := SVS.add sv !reads)
                (state_var_of v)) (Term.vars_of_term t)
          | Term.T.App (_, args) -> List.iter go args
          | Term.T.Var v ->
            Option.iter (fun sv -> reads := SVS.add sv !reads)
              (state_var_at Numeral.zero v)
          | _ -> ()
      )
    in
    go trans ;
    let elsewhere =
      List.fold_left (fun acc p ->
        VS.union acc (vars (inline p.Property.prop_term)))
        (vars init) (TransSys.get_properties sys)
    in
    let in_elsewhere sv =
      VS.exists (fun v ->
        match state_var_of v with
        | Some sv' -> same_sv sv sv'
        | None -> false) elsewhere
    in
    List.filter (fun sv ->
      not (StateVar.is_input sv)
      && not (StateVar.is_const sv)
      && not (SVS.mem sv !reads)
      && not (in_elsewhere sv)) (TransSys.state_vars sys)
  in
  (* Their frame conditions go, and their next values can be eliminated *)
  let trans =
    let frames =
      List.concat_map (fun sv ->
        let x' = term_at sv Numeral.one and x = term_at sv Numeral.zero in
        [ Term.mk_eq [ x' ; x ], Term.t_true ;
          Term.mk_eq [ x ; x' ], Term.t_true ]) write_only
    in
    normal.nf (subst frames trans)
  in
  let projected =
    List.fold_left (fun acc sv ->
      VS.add (var_at sv Numeral.zero) (VS.add (var_at sv Numeral.one) acc))
      VS.empty write_only
  in
  let aux = VS.union aux projected in
  (* Eliminating variables lets branches merge, which lets more variables be
     eliminated *)
  let rec rounds n t =
    let normal = mk_normal () in
    let t' =
      eliminate normal vars aux (normal.nf t) |> mk_simplify normal
    in
    if n = 0 || Term.equal t t' then t' else rounds (n - 1) t'
  in
  let trans = rounds 8 trans in
  let init_cs = conjuncts (simplify init) in
  let trans_cs = conjuncts trans in
  (* Conditions on a state, imposed on the initial states and on the state
     after each step *)
  let always =
    List.filter (fun c ->
      let c' = Term.bump_state Numeral.one c in
      List.exists (Term.equal c') trans_cs) init_cs
  in
  let in_always c = List.exists (Term.equal c) always in
  let init_cs = List.filter (fun c -> not (in_always c)) init_cs in
  let trans_cs =
    let bumped = List.map (Term.bump_state Numeral.one) always in
    List.filter (fun c -> not (List.exists (Term.equal c) bumped)) trans_cs
  in
  (* Variables that only tell the first state from the others, as Kind 2
     has for each system *)
  let first_flags =
    List.filter_map (fun c ->
      match literal_at Numeral.one c with
      | Some (sv, false)
        when List.exists (Term.equal (term_at sv Numeral.zero)) init_cs ->
        Some sv
      | _ -> None) trans_cs
  in
  let is_flag_literal c =
    List.exists (fun sv ->
      Term.equal c (term_at sv Numeral.zero)
      || Term.equal c (negate (term_at sv Numeral.one))) first_flags
  in
  let init_cs = List.filter (fun c -> not (is_flag_literal c)) init_cs in
  let trans_cs = List.filter (fun c -> not (is_flag_literal c)) trans_cs in
  (* The choice between transitions: the largest disjunction that moves
     the state *)
  let moves c = VS.exists (fun v -> next_state_var v <> None) (vars c) in
  let choice =
    List.fold_left (fun best c ->
      let n = List.length (disjuncts c) in
      if n >= 2 && moves c
         && (match best with
             | None -> true
             | Some b -> n > List.length (disjuncts b))
      then Some c else best) None trans_cs
  in
  let common_cs, choice_cs =
    match choice with
    | None -> trans_cs, []
    | Some c ->
      List.filter (fun c' -> not (Term.equal c c')) trans_cs,
      List.map conjuncts (disjuncts c)
  in
  (* Factoring may have merged transitions that have something in common:
     a disjunction whose disjuncts each set a Boolean variable is a choice
     between transitions and not a condition of one. *)
  let rec sets_a_bool t =
    match app_of t with
    | Some ((`AND | `OR), args) -> List.exists sets_a_bool args
    | _ -> Option.is_some (literal_at Numeral.one t)
  in
  let sets_control c = List.for_all sets_a_bool (disjuncts c) in
  let rec split cs =
    match
      List.find_opt (fun c ->
        (match app_of c with Some (`OR, _) -> true | _ -> false)
        && sets_control c) cs
    with
    | None -> [ cs ]
    | Some c ->
      let rest = List.filter (fun c' -> not (Term.equal c c')) cs in
      List.concat_map (fun d -> split (rest @ conjuncts d)) (disjuncts c)
  in
  let choice_cs = List.concat_map split choice_cs in
  let loc_bits = location_bits choice_cs in
  let transitions =
    List.map (fun cs ->
      let values off =
        List.filter_map (fun c ->
          if is_location_literal loc_bits off c then literal_at off c else None)
          cs
      in
      let is_loc c =
        is_location_literal loc_bits Numeral.zero c
        || is_location_literal loc_bits Numeral.one c
      in
      let locs, rest = List.partition is_loc cs in
      {
        src = location_value loc_bits (values Numeral.zero) ;
        dst = location_value loc_bits (values Numeral.one) ;
        loc_literals = locs ;
        step = classify vars rest ;
      }) choice_cs
    |> (fun l ->
        if loc_bits = [] then l
        else List.stable_sort (fun a b -> compare a.src b.src) l)
  in
  {
    sys ; orig_init ; orig_trans ; aux ;
    init = init_cs ; always ; first_flags ;
    common = classify vars common_cs ;
    transitions ; loc_bits ; normal ; vars ; inline ;
  }

(* The initial predicate and the relation, as this module understood them *)
let rebuilt a =
  let bumped = List.map (Term.bump_state Numeral.one) a.always in
  let flags_init = List.map (fun sv -> term_at sv Numeral.zero) a.first_flags
  and flags_next =
    List.map (fun sv -> negate (term_at sv Numeral.one)) a.first_flags
  in
  let init = Term.mk_and (flags_init @ a.init @ a.always) in
  let choice =
    match a.transitions with
    | [] -> []
    | ts ->
      [ Term.mk_or (List.map (fun t ->
          Term.mk_and (t.loc_literals @ step_conjuncts t.step)) ts) ]
  in
  init, Term.mk_and (flags_next @ bumped @ step_conjuncts a.common @ choice)

(* {1 The goal} *)

(* What the property says, as a condition on the state: the definitions of
   the variables it is about are expanded. A query of a MoXI model, for
   instance, is a variable that is true in the initial state and whose next
   value is what is asked of the current state, and it is what must be
   invariant. This amounts to what is asked of the current state being
   invariant. *)
let goal_of a prop =
  let nf = a.normal.nf in
  let step_assign sv =
    List.find_opt (fun (sv', _) -> same_sv sv sv') a.common.assigns
  in
  let is_current e =
    VS.for_all (fun v -> state_var_at Numeral.one v = None) (a.vars e)
  in
  let holds_initially t =
    List.exists (Term.equal t) (a.init @ a.always)
    || (match literal_at Numeral.zero t with
        | Some (sv, true) -> List.exists (same_sv sv) a.first_flags
        | _ -> false)
  in
  (* What holds of every state need not be said of it *)
  let known =
    let facts = TH.create 7 in
    List.iter (fun c ->
      if is_literal c then
        TH.replace facts (unnegate c) (not (is_negated c)))
      a.always ;
    assume_facts facts
  in
  let defs =
    List.filter_map (fun c ->
      match oriented c with
      | (l, e) :: _ when not (is_true e || is_false e) -> Some (l, e)
      | _ -> None) a.always
  in
  let rec expand fuel t =
    if fuel = 0 then t
    else
      let t' = nf (subst defs t) in
      let t' =
        match literal_at Numeral.zero t' with
        | Some (sv, true) when holds_initially t' -> (
          match step_assign sv with
          | Some (_, e) when is_current e -> e
          | _ -> t')
        | _ -> t'
      in
      if Term.equal t t' then t else expand (fuel - 1) t'
  in
  expand 8 (a.inline prop.Property.prop_term |> nf) |> known |> nf

(* {1 Cone of influence} *)

let svars_of a t =
  VS.fold (fun v acc ->
    match state_var_of v with
    | Some sv -> SVS.add sv acc
    | None -> acc) (a.vars t) SVS.empty

(* Whether a condition on a state concerns the variables of [cone]: an
   equation that defines a variable only does if that variable does. *)
let concerns a cone c =
  match oriented c with
  | [] -> not (SVS.is_empty (SVS.inter (svars_of a c) cone))
  | sides ->
    List.exists (fun (l, _) ->
      not (SVS.is_empty (SVS.inter (svars_of a l) cone))) sides

(* The state variables the goal depends on: the ones it mentions, the ones
   in a guard, and the ones used to compute the next value of one of
   these. *)
let cone a goal =
  let steps = a.common :: List.map (fun t -> t.step) a.transitions in
  let start =
    List.fold_left (fun acc { guards ; _ } ->
      List.fold_left (fun acc g -> SVS.union acc (svars_of a g)) acc guards)
      (svars_of a goal) steps
  in
  let rec fix cone =
    let cone' =
      List.fold_left (fun acc c ->
        if concerns a cone c then SVS.union acc (svars_of a c) else acc)
        cone (a.init @ a.always)
    in
    let cone' =
      List.fold_left (fun acc { assigns ; _ } ->
        List.fold_left (fun acc (sv, e) ->
          if SVS.mem sv cone then SVS.union acc (svars_of a e) else acc)
          acc assigns) cone' steps
    in
    if SVS.equal cone cone' then cone else fix cone'
  in
  fix start

(* {1 Printing} *)

let simple_symbol s =
  s <> ""
  && (match s.[0] with '0' .. '9' -> false | _ -> true)
  && String.for_all (function
    | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9'
    | '_' | '.' | '$' | '#' | '-' | '+' | '~' | '!' | '@' | '%' | '^' | '&'
    | '*' | '=' | '<' | '>' | '?' | '/' -> true
    | _ -> false) s

let quote s = if simple_symbol s then s else "|" ^ s ^ "|"

(* Unique names of the state variables, without their scopes if possible *)
let mk_names svars =
  let count = Hashtbl.create 64 in
  let short = List.map (fun sv -> sv, StateVar.name_of_state_var sv) svars in
  List.iter (fun (_, n) ->
    Hashtbl.replace count n
      (1 + Option.value ~default:0 (Hashtbl.find_opt count n))) short ;
  let table = Hashtbl.create 64 in
  List.iter (fun (sv, n) ->
    let n =
      if Hashtbl.find count n = 1 then n else StateVar.string_of_state_var sv
    in
    Hashtbl.replace table (StateVar.uid sv) (quote n)) short ;
  fun sv ->
    match Hashtbl.find_opt table (StateVar.uid sv) with
    | Some n -> n
    | None -> quote (StateVar.string_of_state_var sv)

(* A bit vector in hexadecimal when that is exact: 32 binary digits cost
   the model many more tokens than 8 hexadecimal ones. *)
let const_text t =
  let s = Format.asprintf "%a" Term.pp_print_term t in
  if is_bv_const t
  && String.length s > 2 && String.sub s 0 2 = "#b"
  && (String.length s - 2) mod 4 = 0
  then
    let n = (String.length s - 2) / 4 in
    "#x" ^ String.concat "" (List.init n (fun i ->
      Printf.sprintf "%x"
        (int_of_string ("0b" ^ String.sub s (2 + (4 * i)) 4))))
  else s

(* The subterms used at least twice and of at least [threshold] nodes get
   a name. Returns the definitions, in dependency order, and a printer. *)
let mk_printer ~name ~threshold roots =
  let uses = TH.create 1024 in
  let rec count t =
    match Term.destruct t with
    | exception _ -> ()
    | Term.T.App (_, args) ->
      let n = Option.value ~default:0 (TH.find_opt uses t) in
      TH.replace uses t (n + 1) ;
      if n = 0 then List.iter count args
    | _ -> ()
  in
  List.iter count roots ;
  let memo = TH.create 1024 in
  let defs = ref [] in
  let counter = ref 0 in
  let var_text v =
    match state_var_of v with
    | None -> Format.asprintf "%a" Var.pp_print_var v
    | Some sv ->
      if Var.is_const_state_var v then name sv
      else
        let off = Var.offset_of_state_var_instance v in
        name sv ^ (
          if Numeral.equal off Numeral.one then "'"
          else if Numeral.equal off Numeral.zero then ""
          else Format.asprintf "@%a" Numeral.pp_print_numeral off)
  in
  let rec text t =
    match TH.find_opt memo t with
    | Some r -> r
    | None ->
      let r =
        match Term.destruct t with
        | exception _ -> Format.asprintf "%a" Term.pp_print_term t, 1
        | Term.T.Var v -> var_text v, 1
        | Term.T.Const _ -> const_text t, 1
        | Term.T.App (s, args) ->
          let parts = List.map text args in
          let size = List.fold_left (fun acc (_, n) -> acc + n) 1 parts in
          let body =
            Format.asprintf "(%a %s)" Symbol.pp_print_symbol s
              (String.concat " " (List.map fst parts))
          in
          if Option.value ~default:0 (TH.find_opt uses t) > 1
          && size >= threshold then (
            incr counter ;
            let n = Printf.sprintf "_e%d" !counter in
            defs := (n, body) :: !defs ;
            n, 1
          )
          else body, size
      in
      TH.add memo t r ;
      r
  in
  (* Name the shared subterms in the order of the roots *)
  List.iter (fun t -> ignore (text t)) roots ;
  List.rev !defs, (fun t -> fst (text t))

type rendered = {
  text : string ;
  goal_text : string ;
  state_count : int ;
  omitted_count : int ;
}

let location_name i = Printf.sprintf "L%d" i

(* The number of nodes of a term written as a tree *)
let tree_size t =
  let memo = TH.create 64 in
  let rec go t =
    match TH.find_opt memo t with
    | Some n -> n
    | None ->
      let n =
        match Term.destruct t with
        | exception _ -> 1.
        | Term.T.App (_, args) ->
          List.fold_left (fun acc a -> acc +. go a) 1. args
        | _ -> 1.
      in
      TH.add memo t n ;
      n
  in
  go t

(* A term on its own: written out, unless that would be too long to be of
   any use, and then with its shared subterms named first. *)
let standalone_text ~name t =
  let threshold = if tree_size t < 400. then max_int else 4 in
  let defs, pp = mk_printer ~name ~threshold [ t ] in
  String.concat "\n" (List.map (fun (n, b) -> n ^ " := " ^ b) defs @ [ pp t ])

(* The location of a conjunction of literals over all the bits *)
let location_of_literals bits cs =
  if bits = [] || List.length cs <> List.length bits then None
  else
    let values = List.map (literal_at Numeral.zero) cs in
    if List.for_all Option.is_some values
    then location_value bits (List.map Option.get values)
    else None

let render in_sys a prop =
  let goal = goal_of a prop in
  let cone = cone a goal in
  let in_cone sv = SVS.mem sv cone in
  let all_svars = TransSys.state_vars a.sys in
  let name = mk_names all_svars in
  let is_loc sv = List.exists (same_sv sv) a.loc_bits in
  let relevant = concerns a cone in
  (* What gets printed *)
  let init_all = List.filter relevant a.init in
  let init_locs, init_rest =
    List.partition (is_location_literal a.loc_bits Numeral.zero) init_all
  in
  let init_location = location_of_literals a.loc_bits init_locs in
  let init_cs =
    match init_location with Some _ -> init_rest | None -> init_all
  in
  let always = List.filter relevant a.always in
  let keep_assigns l =
    List.filter (fun (sv, _) -> in_cone sv && not (is_loc sv)) l
  in
  (* The goal may be to stay away from a location *)
  let goal_location =
    match
      location_of_literals a.loc_bits
        (conjuncts (a.normal.nf (Term.mk_not goal)))
    with
    | Some i -> Some (`Not i)
    | None -> (
      match location_of_literals a.loc_bits (conjuncts goal) with
      | Some i -> Some (`At i)
      | None -> None)
  in
  let roots =
    init_cs @ always
    @ a.common.guards @ List.map snd (keep_assigns a.common.assigns)
    @ List.concat_map (fun t ->
        t.step.guards @ List.map snd (keep_assigns t.step.assigns))
        a.transitions
  in
  let defs, pp = mk_printer ~name ~threshold:4 roots in
  let buf = Buffer.create 4096 in
  let add fmt = Printf.bprintf buf fmt in
  let section title lines =
    if lines <> [] then (
      add "## %s\n\n" title ;
      List.iter (fun l -> add "%s\n" l) lines ;
      add "\n"
    )
  in
  (* Where a variable comes from, for a Lustre model *)
  let source_names =
    if InputSystem.is_lustre_input in_sys then
      try InputSystem.mk_state_var_to_lustre_name_map in_sys all_svars
      with _ -> StateVar.StateVarMap.empty
    else StateVar.StateVarMap.empty
  in
  let row sv =
    let source =
      match StateVar.StateVarMap.find_opt sv source_names with
      | Some s when s <> StateVar.name_of_state_var sv ->
        Printf.sprintf " (%s)" s
      | _ -> ""
    in
    let const = if StateVar.is_const sv then " (constant)" else "" in
    Format.asprintf "- %s : %a%s%s" (name sv)
      Type.pp_print_type (StateVar.type_of_state_var sv) const source
  in
  let shown = List.filter in_cone all_svars in
  let inputs, state = List.partition StateVar.is_input shown in
  section "State variables" (List.map row state) ;
  section "Inputs (arbitrary at each step, not part of the state)"
    (List.map row inputs) ;
  (* The locations in use *)
  let used =
    List.concat_map (fun t -> List.filter_map Fun.id [ t.src ; t.dst ])
      a.transitions
    @ (match init_location with Some i -> [ i ] | None -> [])
    @ (match goal_location with
       | Some (`Not i | `At i) -> [ i ]
       | None -> [])
    |> List.sort_uniq compare
  in
  let pp_location i =
    let lits =
      List.mapi (fun k b ->
        if i land (1 lsl k) <> 0 then name b
        else Printf.sprintf "(not %s)" (name b)) a.loc_bits
    in
    Printf.sprintf "%s := (and %s)" (location_name i) (String.concat " " lits)
  in
  section "Control locations" (List.map pp_location used) ;
  section "Abbreviations (x' is the next value of x)"
    (List.map (fun (n, b) -> n ^ " := " ^ b) defs) ;
  section "Initial states"
    ((match init_location with
      | Some i -> [ location_name i ]
      | None -> [])
     @ List.map pp init_cs) ;
  section "Every state satisfies"
    (List.map pp always
     @ List.filter_map (fun sv ->
         if in_cone sv then
           Some (Printf.sprintf
                   "%s is true in the initial state and false in all others"
                   (name sv))
         else None) a.first_flags) ;
  (* The variables whose next value a step says nothing of *)
  let primed_in c =
    VS.fold (fun v acc ->
      match next_state_var v with Some sv -> SVS.add sv acc | None -> acc)
      (a.vars c) SVS.empty
  in
  let constrained step =
    List.fold_left (fun acc g -> SVS.union acc (primed_in g))
      (SVS.union
         (SVS.of_list (List.map fst step.assigns))
         (SVS.of_list step.unchanged))
      step.guards
  in
  let defined =
    List.fold_left (fun acc c -> SVS.union acc (svars_of a c)) SVS.empty always
  in
  let free_vars step =
    let known =
      SVS.union (SVS.of_list a.first_flags)
        (SVS.union (constrained a.common)
           (SVS.union (constrained step) defined))
    in
    List.filter (fun sv ->
      not (is_loc sv) && not (StateVar.is_const sv) && not (SVS.mem sv known))
      state
  in
  let free_line step =
    match free_vars step with
    | [] -> []
    | l ->
      [ Printf.sprintf "free: %s" (String.concat " " (List.map name l)) ]
  in
  let is_known g = List.exists (Term.equal g) a.always in
  let step_lines step =
    (List.filter (fun g -> not (is_known g)) step.guards
     |> List.map (fun g -> "when " ^ pp g))
    @ List.map (fun (sv, e) -> Printf.sprintf "%s' = %s" (name sv) (pp e))
        (keep_assigns step.assigns)
  in
  section "At every step"
    (step_lines a.common
     @ (if a.transitions = [] then free_line a.common else [])) ;
  if a.transitions <> [] then (
    add "## Transitions (each step takes one whose conditions hold; \
         a variable not listed keeps its value)\n\n" ;
    List.iteri (fun i t ->
      ( match t.src, t.dst with
        | Some s, Some d ->
          add "T%d: %s -> %s\n" (i + 1) (location_name s) (location_name d)
        | _ -> add "T%d:\n" (i + 1) ) ;
      List.iter (fun l -> add "  %s\n" l) (step_lines t.step @ free_line t.step)
    ) a.transitions ;
    add "\n"
  ) ;
  let goal_text =
    match goal_location with
    | Some (`Not i) -> Printf.sprintf "(not %s)" (location_name i)
    | Some (`At i) -> location_name i
    | None -> standalone_text ~name goal
  in
  {
    text = Buffer.contents buf ;
    goal_text ;
    state_count = List.length state ;
    omitted_count =
      List.length
        (List.filter (fun sv ->
           not (in_cone sv) && not (StateVar.is_input sv)) all_svars) ;
  }

(* {1 Checking the normal form} *)

(* The term with the variables [vs] existentially quantified *)
let quantified vs t =
  let vs = VS.elements vs in
  if vs = [] then t
  else
    let fresh =
      List.map (fun v ->
        v, Var.mk_fresh_var
          (StateVar.type_of_state_var (Var.state_var_of_state_var_instance v)))
        vs
    in
    let t' =
      subst (List.map (fun (v, f) -> Term.mk_var v, Term.mk_var f) fresh) t
    in
    Term.mk_exists (List.map snd fresh) t'

type check_result = Equivalent | Different of string | Inconclusive of string

(* Ask a solver whether the system as understood is the system as it is.
   Eliminated inputs are existentially quantified on both sides. *)
let check a =
  let init', trans' = rebuilt a in
  let solver =
    SMTSolver.create_instance ~produce_models:false `None (Flags.Smt.solver ())
  in
  Fun.protect ~finally:(fun () -> SMTSolver.delete_instance solver)
    (fun () ->
      TransSys.define_and_declare_of_bounds a.sys
        (SMTSolver.define_fun solver)
        ~define_rec:(SMTSolver.define_funs_rec solver)
        (SMTSolver.declare_fun solver)
        (SMTSolver.declare_sort solver)
        Numeral.zero Numeral.one ;
      TransSys.assert_global_constraints a.sys (SMTSolver.assert_term solver) ;
      let differ what x y =
        let actlit = Actlit.fresh_actlit () in
        SMTSolver.declare_fun solver actlit ;
        let actlit = Actlit.term_of_actlit actlit in
        SMTSolver.assert_term solver
          (Term.mk_implies [ actlit ; Term.mk_not (Term.mk_eq [ x ; y ]) ]) ;
        match
          SMTSolver.check_sat_assuming solver (fun _ -> true) (fun _ -> false)
            [ actlit ]
        with
        | true -> Some (Different what)
        | false -> None
        | exception SMTSolver.Unknown -> Some (Inconclusive what)
      in
      let aux_in t = VS.inter a.aux (a.vars t) in
      match differ "initial states" a.orig_init init' with
      | Some r -> r
      | None -> (
        match
          differ "transition relation"
            (quantified (aux_in a.orig_trans) a.orig_trans)
            (quantified (aux_in trans') trans')
        with
        | Some r -> r
        | None -> Equivalent))
