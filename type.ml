open Ast
open Structure

(* prettyprinter *)
let rec print_type (t : ptype) : string =
  match t with
  | Var_t x -> x
  | Arr (t1, t2) -> "(" ^ print_type t1 ^ " -> " ^ print_type t2 ^ ")"
  | Nat -> "Nat"  
  | N -> "N"
  | List_t t -> "[" ^ print_type t ^ "]"
  | Forall (vars, t) ->
      let vars_str = String.concat ", " vars in
      "∀(" ^ vars_str ^ ").(" ^ print_type t ^ ")"
  | Unit_t -> "Unit"
  | Ref_t t -> "Ref(" ^ print_type t ^ ")"

(* Fonction pour afficher une équation *)
let print_equation (t1, t2) : string =
  print_type t1 ^ " = " ^ print_type t2

(* Fonction pour afficher un système d'équations *)
let print_equa (eqs : equa) : string =
  String.concat "\n" (List.map print_equation eqs)

let compteur_var_t : int ref = ref 0

let nouvelle_var_t () : string = 
  compteur_var_t := !compteur_var_t + 1;
  "T" ^ (string_of_int !compteur_var_t)

(* Recherche d'une variable dans un environnement *)
let rec cherche_type (v : string) (e : env) : ptype option = 
  match e with
  | [] -> raise (VariableNotFound ("Variable " ^ v ^ " not found in environment"))
  | (x, t) :: es ->
      if x = v then Some t
      else cherche_type v es
  
(* Fonction pour extraire les variables libres d'un type *) 
let rec free_vars_t (t : ptype) : string list =
  match t with
  | Var_t x -> [x]
  | Arr (t1, t2) -> List.append (free_vars_t t1) (free_vars_t t2)
  | Nat -> []
  | N -> []
  | List_t t -> free_vars_t t
  | Forall (vars, t) -> 
      let free_in_t = free_vars_t t in
      List.filter (fun v -> not (List.mem v vars)) free_in_t
  | Unit_t -> []
  | Ref_t t -> free_vars_t t

(* Généralisation d'un type *)
let generalize (env : env) (ty : ptype) : ptype =
  let type_vars = free_vars_t ty in
  let free_vars_in_env = List.flatten (List.map (fun (_, t) -> free_vars_t t) env) in
  let free_vars = List.filter (fun x -> not (List.mem x free_vars_in_env)) type_vars in
  Forall (free_vars, ty)

(* occur check *)
let rec occur_check (var: string) (typ: ptype) : bool =
  match typ with
  | Var_t x -> x = var
  | Arr (t1, t2) -> occur_check var t1 || occur_check var t2
  | Nat -> false
  | N-> false
  | List_t t -> occur_check var t
  | Forall (vars, t) -> not (List.mem var vars) && occur_check var t
  | Unit_t -> false
  | Ref_t t -> occur_check var t
  
(* Substitution d'une variable de type par un autre type dans un type donné *)
let rec subst_type (tv : string) (replacement : ptype) (t : ptype) : ptype =
  match t with
  | Var_t v -> if v = tv then replacement else t
  | Arr (t1, t2) -> Arr (subst_type tv replacement t1, subst_type tv replacement t2)
  | Nat -> Nat
  | N -> N 
  | List_t t -> List_t (subst_type tv replacement t)
  | Forall (vars, t) -> 
      if List.mem tv vars then t
      else Forall (vars, subst_type tv replacement t)
  | Unit_t -> Unit_t
  | Ref_t t -> Ref_t (subst_type tv replacement t)

(* Substitution d'une variable de type dans tout un système d'équations *)
let rec subst_in_system (tv : string) (replacement : ptype) (equations : equa) : equa =
  List.map (fun (t1, t2) -> (subst_type tv replacement t1, subst_type tv replacement t2)) equations

(* Fonction d'unification pour une étape *)
let rec unification_step (eqs : equa) (sub_env : env): (equa * env) =
  match eqs with
  | [] -> ([], sub_env)
  | (t1, t2) :: rest ->
      if t1 = t2 then unification_step rest sub_env
      else match t1, t2 with
        | Var_t x, _ when not (occur_check x t2) ->
            let new_eqs = subst_in_system x t2 rest in
            let new_sub_env = (x, t2) :: List.map (fun (v, t) -> (v, subst_type x t2 t)) sub_env in
            unification_step new_eqs new_sub_env
        | _, Var_t x when not (occur_check x t1) ->
            let new_eqs = subst_in_system x t1 rest in
            let new_sub_env = (x, t1) :: List.map (fun (v, t) -> (v, subst_type x t1 t)) sub_env in
            unification_step new_eqs new_sub_env
        | Arr (tga, tgr), Arr (tda, tdr) ->
            unification_step ((tga, tda) :: (tgr, tdr) :: rest) sub_env
        | List_t t1', List_t t2' ->
            unification_step ((t1', t2') :: rest) sub_env
        | Forall (vars, t1'), t2 ->
            let t1' = barendregtisation t1' [] in
            unification_step ((ouvrir t1', t2) :: rest) sub_env
        | t1, Forall (vars, t2') ->
            let t2' = barendregtisation t2' [] in
            unification_step ((t1, ouvrir t2') :: rest) sub_env
        | Unit_t, Unit_t -> unification_step rest sub_env
        | Ref_t t1, Ref_t t2 ->
            unification_step ((t1, t2) :: rest) sub_env
        | _ -> raise (TypeInferenceFailed "Unification failed: incompatible types")

(* Fonction auxiliaire pour la barendregtisation *)
and barendregtisation (t : ptype) (env : (string * string) list) : ptype =
  match t with
  | Var_t v -> (match List.assoc_opt v env with Some nv -> Var_t nv | None -> Var_t v)
  | Arr (t1, t2) -> Arr (barendregtisation t1 env, barendregtisation t2 env)
  | List_t t -> List_t (barendregtisation t env)
  | Forall (vars, t') ->
      let bindings = List.map (fun v -> (v, nouvelle_var_t ())) vars in
      let env' = bindings @ env in
      Forall (List.map snd bindings, barendregtisation t' env')
  | _ -> t

(* Fonction d'ouverture des types *)
and ouvrir (t : ptype) : ptype =
  match t with
  | Forall (vars, t') -> List.fold_left (fun acc v -> subst_type v (Var_t (nouvelle_var_t ())) acc) t' vars
  | _ -> t

exception Timeout

let rec resolve_with_timeout (equations : equa) (sub_env : env) (max_steps : int): (equa * env) option =
  if max_steps <= 0 then raise Timeout
  else
    match equations with
    | [] -> Some (equations, sub_env)
    | _ -> 
          try
            let (new_eqs, new_sub_env) = unification_step equations sub_env
            in resolve_with_timeout new_eqs new_sub_env (max_steps - 1)
          with Failure msg -> raise (OutOfReductionSteps msg)

let rec apply_sub_env (t : ptype) (sub_env : env) : ptype =
  match t with
  | Var_t x -> 
      (try 
         let t' = List.assoc x sub_env in
         apply_sub_env t' sub_env
       with Not_found -> Var_t x)
  | Arr (t1, t2) -> Arr (apply_sub_env t1 sub_env, apply_sub_env t2 sub_env)
  | Nat -> Nat
(* let infer_type (term : pterm) (env : env) (timeout : int)  *)

(* Fonction qui génère des équations de typage à partir d'un terme *)
let rec genere_equa (te : pterm) (ty : ptype) (env : env) : equa =
  match te with
  | Var v -> (
      match cherche_type v env with
      | Some ty_var -> [(ty_var, ty)]
      | None -> raise (VariableNotFound ("Variable " ^ v ^ " not found in environment"))
    )
  | App (t1, t2) ->
      let ta = Var_t (nouvelle_var_t ()) in
      let equa_t1 = genere_equa t1 (Arr (ta, ty)) env in
      let equa_t2 = genere_equa t2 ta env in
      equa_t1 @ equa_t2
  | Abs (x, t) ->
      let ta = Var_t (nouvelle_var_t ()) in  
      let tr = Var_t (nouvelle_var_t ()) in  
      let equa_abs = [(ty, Arr (ta, tr))] in
      let equa_t = genere_equa t tr ((x, ta) :: env) in
      equa_abs @ equa_t
  | Int _ -> [(ty, N)]
  | Nil -> let ta = Var_t (nouvelle_var_t ()) in
    [(ty, List_t ta)]
    
  | Add (t1, t2) | Sub (t1, t2) ->
      (ty, N) :: (genere_equa t1 N env @ genere_equa t2 N env)
  | Head t ->
      let ta = Var_t (nouvelle_var_t ()) in
      let equa_t = genere_equa t (List_t ta) env in
      (ty, ta) :: equa_t
  | List lst ->
      let ta = Var_t (nouvelle_var_t ()) in
      (match lst with
       | Empty -> [(ty, List_t ta)]
       | Cons (hd, tl) ->
           let equa_hd = genere_equa hd ta env in
           let equa_tl = genere_equa (List tl) (List_t ta) env in
           (ty, List_t ta) :: equa_hd @ equa_tl)
  | Tail t ->
      let ta = Var_t (nouvelle_var_t ()) in
      let equa_t = genere_equa t (List_t ta) env in
      (ty, List_t ta) :: equa_t
  | IfZero (cond, cons, alt) ->
      let equa_cond = genere_equa cond N env in
      let equa_cons = genere_equa cons ty env in
      let equa_alt = genere_equa alt ty env in
      equa_cond @ equa_cons @ equa_alt
  | IfEmpty (cond, cons, alt) ->
      let ta = Var_t (nouvelle_var_t ()) in
      let equa_cond = genere_equa cond (List_t ta) env in
      let equa_cons = genere_equa cons ty env in
      let equa_alt = genere_equa alt ty env in
      equa_cond @ equa_cons @ equa_alt
  | Fix (Abs (phi, m)) ->
      let t_input = Var_t (nouvelle_var_t ()) in
      let t_output = Var_t (nouvelle_var_t ()) in
      let env_extended = (phi, Arr (t_input, t_output)) :: env in
      let equa_m = genere_equa m (Arr (t_input, t_output)) env_extended in
      (ty, Arr (t_input, t_output)) :: equa_m
      | Let (x, e1, e2) ->  
  let inferredType, _ = infer_type env e1 in
      (match inferredType with
      | Some ty' -> 
          let gen = generalize env ty' in
          let env2 = (x, gen) :: env in
          genere_equa e2 ty env2
      | None -> raise (TypeInferenceFailed "Type inference failed"))
  | Ref e -> 
      let ty_cbl = Var_t (nouvelle_var_t ()) in   
      (ty, Ref_t ty_cbl) :: (genere_equa e ty_cbl env)
  | Unit -> [(ty, Unit_t)]
  | Deref e -> 
      let ty_cbl = Var_t (nouvelle_var_t ()) in
      (ty, ty_cbl) :: (genere_equa e ty_cbl env)
  | Adresse _ -> [(ty, N)]
  | Assign (t1, t2) ->
      let ty_cbl = Var_t (nouvelle_var_t ()) in
      (ty, Unit_t) :: (genere_equa t1 (Ref_t ty_cbl) env) @ (genere_equa t2 ty_cbl env)
  | _ -> raise (UnsupportedTerm "Unsupported term in genere_equa")

and infer_type(env: env) (term : pterm) : (ptype option * equa) =
  let target_type = Var_t (nouvelle_var_t ()) in
  let equations = genere_equa term target_type env in
  match resolve_with_timeout equations [] 500 with
  | Some (_, substitutions) -> 
      let inferred_type = apply_sub_env target_type substitutions in
      (Some inferred_type, equations)  
  | None -> (None, equations) 