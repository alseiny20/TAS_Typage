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
  | Forall (x, t) -> "∀" ^ x ^ ".(" ^ print_type t ^ ")"

(* Fonction pour afficher une équation *)
let print_equation (t1, t2) : string =
  print_type t1 ^ " = " ^ print_type t2

(* Fonction pour afficher un système d'équations *)
let print_equa (eqs : equa) : string =
  String.concat "\n" (List.map print_equation eqs)
  let compteur_var_t : int ref = ref 0

  let nouvelle_var_t () : string = compteur_var_t := ! compteur_var_t + 1;
    "T"^( string_of_int ! compteur_var_t )

  (* recherche dune variable dans un environment *)
  let rec cherche_type (v : string ) (e : env) : ptype option = 
    match e with
    [] -> None
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
  | Forall (var, t) -> List.filter (fun v -> v <> var) (free_vars_t t)

(* Généralisation d'un type *)
let generalize (env : env) (ty : ptype) : ptype =
  let type_vars = free_vars_t ty in
  let free_vars_in_env = List.flatten (List.map (fun (_, t) -> free_vars_t t) env) in
  let free_vars = List.filter (fun x -> not (List.mem x free_vars_in_env)) type_vars in
  List.fold_right (fun x acc -> Forall (x, acc)) free_vars ty

(* Fonction qui génère des équations de typage à partir d'un terme *)
let rec generate_equa (te : pterm) (ty : ptype) (env : env) : (equa * env) =
  match te with
  | Var v -> (
      match cherche_type v env with
      | Some ty_var -> ([(ty_var, ty)], env)
      | None -> failwith ("Variable " ^ v ^ " not found in environment")
    )
  | App (t1, t2) ->
      let ta = Var_t (nouvelle_var_t ()) in
      let (eqs_t1, env') = generate_equa t1 (Arr (ta, ty)) env in
      let (eqs_t2, env'') = generate_equa t2 ta env' in
      (eqs_t1 @ eqs_t2, env'')
  | Abs (x, t) ->
      let ta = Var_t (nouvelle_var_t ()) in  
      let tr = Var_t (nouvelle_var_t ()) in  
      let env' = (x, ta) :: env in
      let (eqs_t, env'') = generate_equa t tr env' in
      ((ty, Arr (ta, tr)) :: eqs_t, env'')
  | Int _ -> 
      ([(ty, N)], env)
  (* | List l -> (
      let ta = Var_t (nouvelle_var_t ()) in
      let list_type = List_t ta in
      match l with
      | Empty -> ([(ty, list_type)], env)
      | Cons (hd, tl) -> 
          let (eqs_hd, env') = generate_equa hd ta env in
          let (eqs_tl, env'') = generate_equa tl list_type env' in
          ((ty, list_type) :: eqs_hd @ eqs_tl, env'')
    ) *)
  | Head t -> 
      let ta = Var_t (nouvelle_var_t ()) in
      let (eqs_t, env') = generate_equa t (List_t ta) env in 
      ((ty, ta) :: eqs_t, env')  
  | Tail t -> 
      let ta = Var_t (nouvelle_var_t ()) in
      let (eqs_t, env') = generate_equa t (List_t ta) env in 
      ((ty, List_t ta) :: eqs_t, env')  
  | IfZero (cond, cons, alt) -> 
      let (eqs_cond, env') = generate_equa cond N env in 
      let (eqs_cons, env'') = generate_equa cons ty env' in  
      let (eqs_alt, env''') = generate_equa alt ty env'' in    
      ((eqs_cond @ eqs_cons @ eqs_alt), env''')
  | IfEmpty (cond, cons, alt) -> 
      let ta = Var_t (nouvelle_var_t ()) in
      let (eqs_cond, env') = generate_equa cond (List_t ta) env in  
      let (eqs_cons, env'') = generate_equa cons ty env' in  
      let (eqs_alt, env''') = generate_equa alt ty env'' in   
      ((eqs_cond @ eqs_cons @ eqs_alt), env''')
  (* | Let (x, e1, e2) ->  *)
   (* let inferredType, _ = infer_type env e1 in
    match inferredType with
    | Some ty' -> 
        let gen = generalize env ty' in
        let env2 = (x, gen) :: env in
        generate_equa e2 ty env2
    | None -> failwith "Type inference failed" *)
  (* Fix *)
  | Fix (Abs (phi, m)) ->
      let t_input = Var_t (nouvelle_var_t ()) in
      let t_output = Var_t (nouvelle_var_t ()) in
      let env_extended = (phi, Arr (t_input, t_output)) :: env in
      let (eqs_m, updated_env) = generate_equa m (Arr (t_input, t_output)) env_extended in
      ((ty, Arr (t_input, t_output)) :: eqs_m, updated_env)
      
  | _ -> failwith "Unsupported term in generate_equa"


(* occur check *)
let rec occur_check (var: string) (typ: ptype) : bool =
  match typ with
  | Var_t x -> x = var
  | Arr (t1, t2) -> occur_check var t1 || occur_check var t2
  | Nat -> false

(* Substitution d'une variable de type par un autre type dans un type donné *)
let rec subst_type (tv : string) (replacement : ptype) (t : ptype) : ptype =
  match t with
  | Var_t v -> if v = tv then replacement else t  (* Si on trouve la variable tv, on la remplace *)
  | Arr (t1, t2) -> Arr (subst_type tv replacement t1, subst_type tv replacement t2)  (* Appliquer en profondeur *)
  | Nat -> Nat (* on fais rien ici *)


(* Substitution d'une variable de type dans tout un système d'équations *)
let rec subst_in_system (tv : string) (replacement : ptype) (equations : equa) : equa =
  List.map (fun (t1, t2) -> (subst_type tv replacement  t1, subst_type tv replacement t2)) equations

(* Fonction d'unification pour une étape *)
let rec unification_step (eqs : equa) (sub_env : env): (equa * env) =
  match eqs with
  | [] -> ([], sub_env)  (* Si le système est vide, il est déjà unifié *)
  
  | (t1, t2) :: rest ->
      (* Cas 1: Si les deux types sont égaux, on supprime l'équation *)
      if t1 = t2 then
        unification_step rest sub_env

      (* Cas 2: Si t1 est une variable de type et n'apparaît pas dans t2 *)
      else (match t1, t2 with
        | Var_t x, _ when not (occur_check x t2) ->
            (* Substitution de la variable de type dans tout le système *)
            let new_eqs = subst_in_system x t2 rest in
            let new_sub_env = (x, t2) :: (List.map (fun (v, t) -> (v, subst_type x t2 t)) sub_env) in
            unification_step new_eqs new_sub_env
        
        (* Cas 2 inverse: Si t2 est une variable de type et n'apparaît pas dans t1 *)
        | _, Var_t x when not (occur_check x t1) ->
            (* Substitution de la variable de type dans tout le système *)
            let new_eqs = subst_in_system x t1 rest in
            let new_sub_env = (x, t1) :: (List.map (fun (v, t) -> (v, subst_type x t1 t)) sub_env) in
            unification_step new_eqs new_sub_env

        (* Cas 3: Si les deux types sont des flèches *)
        | Arr (tga, tgr), Arr (tda, tdr) ->
            (* On ajoute les équations pour les parties gauche et droite *)
            unification_step ((tga, tda) :: (tgr, tdr) :: rest) sub_env

        (* Sinon, on échoue *)
        | _ ->   failwith ("Unification échouée: types incompatibles")
      )

exception Timeout

let rec resolve_with_timeout (equations : equa) (sub_env : env) (max_steps : int): (equa * env) option =
  if max_steps <= 0 then raise Timeout (* steps max atteinte *)
  else
    match equations with
    | [] -> Some (equations, sub_env)  (* tout a pu avoir un type dans les temps *)
    | _ -> 
          try
            let (new_eqs, new_sub_env) = unification_step equations sub_env
            in resolve_with_timeout new_eqs new_sub_env (max_steps - 1)
          with Failure _ -> None 


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

let infer_type(env: env) (term : pterm) : (ptype option * equa) =
  let target_type = Var_t (nouvelle_var_t ()) in
  let equations = genere_equa term target_type env in
  match resolve_with_timeout equations [] 500 with
  | Some (_, substitutions) -> 
      let inferred_type = apply_sub_env target_type substitutions in
      (Some inferred_type, equations)  
  | None -> (None, equations) 

