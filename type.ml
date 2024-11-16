(* import Ast *)
open Ast
open Structure

(* prettyprinter *)
let rec print_type (t : ptype ) : string =
  match t with
  Var_t x -> x
  | Arr (t1 , t2) -> "(" ^ ( print_type t1) ^" -> "^ ( print_type t2) ^")"
  | Nat -> "nat"


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
  
(* Fonction qui génère des équations de typage à partir d'un terme *)
let rec genere_equa (te : pterm ) (ty : ptype ) (e : env) : equa =
  match te with
  (* Si c'est une variable, on cherche son type dans l'environnement *)
  | Var v -> (
      match cherche_type v e with
      | Some ty_var -> [(ty_var, ty)]  (* On génère l'équation entre le type de la variable et le type cible *)
      | None -> failwith ("Variable " ^ v ^ " not found in environment")
    )
  
  (* Si c'est une application t1 t2 *)
  | App (t1, t2) ->
      let ta = Var_t (nouvelle_var_t ()) in  (* On génère un type frais pour l'argument *)
      (* On génère les équations pour t1 avec le type de la forme "ta -> ty" *)
      let equa_t1 = genere_equa t1 (Arr (ta, ty)) e in
      (* On génère les équations pour t2 avec le type "ta" *)
      let equa_t2 = genere_equa t2 ta e in
      equa_t1 @ equa_t2  (* On retourne la combinaison des équations *)

  (* Si c'est une abstraction λx.t *)
  | Abs (x, t) ->
      let ta = Var_t (nouvelle_var_t ()) in  
      let tr = Var_t (nouvelle_var_t ()) in  
      (* On génère une équation pour la flèche entre le type de l'argument et le type de résultat *)
      let equa_abs = [(ty, Arr (ta, tr))] in
      (* On génère récursivement les équations pour le corps de l'abstraction *)
      let equa_t = genere_equa t tr ((x, ta) :: e) in
      equa_abs @ equa_t  (* Combinaison des équations *)

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
