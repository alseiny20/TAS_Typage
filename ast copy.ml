type pterm = 
  | Var of string
  | App of pterm * pterm
  | Abs of string * pterm

let rec print_term (t : pterm ) : string =
  match t with
  | Var x -> x
  | App (t1, t2) -> "(" ^ (print_term t1) ^ " " ^ (print_term t2) ^ ")"
  | Abs (x, t) -> "(fun " ^ x ^ " -> " ^ (print_term t) ^ ")"

let compteur_var : int ref = ref 0

let nouvelle_var () : string =
  compteur_var := !compteur_var + 1;
  "X" ^ (string_of_int !compteur_var)

(* 3 alpha-conversion *)
let rec alphaconv (t : pterm) (annuaire : (string * string) list) : pterm =
  match t with
  | Var x ->
      (match List.assoc_opt x annuaire with
       | Some new_name -> Var new_name
       | None -> Var x)
  | App (t1, t2) ->
      App (alphaconv t1 annuaire, alphaconv t2 annuaire)
  | Abs (x, t1) ->
      let new_var = nouvelle_var () in
      let new_annuaire = (x, new_var) :: annuaire in
      Abs (new_var, alphaconv t1 new_annuaire)

(* 4 fonction de substitution *)
let rec free_vars (t : pterm) : string list =
  match t with
  | Var x -> [x]
  | App (t1, t2) -> free_vars t1 @ free_vars t2
  | Abs (x, t1) -> List.filter (fun y -> y <> x) (free_vars t1)

let rec substitution (x : string) (n : pterm) (t : pterm) : pterm =
  match t with
  | Var y -> if y = x then n else t
  | App (t1, t2) -> App (substitution x n t1, substitution x n t2)
  | Abs (y, t1) ->
      if y = x then Abs (y, t1)
      else if List.mem y (free_vars n) then
        let new_var = nouvelle_var () in
        let renamed_body = substitution y (Var new_var) t1 in
        Abs (new_var, substitution x n renamed_body)
      else Abs (y, substitution x n t1)

(* Fonction de vérification de si un terme est une value *)
let is_value (t : pterm) : bool =
  match t with
  | Var _ -> true
  | Abs (_, _) -> true
  | _ -> false

(* Fonction de simplification avec limite d'étapes *)
let rec simplify_term_with_limit (t : pterm) (limit : int) : pterm =
  if limit <= 0 then
    (* Si la limite est atteinte, renvoyer simplement le terme sans lever d'exception *)
    t
  else
    match t with
    | App (Abs (x, t1), t2) -> simplify_term_with_limit (substitution x t2 t1) (limit - 1)
    | App (t1, t2) -> App (simplify_term_with_limit t1 (limit - 1), simplify_term_with_limit t2 (limit - 1))
    | Abs (x, t1) -> Abs (x, simplify_term_with_limit t1 (limit - 1))
    | Var _ -> t

(* Fonction de réduction Call-by-Value avec limitation d'étapes *)
let rec ltr_ctb_step_with_limit (t : pterm) (limit : int) : pterm option =
  if limit <= 0 then None else
  match t with
  | Var _ -> None
  | Abs (x, t1) ->
      (match ltr_ctb_step_with_limit t1 (limit - 1) with
       | Some t1' -> Some (Abs (x, simplify_term_with_limit t1' limit))
       | None -> None)
  | App (Abs (x, t1), v2) when is_value v2 ->
      Some (simplify_term_with_limit (substitution x v2 t1) limit)
  | App (t1, t2) ->
      (match ltr_ctb_step_with_limit t1 (limit - 1) with
       | Some t1' -> Some (App (simplify_term_with_limit t1' limit, t2))
       | None ->
           (match ltr_ctb_step_with_limit t2 (limit - 1) with
            | Some t2' -> Some (App (t1, simplify_term_with_limit t2' limit))
            | None -> None))

(* Fonction de réduction normale avec limitation d'étapes *)
let rec ltr_cbv_norm_with_timeout (t : pterm) (max_steps : int) : pterm =
  let rec normalize_with_limit (term : pterm) (current_limit : int) : pterm option =
    if current_limit <= 0 then (
      print_endline ("Ce terme ne converse pas en " ^ string_of_int max_steps ^ " reductions");
      Some term  (* Retourne le terme non réduit sans lever d'erreur *)
    ) else
      match ltr_ctb_step_with_limit term current_limit with
      | Some next_term -> normalize_with_limit next_term (current_limit - 1)
      | None -> Some term
  in
  match normalize_with_limit t max_steps with
  | Some result -> result
  | None -> t
