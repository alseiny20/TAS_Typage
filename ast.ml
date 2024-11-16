open Structure

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
      (* change le nom de la variable et je rajoute dans l'ennuaire la modification opperer  *)
      Abs (new_var, alphaconv t1 ((x, new_var) :: annuaire))

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
      if y = x then Abs (y, t1) (* on fais rien car cette variable la est djea liée ici *)
      else if List.mem y (free_vars n) then
        let new_var = nouvelle_var () in
        let renamed_body = substitution y (Var new_var) t1 in
        Abs (new_var, substitution x n renamed_body)
      else Abs (y, substitution x n t1)

(* let rec ltr_ctb_step (t : pterm) : pterm option =
  match t with
  | Var _ -> None
  | Abs (x, t1) ->
      (* On essaie de réduire le corps de l'abstraction *)
      (match ltr_ctb_step t1 with
        | Some t1' -> Some (Abs (x, t1'))
        | None -> None)  (* Si le corps est déjà en forme normale, on ne fait rien *)
  | App (Abs (x, t1), v2) when is_value v2 ->
      (* Si le terme est de la forme (λx.t1) v2 avec v2 une valeur, on applique la substitution *)
      Some (substitution x v2 t1)
  | App (t1, t2) ->
      (* On essaie d'abord de réduire t1 *)
      (match ltr_ctb_step t1 with
        | Some t1' -> Some (App (t1', t2))
        | None ->
            (* Si t1 est déjà une valeur, on essaie de réduire t2 *)
            (match ltr_ctb_step t2 with
            | Some t2' -> Some (App (t1, t2'))
            | None -> None)) *)


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

(* Fonction pour vérifier si un terme est une valeur *)
and is_value (t : pterm) : bool =
match t with
| Var _ -> true
| App (Var x, t2) -> is_value t2
| Abs (_, _) -> true
| _ -> false

(* Fonction de réduction Call-by-Value avec limitation d'étapes *)
let rec ltr_ctb_step_with_limit (t : pterm) : pterm option =
  match t with
  | Var _ -> None
  | Abs (x, t1) ->
      (match ltr_ctb_step_with_limit t1 with
       | Some t1' -> Some (Abs (x, simplify_term_with_limit t1' 4))
       | None -> None)
  | App (Abs (x, t1), v2) when is_value v2 ->
      Some (simplify_term_with_limit (substitution x v2 t1) 4)
  | App (t1, t2) ->
      (match ltr_ctb_step_with_limit t1 with
       | Some t1' -> Some (App (simplify_term_with_limit t1' 4, t2))
       | None ->
           (match ltr_ctb_step_with_limit t2 with
            | Some t2' -> Some (App (t1, simplify_term_with_limit t2' 4))
            | None -> None))


let rec ltr_cbv_norm (t : pterm) : pterm =
  match ltr_ctb_step_with_limit t with
  | Some t' -> ltr_cbv_norm t'  (* On continue à réduire le terme *)
  | None -> t  (* Si aucune réduction n'est possible, on aret en renvoyan le terme  *)
            
(* Fonction de réduction normale avec limitation d'étapes *)
let rec ltr_cbv_norm_with_timeout (t : pterm) (max_steps : int) : pterm =
  let rec normalize_with_limit (term : pterm) (current_limit : int) : pterm option =
    if current_limit <= 0 then (
      print_endline ("Ce terme ne converse pas en " ^ string_of_int max_steps ^ " reductions");
      Some term  (* Retourne le terme non réduit sans lever d'erreur *)
    ) else
      match ltr_ctb_step_with_limit term with
      | Some next_term -> normalize_with_limit next_term (current_limit - 1)
      | None -> Some term
  in
  match normalize_with_limit t max_steps with
  | Some result -> result
  | None -> t


(* let term = App (
              Abs ("x", App (Abs ("y", Var "y"), Var "x")),  (* λx. (λy. y) x *)
              App (Abs ("z", App (Var "z", Var "z")), Abs ("z", Var "z"))
          )

let normal_term = ltr_cbv_norm term

let () =
  print_endline (print_term normal_term) *)