open Structure

let rec print_term (t : pterm) : string =
  match t with
  | Var x -> x
  | App (t1, t2) -> "(" ^ (print_term t1) ^ " " ^ (print_term t2) ^ ")"
  | Abs (x, t) -> "(fun " ^ x ^ " -> " ^ (print_term t) ^ ")"
  | Int n -> string_of_int n
  | Nil -> "Nil"
  | List l -> print_term_list l
  | Add (t1, t2) -> "(" ^ (print_term t1) ^ " + " ^ (print_term t2) ^ ")"
  | Sub (t1, t2) -> "(" ^ (print_term t1) ^ " - " ^ (print_term t2) ^ ")"
  | Cons (head, tail) -> "(cons " ^ (print_term head) ^ " " ^ (print_term tail) ^ ")"
  | Head t -> "(head " ^ (print_term t) ^ ")"
  | Tail t -> "(tail " ^ (print_term t) ^ ")"
  | IfZero (t1, t2, t3) -> "(if zero " ^ (print_term t1) ^ " then " ^ (print_term t2) ^ " else " ^ (print_term t3) ^ ")"
  | IfEmpty (t1, t2, t3) -> "(if empty " ^ (print_term t1) ^ " then " ^ (print_term t2) ^ " else " ^ (print_term t3) ^ ")"
  | Fix t -> "(fix " ^ (print_term t) ^ ")"
  | Let (x, t1, t2) -> "(let " ^ x ^ " = " ^ (print_term t1) ^ " in " ^ (print_term t2) ^ ")"
  and print_term_list (l : pterm listStand) : string =
    match l with
      Empty -> ""
      | Cons (t, Empty) -> print_term t
      | Cons (t, l) -> (print_term t) ^ "; " ^ (print_term_list l)
      
let compteur_var : int ref = ref 0

let nouvelle_var () : string =
  compteur_var := !compteur_var + 1;
  "X" ^ (string_of_int !compteur_var)

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
        Abs (new_var, alphaconv t1 ((x, new_var) :: annuaire))
    | Int _ -> t
    | Add (t1, t2) -> Add (alphaconv t1 annuaire, alphaconv t2 annuaire)
    | Sub (t1, t2) -> Sub (alphaconv t1 annuaire, alphaconv t2 annuaire)
    | Cons (t1, t2) -> Cons (alphaconv t1 annuaire, alphaconv t2 annuaire)
    | Nil -> Nil
    | List l -> List (alphaconv_list l annuaire)
    | Head t -> Head (alphaconv t annuaire)
    | Tail t -> Tail (alphaconv t annuaire)
    | IfZero (t1, t2, t3) -> IfZero (alphaconv t1 annuaire, alphaconv t2 annuaire, alphaconv t3 annuaire)
    | IfEmpty (t1, t2, t3) -> IfEmpty (alphaconv t1 annuaire, alphaconv t2 annuaire, alphaconv t3 annuaire)
    | Fix t -> Fix (alphaconv t annuaire)
    | Let (x, t1, t2) ->
        let new_var = nouvelle_var () in
        Let (new_var, alphaconv t1 annuaire, alphaconv t2 ((x, new_var) :: annuaire))
  
  and alphaconv_list (lst : pterm listStand) (annuaire : (string * string) list) : pterm listStand =
    match lst with
    | Empty -> Empty
    | Cons (hd, tail) ->
        Cons (alphaconv hd annuaire, alphaconv_list tail annuaire)

(* 4 fonction de substitution *)
let rec free_vars (t : pterm) : string list =
  match t with
  | Var x -> [x]
  | Abs (x, body) -> List.filter (fun v -> v <> x) (free_vars body)
  | App (t1, t2) -> free_vars t1 @ free_vars t2
  | Int _ -> []
  | Nil -> []
  | List l -> free_vars_list l
  | Add (t1, t2) -> free_vars t1 @ free_vars t2
  | Sub (t1, t2) -> free_vars t1 @ free_vars t2
  | Cons (head, tail) -> free_vars head @ free_vars tail
  | Head t -> free_vars t
  | Tail t -> free_vars t
  | IfZero (t1, t2, t3) -> free_vars t1 @ free_vars t2 @ free_vars t3
  | IfEmpty (t1, t2, t3) -> free_vars t1 @ free_vars t2 @ free_vars t3
  | Fix (Abs (f, body)) -> List.filter (fun v -> v <> f) (free_vars body)
  | Let (x, t1, t2) -> free_vars t1 @ List.filter (fun v -> v <> x) (free_vars t2)
  and free_vars_list (l: pterm listStand) : string list =
    match l with 
    |Empty -> []
    |Cons (head,tail)-> (free_vars head) @ (free_vars_list tail) 


(* 5 fonction de substitution *)
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
  | Int _ -> t
  | Nil -> Nil
  | List l -> List (substitution_list x n l)
  | Head t -> Head (substitution x n t)
  | Add (t1, t2) -> Add (substitution x n t1, substitution x n t2)
  | Sub (t1, t2) -> Sub (substitution x n t1, substitution x n t2)
  | Cons (t1, t2) -> Cons (substitution x n t1, substitution x n t2)
  | Head t -> Head (substitution x n t)
  | Tail t -> Tail (substitution x n t)
  | IfZero (t1, t2, t3) -> IfZero (substitution x n t1, substitution x n t2, substitution x n t3)
  | IfEmpty (t1, t2, t3) -> IfEmpty (substitution x n t1, substitution x n t2, substitution x n t3)
  | Fix (t) -> Fix (substitution x n t)
  |  Let (y, e1, e2) ->
      let e1' = substitution x n e1 in
      if y = x then
        Let (y, e1', e2) 
      else
        Let (y, e1', substitution x n e2)
  and substitution_list (a : string) (b : pterm) (l : pterm listStand) = 
    match l with 
    | Empty -> Empty
    | Cons (head, tail) -> Cons (substitution a b head,substitution_list a b tail)
        
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
    t (* Si la limite est atteinte, retourner le terme tel quel *)
  else
    match t with
    | App (Abs (x, t1), t2) ->
        simplify_term_with_limit (substitution x t2 t1) (limit - 1)
    | App (t1, t2) ->
        App (simplify_term_with_limit t1 (limit - 1), simplify_term_with_limit t2 (limit - 1))
    | Abs (x, t1) ->
        Abs (x, simplify_term_with_limit t1 (limit - 1))
    | Add (Int n1, Int n2) ->
        Int (n1 + n2)
    | Add (t1, t2) ->
        Add (simplify_term_with_limit t1 (limit - 1), simplify_term_with_limit t2 (limit - 1))
    | Sub (Int n1, Int n2) ->
        Int (n1 - n2)
    | Sub (t1, t2) ->
        Sub (simplify_term_with_limit t1 (limit - 1), simplify_term_with_limit t2 (limit - 1))
    | Cons (t1, t2) ->
        Cons (simplify_term_with_limit t1 (limit - 1), simplify_term_with_limit t2 (limit - 1))
    | List l ->
        List (simplify_list_with_limit l (limit - 1))
    | Let (x, t1, t2) when is_value t1 ->
        simplify_term_with_limit (substitution x t1 t2) (limit - 1)
    | Let (x, t1, t2) ->
        Let (x, simplify_term_with_limit t1 (limit - 1), simplify_term_with_limit t2 (limit - 1))
    | Head (List (Cons (t1, _))) ->
        simplify_term_with_limit t1 (limit - 1)
    | Tail (List (Cons (_, t2))) ->
        simplify_term_with_limit (List t2) (limit - 1)
    | IfZero (Int 0, t2, _) ->
        simplify_term_with_limit t2 (limit - 1)
    | IfZero (Int _, _, t3) ->
        simplify_term_with_limit t3 (limit - 1)
    | IfZero (t1, t2, t3) ->
        IfZero (simplify_term_with_limit t1 (limit - 1), t2, t3)
    | _ -> t

and simplify_list_with_limit (l : pterm listStand) (limit : int) : pterm listStand =
  match l with
  | Empty -> Empty
  | Cons (t, ts) ->
      let t' = simplify_term_with_limit t limit in
      let ts' = simplify_list_with_limit ts limit in
      Cons (t', ts')

(* Fonction pour vérifier si un terme est une valeur *)
and is_value (t : pterm) : bool =
match t with
| Var _ -> true
| App (Var x, t2) -> is_value t2
| Abs (_, _) -> true
| _ -> false


let rec ltr_ctb_step (t : pterm) : pterm option =
  match t with
  | Var _ -> None
  | Abs (x, t1) ->
      (match ltr_ctb_step t1 with
       | Some t1' -> Some (Abs (x, t1'))
       | None -> None)
  | App (Abs (x, t1), v2) when is_value v2 ->
      Some (substitution x v2 t1)
  | App (t1, t2) ->
      (match ltr_ctb_step t1 with
       | Some t1' -> Some (App (t1', t2))
       | None ->
           (match ltr_ctb_step t2 with
            | Some t2' -> Some (App (t1, t2'))
            | None -> None))
  | Int _ -> None
  | Add (Int n1, Int n2) -> Some (Int (n1 + n2))
  | Add (t1, t2) when is_value t1 ->
      (match ltr_ctb_step t2 with
       | Some t2' -> Some (Add (t1, t2'))
       | None -> None)
  | Add (t1, t2) ->
      (match ltr_ctb_step t1 with
       | Some t1' -> Some (Add (t1', t2))
       | None -> None)
  | Sub (Int n1, Int n2) -> Some (Int (n1 - n2))
  | Sub (t1, t2) when is_value t1 ->
      (match ltr_ctb_step t2 with
       | Some t2' -> Some (Sub (t1, t2'))
       | None -> None)
  | Sub (t1, t2) ->
      (match ltr_ctb_step t1 with
       | Some t1' -> Some (Sub (t1', t2))
       | None -> None)
  | Cons (t1, t2) when is_value t1 ->
      (match ltr_ctb_step t2 with
       | Some t2' -> Some (Cons (t1, t2'))
       | None -> None)
  | Cons (t1, t2) ->
      (match ltr_ctb_step t1 with
       | Some t1' -> Some (Cons (t1', t2))
       | None -> None)
  | List l -> (
      match ltr_ctb_step_list l with
      | Some l' -> Some (List l')
      | None -> None)
  | Nil -> None
  | Head (List (Cons (t1, _))) -> Some t1
  | Head (List Empty) -> None
  | Head t ->
      (match ltr_ctb_step t with
       | Some t' -> Some (Head t')
       | None -> None)
  | Tail (List (Cons (_, t2))) -> Some (List t2)
  | Tail (List Empty) -> None
  | Tail t ->
      (match ltr_ctb_step t with
       | Some t' -> Some (Tail t')
       | None -> None)
  | IfZero (Int 0, t2, _) -> Some t2
  | IfZero (Int _, _, t3) -> Some t3
  | IfZero (t1, t2, t3) ->
      (match ltr_ctb_step t1 with
       | Some t1' -> Some (IfZero (t1', t2, t3))
       | None -> None)
  | IfEmpty (List Empty, t2, _) -> Some t2
  | IfEmpty (List (Cons _), _, t3) -> Some t3
  | IfEmpty (t1, t2, t3) ->
      (match ltr_ctb_step t1 with
       | Some t1' -> Some (IfEmpty (t1', t2, t3))
       | None -> None)
  | Fix (Abs (x, t)) -> Some (substitution x t t)
  | Let (x, t1, t2) when is_value t1 ->
      Some (substitution x t1 t2)
  | Let (x, t1, t2) ->
      (match ltr_ctb_step t1 with
       | Some t1' -> Some (Let (x, t1', t2))
       | None -> None)
  | _ -> None

and ltr_ctb_step_list (l : pterm listStand) : pterm listStand option =
  match l with
  | Empty -> None
  | Cons (t, ts) -> (
      match ltr_ctb_step t with
      | Some t' -> Some (Cons (t', ts))
      | None -> (
          match ltr_ctb_step_list ts with
          | Some ts' -> Some (Cons (t, ts'))
          | None -> None))
  
            
(* Fonction de réduction Call-by-Value avec limitation d'étapes *)
let rec ltr_ctb_step_with_limit (t : pterm) : pterm option =
  match t with
  | Var _ -> None
  | Abs (x, t1) ->
      (match ltr_ctb_step_with_limit t1 with
       | Some t1' -> Some (Abs (x, t1'))
       | None -> None)
  | App (Abs (x, t1), v2) when is_value v2 ->
      Some (simplify_term_with_limit (substitution x v2 t1) 4) (* Limite fixée à 4 *)
  | App (t1, t2) ->
      (match ltr_ctb_step_with_limit t1 with
       | Some t1' -> Some (App (t1', t2))
       | None ->
           (match ltr_ctb_step_with_limit t2 with
            | Some t2' -> Some (App (t1, t2'))
            | None -> None))
  | Int _ -> None
  | Add (Int n1, Int n2) -> Some (Int (n1 + n2))
  | Add (t1, t2) when is_value t1 ->
      (match ltr_ctb_step_with_limit t2 with
       | Some t2' -> Some (Add (t1, t2'))
       | None -> None)
  | Add (t1, t2) ->
      (match ltr_ctb_step_with_limit t1 with
       | Some t1' -> Some (Add (t1', t2))
       | None -> None)
  | Sub (Int n1, Int n2) -> Some (Int (n1 - n2))
  | Sub (t1, t2) when is_value t1 ->
      (match ltr_ctb_step_with_limit t2 with
       | Some t2' -> Some (Sub (t1, t2'))
       | None -> None)
  | Sub (t1, t2) ->
      (match ltr_ctb_step_with_limit t1 with
       | Some t1' -> Some (Sub (t1', t2))
       | None -> None)
  | Cons (t1, t2) when is_value t1 ->
      (match ltr_ctb_step_with_limit t2 with
       | Some t2' -> Some (Cons (t1, t2'))
       | None -> None)
  | Cons (t1, t2) ->
      (match ltr_ctb_step_with_limit t1 with
       | Some t1' -> Some (Cons (t1', t2))
       | None -> None)
  | List l -> (
      match ltr_ctb_step_list_limited l with
      | Some l' -> Some (List l')
      | None -> None)
  | Head (List (Cons (t1, _))) -> Some t1
  | Tail (List (Cons (_, t2))) -> Some (List t2)
  | Let (x, t1, t2) when is_value t1 ->
      Some (simplify_term_with_limit (substitution x t1 t2) 4) (* Limite fixée à 4 *)
  | Let (x, t1, t2) ->
      (match ltr_ctb_step_with_limit t1 with
       | Some t1' -> Some (Let (x, t1', t2))
       | None -> None)
  | _ -> None

and ltr_ctb_step_list_limited (l : pterm listStand) : pterm listStand option =
  match l with
  | Empty -> None
  | Cons (t, ts) -> (
      match ltr_ctb_step_with_limit t with
      | Some t' -> Some (Cons (t', ts))
      | None -> (
          match ltr_ctb_step_list_limited ts with
          | Some ts' -> Some (Cons (t, ts'))
          | None -> None))

let rec ltr_cbv_norm (t : pterm) : pterm =
  match ltr_ctb_step t with
  | Some t' -> ltr_cbv_norm t'  (* On continue à réduire le terme *)
  | None -> t  
           
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
