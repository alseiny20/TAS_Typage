open Structure
open Ast

(* j'ai utuliser chatGpt pour cette fonction *)
(* Fonction qui traduit un entier Church en entier normale *)
let church_to_int (n : pterm) : int =
  let rec apply_church church_num =
    match church_num with
    | Abs ("f", Abs ("x", body)) ->
        let succ = fun x -> x + 1 in
        let base = 0 in
        let rec eval_term term f x =
          match term with
          | Var "x" -> x
          | App (Var "f", t) -> eval_term t f (f x)
          | _ -> failwith "Invalid Church numeral"
        in
        eval_term body succ base
    | _ -> failwith "Invalid Church numeral"
  in
  apply_church n

(* Vérification des résultats avec affichage du terme *)
let verify_result term expected_value =
  let reduced_term = ltr_cbv_norm_with_timeout term 100 in
  print_endline ("Terme réduit obtenu : " ^ print_term reduced_term);  
  let computed_value = church_to_int reduced_term in
  if computed_value = expected_value then
    (* Affichage du terme obtenu et de la valeur calculée *)
    print_endline ("Résultat correct : terme value = " ^ string_of_int computed_value)
  else
    failwith ("Erreur : le résultat attendu était " ^ string_of_int expected_value ^ " mais obtenu " ^ string_of_int computed_value)

(* Identité I : λx. x *)
let i = Abs ("x", Var "x")

(* Duplicateur δ : λx. x x *)
let delta = Abs ("x", App (Var "x", Var "x"))

(* Terme divergent Ω : δ δ *)
let omega = App (delta, delta)

(* Combinateur S : λx.λy.λz. (x z) (y z) *)
let s = Abs ("x", Abs ("y", Abs ("z", App (App (Var "x", Var "z"), App (Var "y", Var "z")))))

(* Combinateur K : λx.λy. x *)
let k = Abs ("x", Abs ("y", Var "x"))

(* S K K : λx. x *)
let skk = App (App (s, k), k)

(* S I I : λx. (x x) *)
let sii = App (App (s, i), i)

(* K I : λx. x *)
let ki = App (k, i)

(* S K I I : λx. x *)
let skii = App (App (App (s, k), i), i)

(* S K (S I I) *)
let sk_sii = App (App (s, k), sii)

(* K (S I I) *)
let k_sii = App (k, sii)

(* S I K *)
let sik = App (App (s, i), k)

(* Terme divergent supplémentaire : δ δ δ *)
let delta_delta_delta = App (delta, App (delta, delta))

(* Y combinator *)
let y_combinator = Abs ("f", App (Abs ("x", App (Var "f", App (Var "x", Var "x"))), Abs ("x", App (Var "f", App (Var "x", Var "x")))))

(* Encodage des entiers de Church : 0, 1, 2, 3 *)
let church_zero = Abs ("f", Abs ("x", Var "x"))
let church_one = Abs ("f", Abs ("x", App (Var "f", Var "x")))
let church_two = Abs ("f", Abs ("x", App (Var "f", App (Var "f", Var "x"))))
let church_three = Abs ("f", Abs ("x", App (Var "f", App (Var "f", App (Var "f", Var "x")))))

(* Addition des entiers de Church : λm.λn.λf.λx. m f (n f x) *)
let church_add = Abs ("m", Abs ("n", Abs ("f", Abs ("x", App (App (Var "m", Var "f"), App (App (Var "n", Var "f"), Var "x"))))))

(* Multiplication des entiers de Church : λm.λn.λf. m (n f) *)
let church_mult = Abs ("m", Abs ("n", Abs ("f", App (Var "m", App (Var "n", Var "f")))))

(* Exécution des tests *)
let () =
  (* Test de l'identité I *)
  print_endline "Test I: Identité";
  let result_i = ltr_cbv_norm_with_timeout i 1 in
  print_endline ("Résultat: " ^ print_term result_i);

  (* Test du duplicateur δ *)
  print_endline "\nTest δ: Duplicateur";
  let result_delta = ltr_cbv_norm_with_timeout delta 2 in
  print_endline ("Résultat: " ^ print_term result_delta);

  (* Test du terme divergent Ω *)
  print_endline "\nTest Ω: Terme Divergent";
  let result_omega = ltr_cbv_norm_with_timeout omega 100 in
  print_endline ("Résultat: " ^ print_term result_omega);

  (* Test du terme divergent δ δ δ *)
  print_endline "\nTest δ δ δ: Terme Divergent";
  let result_delta_delta_delta = ltr_cbv_norm_with_timeout delta_delta_delta 100 in
  print_endline ("Résultat: " ^ print_term result_delta_delta_delta);

  (* Test du Y Combinator *)
  print_endline "\nTest Y Combinator: Terme Divergent";
  let result_y_combinator = ltr_cbv_norm_with_timeout y_combinator 100 in
  print_endline ("Résultat: " ^ print_term result_y_combinator);

  (* Test de S K K *)
  print_endline "\nTest S K K";
  let result_skk = ltr_cbv_norm_with_timeout skk 4 in
  print_endline ("Résultat: " ^ print_term result_skk);

  (* Test de S I I *)
  print_endline "\nTest S I I";
  let result_sii = ltr_cbv_norm_with_timeout sii 4 in
  print_endline ("Résultat: " ^ print_term result_sii);

  (* Test de K I *)
  print_endline "\nTest K I";
  let result_ki = ltr_cbv_norm_with_timeout ki 2 in
  print_endline ("Résultat: " ^ print_term result_ki);

  (* Test de S K I I *)
  print_endline "\nTest S K I I";
  let result_skii = ltr_cbv_norm_with_timeout skii 4 in
  print_endline ("Résultat: " ^ print_term result_skii);

  (* Test de S K (S I I) *)
  print_endline "\nTest S K (S I I)";
  let result_sk_sii = ltr_cbv_norm_with_timeout sk_sii 5 in
  print_endline ("Résultat: " ^ print_term result_sk_sii);

  (* Test de K (S I I) *)
  print_endline "\nTest K (S I I)";
  let result_k_sii = ltr_cbv_norm_with_timeout k_sii 3 in
  print_endline ("Résultat: " ^ print_term result_k_sii);

  (* Test de S I K *)
  print_endline "\nTest S I K";
  let result_sik = ltr_cbv_norm_with_timeout sik 3 in
  print_endline ("Résultat: " ^ print_term result_sik);

  (* Test de l'addition Church (1 + 2) *)
  print_endline "\nTest de l'addition Church (1 + 2)";
  let add_test = App (App (church_add, church_one), church_two) in
  verify_result add_test 3;

  (* Test de la multiplication Church (2 * 3) *)
  print_endline "\nTest de la multiplication Church (2 * 3)";
  let mult_test = App (App (church_mult, church_two), church_three) in
  verify_result mult_test 6