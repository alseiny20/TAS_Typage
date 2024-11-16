open Type
open Ast

(* Test de la fonction genere_equa *)
let test_genere_equa () =
  let term = Var "x" in
  let env = [("x", Nat)] in
  let ty = Var_t "T" in
  let expected = [(Nat, ty)] in
  let result = genere_equa term ty env in
  let _ = print_endline (" result " ^ (print_equa result)) in
  let _ = print_endline (" expected " ^ (print_equa expected)) in

  if result = expected then
    print_endline "test_genere_equa passed"
  else
    failwith "test_genere_equa failed"


(* Test de la fonction occur_check avec les cas vrais et faux *)
let true_cases = [
  ("T", Var_t "T");
  ("T", Arr (Var_t "T", Nat));
  ("X", Arr (Var_t "A", Var_t "X"));
  ("Z", Arr (Nat, Arr (Var_t "Z", Nat)));
]

let false_cases = [
  ("T", Nat);
  ("X", Arr (Var_t "A", Nat));
  ("Z", Arr (Nat, Arr (Var_t "Y", Nat)));
  ("A", Var_t "B");
]

let test_occur_check_cases cases expected_result =
  List.fold_left (fun acc (key, typ) ->
    let result = occur_check key typ in
    if result = expected_result then
      acc
    else
      (print_endline ("Test failed for key: " ^ key ^ " in type: " ^ print_type typ ^ ". Expected " ^ string_of_bool expected_result ^ ", got " ^ string_of_bool result);
       false)
  ) true cases

let test_occur_check () =
  let true_result = test_occur_check_cases true_cases true in
  let false_result = test_occur_check_cases false_cases false in
  if true_result && false_result then
    print_endline "test_occur_check passed"
  else
    failwith "test_occur_check failed"

(* Test de la fonction unification_step *)
let test_unification_step () =
  let equations = [(Var_t "T", Nat)] in
  let expected_sub_env = [("T", Nat)] in
  let _, sub_env = unification_step equations [] in
  if sub_env = expected_sub_env then
    print_endline "test_unification_step passed"
  else
    failwith "test_unification_step failed"

let test_unification_step_arrow () =
  let equations = [
    (Var_t "T1", Var_t "T2"); 
    (Arr (Var_t "T1", Var_t "T2"), Arr (Var_t "T3", Var_t "T4"))
  ] 
  in
  let expected_sub_env = [("T", Nat); ("U", Nat)] in
  let res = resolve_with_timeout equations [] 500  in
  match res with
  | Some _ ->  print_endline "test_unification_step_arrow passed"
  | _ -> failwith "test_unification_step_arrow failed"

let test_unification_step_complex () =
  let equations = [
    (Var_t "X", Arr (Nat, Var_t "Y"));  (* X = Nat -> Y *)
    (Var_t "Y", Arr (Var_t "Z", Nat));  (* Y = Z -> Nat *)
    (Var_t "Z", Nat);                   (* Z = Nat *)
    (Arr (Var_t "X", Var_t "Y"), Var_t "W")  (* X -> Y = W *)
  ] in
  let expected_sub_env = [
    ("X", Arr (Nat, Arr (Nat, Nat)));
    ("Y", Arr (Nat, Nat));
    ("Z", Nat);
    ("W", Arr (Arr (Nat, Nat), Arr (Nat, Nat)))
  ] in
  let res = resolve_with_timeout equations [] 500 in
  match res with
  | Some (_, sub_env) when sub_env = expected_sub_env ->
      print_endline "test_unification_step_complex passed"
  | Some (_, sub_env) ->
      failwith ("test_unification_step_complex failed: unexpected substitution environment " ^ (String.concat "; " (List.map (fun (v, t) -> v ^ " -> " ^ print_type t) sub_env)))
  | None -> failwith "test_unification_step_complex failed: no solution found"

let test_unification_step_impossible () =
  let equations = [
    (Nat, Arr (Var_t "T1", Var_t "T2"));  (* Nat = T1 -> T2, ce qui est impossible car Nat n'est pas une fonction *)
    (Var_t "T1", Nat);
    (Var_t "T2", Var_t "T3");
    (Arr (Nat, Var_t "T3"), Nat)  (* Nat -> T3 = Nat, également impossible car un type fléché ne peut pas être égal à Nat *)
  ] in
  let res = resolve_with_timeout equations [] 500 in
  match res with
  | None -> print_endline "test_unification_step_impossible passed: unification not possible"
  | Some _ -> failwith "test_unification_step_impossible failed: expected unification failure"


(* Test de la fonction infer_type *)
let test_infer_type_identity () =
  let term = Abs ("x", Var "x") in
  let env = [] in
  let result, _ = infer_type env term in
  match result with
  | Some (Arr (Var_t _, Var_t _)) -> print_endline "test_infer_type_identity passed"
  | _ -> failwith "Expected a polymorphic identity function type (T -> T)"

(* let test_infer_type_application () =
  let term = App (Var "f", Var "x") in
  let env = [("f", Arr (Nat, Nat)); ("x", Nat)] in
  let result, _ = infer_type env term in
  match result with
  | Some Nat -> print_endline "test_infer_type_application passed"
  | _ -> failwith "Expected type Nat" *)

let test_infer_type_complex_application () =
  (* Terme: (λy. f (g y)) x *)
  (* Où f : T1 -> T2, g : T3 -> T1, et x : T3 *)
  let term = App (Abs ("y", App (Var "f", App (Var "g", Var "y"))), Var "x") in
  let env = [
    ("f", Arr (Var_t "T1", Var_t "T2"));
    ("g", Arr (Var_t "T3", Var_t "T1"));
    ("x", Var_t "T3")
  ] in
  let result, _ = infer_type env term in
  match result with
  | Some (Var_t "T2") -> print_endline "test_infer_type_complex_application passed"
  | _ -> failwith "Expected type T2"

let test_infer_type_incompatible_application1 () =
  (* Terme: (λy. f (y y)) *)
  (* Où f : T1 -> T2, mais y est appliqué à lui-même, ce qui est impossible pour un type non-fonctionnel *)
  let term = Abs ("y", App (Var "f", App (Var "y", Var "y"))) in
  let env = [
    ("f", Arr (Var_t "T1", Var_t "T2"))
  ] in
  let result, _ = infer_type env term in
  match result with
  | None -> print_endline "test_infer_type_incompatible_application passed (incompatible types detected)"
  | Some _ -> failwith "Expected type inference failure due to incompatible application"
  
let test_infer_type_incompatible_application () =
  (* Terme: f (x x), où f : T1 -> T2 et x est appliqué à lui-même, ce qui est incompatible. *)
  let term = App (Var "f", App (Var "x", Var "x")) in
  let env = [
    ("f", Arr (Var_t "T1", Var_t "T2"));  (* f : T1 -> T2 *)
    ("x", Nat)  (* x : nat, donc (x x) est impossible *)
  ] in
  let result, _ = infer_type env term in
  match result with
  | None -> print_endline "test_infer_type_incompatible_application passed (incompatible types detected)"
  | Some _ -> failwith "Expected type inference failure due to incompatible application"

(* Exécution de tous les tests *)
let () =
  test_genere_equa ();
  (* test_genere_equa_application (); *)
  test_occur_check ();
  test_unification_step ();
  test_unification_step_arrow ();
  test_unification_step_impossible();
  test_infer_type_identity ();
  (* test_infer_type_application (); *)
  (* test_infer_type_complex_application(); *)
  (* test_infer_type_incompatible_application (); *)