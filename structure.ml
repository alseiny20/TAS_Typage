(* liste standard *)
type 'a listStand = Empty | Cons of 'a * 'a listStand
type pterm = 
  | Var of string
  | App of pterm * pterm
  | Abs of string * pterm
  | Int of int
  | Add of pterm * pterm
  | Sub of pterm * pterm
  | Cons of pterm * pterm
  | List of pterm listStand
  | Nil
  | Head of pterm
  | Tail of pterm
  | IfZero of pterm * pterm * pterm
  | IfEmpty of pterm * pterm * pterm
  | Fix of pterm
  | Let of string * pterm * pterm
  | Unit
  | Ref of pterm
  | Deref of pterm        
  | Assign of pterm * pterm 
  | Adresse of int         

type ptype = Var_t of string 
            | Arr of ptype * ptype
            | Nat 
            | N 
            | List_t of ptype             
            | Forall of string list * ptype    
            | Unit_t
            | Ref_t of ptype

type equa = ( ptype * ptype ) list

type env = ( string * ptype ) list

(* Exceptions déclarées pour les erreurs pertinentes *)
exception InvalidFixApplication of string
(* Levée lorsque Fix est appliqué à autre chose qu'une abstraction *)

exception VariableNotFound of string
(* Levée lorsqu'une variable n'est pas trouvée dans l'environnement *)

exception TypeInferenceFailed of string
(* Levée lorsque l'inférence de type échoue pour une expression *)

exception UnsupportedTerm of string
(* Levée lorsqu'un terme non pris en charge est rencontré dans une fonction *)

exception OutOfReductionSteps of string
(* Levée lorsqu'une limite de réduction est atteinte *)