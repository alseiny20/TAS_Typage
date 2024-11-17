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

type ptype = Var_t of string 
            | Arr of ptype * ptype
            | Nat 
            | N 
            | List_t of ptype             
            | Forall of string list * ptype    
            | Unit_t
            | Ref_t of pterm

type equa = ( ptype * ptype ) list

type env = ( string * ptype ) list

