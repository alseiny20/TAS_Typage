type pterm = 
  | Var of string
  | App of pterm * pterm
  | Abs of string * pterm

type ptype = Var_t of string 
            | Arr of ptype * ptype
            | Nat 

type equa = ( ptype * ptype ) list

type env = ( string * ptype ) list

