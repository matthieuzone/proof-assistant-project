(** Variables. *)
type var = string

(** Expressions. *)
type expr =
  | Type
  | Var of var
  | App of expr * expr
  | Abs of var * expr * expr
  | Pi of var * expr * expr
  | Nat
  | Z
  | S of expr
  | Ind of expr * expr * expr * expr 
  | Eq of expr * expr
  | Refl of expr
  | J of expr * expr * expr * expr * expr

(* Fill me in! *)
let to_string = function
  | Type -> "Type"
  | Var x -> x
  | App (e1, e2) -> "(" ^ to_string e1 ^ " " ^ to_string e2 ^ ")"
  | Abs (x, ty, e) -> "(λ" ^ x ^ ":" ^ to_string ty ^ "." ^ to_string e ^ ")"
  | Pi (x, ty, e) -> "(Π" ^ x ^ ":" ^ to_string ty ^ "." ^ to_string e ^ ")"
  | _ -> "Not implemented"