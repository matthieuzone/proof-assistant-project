(** Type variables. *)
type tvar = string

(** Term variables. *)
type var = string

(** Types. *)
type ty =
  | TVar of tvar
  | Imp of ty * ty
  | TPair of ty * ty
  | True
  | TCoproduct of ty * ty
  | False

(** Terms. *)
type tm =
  | Var of var
  | Abs of var * ty * tm
  | App of tm * tm
  | Pair of tm * tm
  | Fst of tm
  | Snd of tm
  | Unit
  | Case of tm * tm * tm
  | Inl of tm * ty
  | Inr of ty * tm
  | Curryabs of var * tm
  | Empty of tm * ty