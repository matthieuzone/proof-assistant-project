open Expr

let ty_of_string s = Parser.ty Lexer.token (Lexing.from_string s)

let tm_of_string s = Parser.tm Lexer.token (Lexing.from_string s)

let rec string_of_ty = function
  | TVar a -> a
  | Imp (a, b) -> "(" ^ string_of_ty a ^ " ⇒ " ^ string_of_ty b ^ ")"
  | TPair (a, b) -> "(" ^ string_of_ty a ^ " ∧ " ^ string_of_ty b ^ ")"
  | True -> "⊤"
  | TCoproduct (a, b) -> "(" ^ string_of_ty a ^ " ∨ " ^ string_of_ty b ^ ")"
  | False -> "⊥"

let rec string_of_tm = function
  | Var x -> x
  | Abs (x, ty, t) -> "(λ" ^ x ^ ":" ^ string_of_ty ty ^ "." ^ string_of_tm t ^ ")"
  | App (t1, t2) -> "(" ^ string_of_tm t1 ^ " " ^ string_of_tm t2 ^ ")"
  | Pair (t1, t2) -> "<" ^ string_of_tm t1 ^ ", " ^ string_of_tm t2 ^ ">"
  | Fst t -> "π₁" ^ string_of_tm t
  | Snd t -> "π₂" ^ string_of_tm t
  | Unit -> "<>"
  | Case (t, u, v) -> "case(" ^ string_of_tm t ^ " of inl " ^ string_of_tm u ^ " | inr " ^ string_of_tm v ^ ")"
  | Inl (t, _) -> "ιl(" ^ string_of_tm t ^ ")"
  | Inr (_, t) -> "ιr(" ^ string_of_tm t ^ ")"
  | Curryabs (x, t) -> "(λ" ^ x ^ "." ^ string_of_tm t ^ ")"
  | Empty (t, _) -> "case(" ^ string_of_tm t ^ ")"

type context = (var * ty) list
exception Type_error

let rec infer_type (c : context) (t : tm) : ty = match t with
  | Var x -> (try List.assoc x c with Not_found -> raise Type_error)
  | Abs (x, ty, t) -> Imp (ty, infer_type ((x, ty) :: c) t)
  | App (t1, t2) -> (match infer_type c t1 with
    | Imp (ty1, ty2) -> check_type c t2 ty1; ty2
    | _ -> raise Type_error)
  | Pair (t1, t2) -> TPair (infer_type c t1, infer_type c t2)
  | Fst t -> (match infer_type c t with
    | TPair (ty1, _) -> ty1
    | _ -> raise Type_error)
  | Snd t -> (match infer_type c t with
    | TPair (_, ty2) -> ty2
    | _ -> raise Type_error)
  | Unit -> True
  | Inl (t, ty) -> TCoproduct (infer_type c t, ty)
  | Inr (ty, t) -> TCoproduct (ty, infer_type c t)
  | Case (t, u, v) -> (match infer_type c t with
    | TCoproduct (ty1, ty2) -> (match u, v with
      | Curryabs (x, u1), Curryabs (y, v1) -> (let ty = infer_type ((x, ty1) :: c) u1 in
        check_type ((y, ty2) :: c) v1 ty; ty
        )
      | _ -> raise Type_error)
    | _ -> raise Type_error)
  | Curryabs _ -> raise Type_error
  | Empty (t, ty) -> check_type c t False; ty

and check_type env t ty =
  match t, ty with
    | Curryabs (x, t), Imp (ty1, ty2) -> check_type ((x, ty1) :: env) t ty2;
    | _ -> if infer_type env t <> ty then raise Type_error

let t1 = 
Abs ("f", Imp (TVar "A", TVar "B"),
  Abs ("g", Imp (TVar "B", TVar "C"),
    Abs ("x", TVar "A",
      App (Var "g", App (Var "f", Var "x"))
    )
  )
);;

string_of_tm t1;;
string_of_ty (infer_type [] t1);;

let t2 = Abs ("f" , TVar "A", Var "x");;
string_of_tm t2;;
(* string_of_ty (infer_type [] t2);; *)

let t3 = 
Abs ("f", TVar "A",
  Abs ("x", TVar "B",
    App (Var "f", Var "x")
  )
);;
string_of_tm t3;;
(* string_of_ty (infer_type [] t3);; *)

let t4 = 
Abs ("f", Imp (TVar "A", TVar "B"),
  Abs ("x", TVar "B",
    App (Var "f", Var "x")
  )
);;

string_of_tm t4;;
(* string_of_ty (infer_type [] t4);; *)

let andcomm = Abs ("x", TPair (TVar "A", TVar "B"), Pair (Snd (Var "x"), Fst (Var "x")));;
string_of_tm andcomm;;
string_of_ty (infer_type [] andcomm);;

let t5 = Abs ("x", Imp (True, TVar "A"), App (Var "x", Unit));;
string_of_tm t5;;
string_of_ty (infer_type [] t5);;

let orcomm = Abs ("x", TCoproduct (TVar "A", TVar "B"), Case (Var "x", Curryabs ("t", Inr (TVar "B", Var "t")), Curryabs ("t", Inl (Var "t", TVar "A"))));;
string_of_tm orcomm;;
string_of_ty (infer_type [] orcomm);;

let t6 = Abs(
  "x", TPair(TVar "A", (Imp(TVar "A", False))),
  Empty(Var"x", TVar "B")
);;
string_of_tm t6;;
(* string_of_ty (infer_type [] t6);; *)

let t7 = Abs(
  "p", TPair(TVar "A", Imp (TVar "A", False)),
  Empty(App(Snd(Var "p"), Fst(Var "p")), TVar "B")
);;
print_string ((string_of_tm t7) ^ "\n");;
print_string ((string_of_ty (infer_type [] t7)) ^ "\n");;

let () =
  let l = [
    "A => B";
    "A ⇒ B";
    "A /\\ B";
    "A ∧ B";
    "T";
    "A \\/ B";
    "A ∨ B";
    "_";
    "not A";
    "¬ A";
  ]
  in
  List.iter
    (fun s ->
       Printf.printf
         "the parsing of %S is %s\n%!" s (string_of_ty (ty_of_string s))
    ) l;;

let () =
  let l = [
    "t u v";
    "fun (x : A) -> t";
    "λ (x : A) → t";
    "(t , u)";
    "fst(t)";
    "snd(t)";
    "()";
    "case t of x -> u | y -> v";
    "left(t,B)";
    "right(A,t)";
    "absurd(t,A)"
  ]
  in
  List.iter
    (fun s ->
        Printf.printf
          "the parsing of %S is %s\n%!" s (string_of_tm (tm_of_string s))
    ) l;;

let string_of_context c =
  String.concat " , " (List.map (fun (x, ty) -> x ^ " : " ^ string_of_ty ty) c)

type sequent = context * ty
let string_of_sequent (c, ty) = string_of_context c ^ " ⊢ " ^ string_of_ty ty

let rec prove env a =
  print_endline (string_of_sequent (env,a));
  print_string "? "; flush_all ();
  let error e = print_endline e; prove env a in
  let cmd, arg =
    let cmd = input_line stdin in
    let n = try String.index cmd ' ' with Not_found -> String.length cmd in
    let c = String.sub cmd 0 n in
    let a = String.sub cmd n (String.length cmd - n) in
    let a = String.trim a in
    c, a
  in
  match cmd with
  | "intro" ->
     (
       match a with
       | Imp (a, b) ->
          if arg = "" then error "Please provide an argument for intro." else
            let x = arg in
            let t = prove ((x,a)::env) b in
            Abs (x, a, t)
       | _ ->
          error "Don't know how to introduce this."
     )
  | "exact" ->
     let t = tm_of_string arg in
     if infer_type env t <> a then error "Not the right type."
     else t
  | "elim" ->
    (
      let t = tm_of_string arg in
      match infer_type env t with
        | Imp (ta, tb) ->
          if tb <> a then error ("Can't use _ => " ^ string_of_ty tb ^ " to prove " ^ string_of_ty a)
          else App (t, prove env ta)
        | _ -> error "Can't eliminate this."

    )

  | cmd -> error ("Unknown command: " ^ cmd)
         
let () =
  print_endline "Please enter the formula to prove:";
  let a = input_line stdin in
  let a = ty_of_string a in
  print_endline "Let's prove it.";
  let t = prove [] a in
  print_endline "done.";
  print_endline "Proof term is";
  print_endline (string_of_tm t);
  print_string  "Typechecking... "; flush_all ();
  assert (infer_type [] t = a);
  print_endline "ok."