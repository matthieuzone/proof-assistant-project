open Expr

let of_string s = Parser.expr Lexer.token (Lexing.from_string s)

let rec to_string e = match e with
  | Type -> "Type"
  | Var x -> x
  | App (e1, e2) -> "(" ^ to_string e1 ^ " " ^ to_string e2 ^ ")"
  | Abs (x, ty, e) -> "(λ (" ^ x ^ " : " ^ to_string ty ^ ") -> " ^ to_string e ^ ")"
  | Pi (x, ty, e) -> "(Π (" ^ x ^ " : " ^ to_string ty ^ ") -> " ^ to_string e ^ ")"
  | Nat -> "Nat"
  | Z -> "Z"
  | S t -> "(S " ^ to_string t ^ ")"
  | Ind (p, z, s, m) -> "(Ind " ^ to_string p ^ " " ^ to_string z ^ " " ^ to_string s ^ " " ^ to_string m ^ ")"
  | Eq (t, u) -> "("^to_string t ^ " = " ^ to_string u ^ ")"
  | Refl t -> "(Refl " ^ to_string t ^ ")"
  | J (p, r, x, y, e) -> "(J " ^ to_string p ^ " " ^ to_string r ^ " " ^ to_string x ^ " " ^ to_string y ^ " " ^ to_string e ^ ")"

let fresh_var =
  let r = ref 0 in
  fun () ->
    let v = "x" ^ string_of_int !r in
    r := !r + 1;
    v

let rec subst x t u =
  match u with
  | Type -> Type
  | Var y -> if x = y then t else Var y
  | App (u1, u2) -> App (subst x t u1, subst x t u2)
  | Abs (y, ty, u) -> let z = fresh_var () in
      Abs (z, subst x t ty, subst x t (subst y (Var z) u))
  | Pi (y, ty, u) -> let z = fresh_var () in
      Pi (z, subst x t ty, subst x t (subst y (Var z) u))
  | Nat -> Nat
  | Z -> Z
  | S u -> S (subst x t u)
  | Ind (p, z, s, m) -> Ind (subst x t p, subst x t z, subst x t s, subst x t m)
  | Eq (u1, u2) -> Eq (subst x t u1, subst x t u2)
  | Refl u -> Refl (subst x t u)
  | J (p, r, y, z, e) -> J (subst x t p, subst x t r, subst x t y, subst x t z, subst x t e)

type context = (var * (expr * expr option)) list

let rec string_of_context = function
  | [] -> ""
  | (x, (ty, None)) :: ctx -> x ^ ":" ^ to_string ty ^ "\n" ^ string_of_context ctx
  | (x, (ty, Some e)) :: ctx -> x ^ ":" ^ to_string ty ^ " = " ^ to_string e ^ "\n" ^ string_of_context ctx

let rec normalize ctx e =
  match e with
  | Type -> Type
  | Var x -> (try
      match List.assoc x ctx with
        |(_, Some v) -> normalize ctx v
        |(_, None) -> Var x
    with Not_found -> Var x)
  | App (e1, e2) -> (match normalize ctx e1 with
      | Abs (x, _, eq) -> normalize ctx (subst x e2 eq)
      | e1' -> App (e1', normalize ctx e2))
  | Abs (x, ty, eq) -> let fv = fresh_var () in Abs (fv, normalize ctx ty, normalize ctx (subst x (Var fv) eq))
  | Pi (x, ty, eq) -> let fv = fresh_var () in Pi (fv, normalize ctx ty, normalize ctx (subst x (Var fv) eq))
  | Nat -> Nat
  | Z -> Z
  | S eq -> S (normalize ctx eq)
  | Ind (p, z, s, m) -> (match normalize ctx m with
      | Z -> normalize ctx z
      | S n -> normalize ctx (App (App (s, n), Ind (p, z, s, n)))
      | _ -> Ind (p, z, s, m))
  | Eq (t, u) -> Eq (normalize ctx t, normalize ctx u)
  | Refl t -> Refl (normalize ctx t)
  | J (p, r, x, y, eq) -> (match normalize ctx eq with
      | Refl t -> normalize ctx (App (r, t))
      | en -> J (normalize ctx p, normalize ctx r, normalize ctx x, normalize ctx y, en))

let rec alpha e1 e2 =
  match e1, e2 with
  | Type, Type -> true
  | Var x, Var y -> x = y
  | App (e1, e2), App (e1', e2') -> alpha e1 e1' && alpha e2 e2'
  | Abs (x, ty, e), Abs (y, ty', e') -> alpha ty ty' && alpha (subst x (Var y) e) e'
  | Pi (x, ty, e), Pi (y, ty', e') -> alpha ty ty' && alpha (subst x (Var y) e) e'
  | Nat, Nat -> true
  | Z, Z -> true
  | S e, S e' -> alpha e e'
  | Ind (p, z, s, m), Ind (p', z', s', m') -> alpha p p' && alpha z z' && alpha s s' && alpha m m'
  | Eq (t, u), Eq (t', u') -> alpha t t' && alpha u u'
  | Refl t, Refl t' -> alpha t t'
  | J (p, r, x, y, e), J (p', r', x', y', e') -> alpha p p' && alpha r r' && alpha x x' && alpha y y' && alpha e e'
  | _ -> false

let conv ctx e1 e2 =
  alpha (normalize ctx e1) (normalize ctx e2)

exception Type_error of string

let rec infer ctx e = match e with 
  |Type -> Type
  |Var x -> (try
      let (ty, _) = List.assoc x ctx in
      ty
    with Not_found -> raise (Type_error ("Variable " ^ x ^ " not found")))
  |App (e1, e2) -> (match infer ctx e1, infer ctx e2 with
      |Pi (x, ty, e), ty' when conv ctx ty ty' -> subst x e2 e
      |_, _ -> raise (Type_error "Type mismatch in application"))

  |Abs (x, ty, e) -> Pi (x, ty, infer ((x, (ty, None)) :: ctx) e)
  |Pi (x, ty, e) -> (match infer ctx ty, infer ((x, (ty, None)) :: ctx) e with
      |Type, Type -> Type
      |_, _ -> raise (Type_error "Type mismatch in Pi"))
  |Nat -> Type
  |Z -> Nat
  |S e -> (match infer ctx e with
      |Nat -> Nat
      | _ -> raise (Type_error "Type mismatch in S"))
  |Ind (p, z, s, m) -> (match infer ctx p, infer ctx z, infer ctx s, infer ctx m with
      |Pi (_, Nat, typ), pz, Pi (k, Nat, Pi (_, pk, pk1)), Nat when conv ctx (infer ctx typ) Type && conv ctx pz (App (p, Z)) && conv ctx pk (App (p, Var k)) && conv ctx pk1 (App (p, S (Var k))) -> App (p, m)
      (*should actually by after reduction and not equality in the matching*)
      |_, _, _, _ -> raise (Type_error "Type mismatch in Ind")
    )
  |Eq (t, u) -> (match infer ctx t, infer ctx u with
      |typ, typ' when conv ctx typ typ' -> Type
      |_, _ -> raise (Type_error "Type mismatch in Eq"))
  |Refl t -> Eq (t, t)
  |J (p, r, x, y, e) -> (match infer ctx p, infer ctx r, infer ctx x, infer ctx y, infer ctx e with
      |Pi (x', a1, Pi (y', a2, Pi (_, Eq (vx', vy'), typ))), Pi (z, a3, pzzrz), a4, a5, Eq (vx, vy) when 
      conv ctx a1 a2 && conv ctx a2 a3 && conv ctx a3 a4 && conv ctx a4 a5 && conv ctx vx' (Var x') && conv ctx vy' (Var y') && conv ctx vx x && conv ctx vy y && conv ctx typ Type && conv ctx pzzrz (App (App (App (p, Var z), Var z), Refl (Var z))) -> App (App (App (p, x), y), e)
      (*should actually by after reduction and not equality in the matching*)
      |_, _, _, _, _ -> raise (Type_error "Type mismatch in J"))

let check ctx e ty =
  if conv ctx (infer ctx e) ty then ()
  else raise (Type_error "Type mismatch in check")

let () =
  let env = ref [] in
  let loop = ref true in
  let file = open_out "interactive.proof" in
  let split c s =
    try
      let n = String.index s c in
      String.trim (String.sub s 0 n), String.trim (String.sub s (n+1) (String.length s - (n+1)))
    with Not_found -> s, ""
  in
  while !loop do
    try
      print_string "? ";
      flush_all ();
      let cmd, arg =
        let cmd = input_line stdin in
        output_string file (cmd^"\n");
        print_endline cmd;
        split ' ' cmd
      in
      match cmd with
      | "assume" ->
        let x, sa = split ':' arg in
        let a = of_string sa in
        check !env a Type;
        env := (x,(a,None)) :: !env;
        print_endline (x^" assumed of type "^to_string a)
      | "define" ->
        let x, st = split '=' arg in
        let t = of_string st in
        let a = infer !env t in
        env := (x,(a,Some t)) :: !env;
        print_endline (x^" defined to "^to_string t^" of type "^to_string a)
      | "context" ->
        print_endline (string_of_context !env)
      | "type" ->
        let t = of_string arg in
        let a = infer !env t in
        print_endline (to_string t^" is of type "^to_string a)
      | "check" ->
        let t, a = split '=' arg in
        let t = of_string t in
        let a = of_string a in
        check !env t a;
        print_endline "Ok."
      | "eval" ->
        let t = of_string arg in
        let _ = infer !env t in
        print_endline (to_string (normalize !env t))
      | "exit" -> loop := false
      | "" | "#" -> ()
      | cmd -> print_endline ("Unknown command: "^cmd)
    with
    | End_of_file -> loop := false
    | Failure err -> print_endline ("Error: "^err^".")
    | Type_error err -> print_endline ("Typing error :"^err^".")
    | Parsing.Parse_error -> print_endline ("Parsing error.")
  done;
  print_endline "Bye."