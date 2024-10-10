(* Define the expression type *)
type expr =
  | Var of string
  | Star
  | Pi of string * expr * expr      (* (x : τ1) → τ2 *)
  | Lambda of string * expr * expr  (* λ(x : τ1). e2 *)
  | App of expr * expr              (* e1 e2 *)
  | Nat                             (* ℕ *)
  | Zero                            (* 0 *)
  | Succ of expr                    (* succ e *)
  | ElimNat of expr * expr * expr * expr  (* elimNat e1 e2 e3 e4 *)

(* Print the expression structure *)
let rec dump_expr e =
  match e with
  | Var x -> Printf.sprintf "Var(%s)" x
  | Star -> "Star"
  | Pi (x, tau1, tau2) ->
      Printf.sprintf "Pi(%s, %s, %s)" x (dump_expr tau1) (dump_expr tau2)
  | Lambda (x, tau1, e2) ->
      Printf.sprintf "Lambda(%s, %s, %s)" x (dump_expr tau1) (dump_expr e2)
  | App (e1, e2) ->
      Printf.sprintf "App(%s, %s)" (dump_expr e1) (dump_expr e2)
  | Nat -> "Nat"
  | Zero -> "Zero"
  | Succ e1 -> Printf.sprintf "Succ(%s)" (dump_expr e1)
  | ElimNat (e1, e2, e3, e4) ->
      Printf.sprintf "ElimNat(%s, %s, %s, %s)"
        (dump_expr e1) (dump_expr e2) (dump_expr e3) (dump_expr e4)


(* Define the environment *)
type environment = (string * expr) list

let rec lookup env x =
  match env with
  | [] -> None
  | (y, ty) :: rest -> if x = y then Some ty else lookup rest x

(* Module for sets of strings *)
module StringSet = Set.Make(String)

(* Compute the set of free variables in an expression *)
let rec free_vars expr =
  match expr with
  | Var x -> StringSet.singleton x
  | Star -> StringSet.empty
  | Pi (x, tau1, tau2) ->
      let fv_tau1 = free_vars tau1 in
      let fv_tau2 = StringSet.remove x (free_vars tau2) in
      StringSet.union fv_tau1 fv_tau2
  | Lambda (x, tau1, e2) ->
      let fv_tau1 = free_vars tau1 in
      let fv_e2 = StringSet.remove x (free_vars e2) in
      StringSet.union fv_tau1 fv_e2
  | App (e1, e2) ->
      StringSet.union (free_vars e1) (free_vars e2)
  | Nat -> StringSet.empty
  | Zero -> StringSet.empty
  | Succ e1 ->
      free_vars e1
  | ElimNat (e1, e2, e3, e4) ->
      StringSet.union (free_vars e1)
        (StringSet.union (free_vars e2)
          (StringSet.union (free_vars e3) (free_vars e4)))

(* Generate a fresh variable name not in the given set *)
let rec fresh_var x used_vars =
  if StringSet.mem x used_vars then
    fresh_var (x ^ "'") used_vars
  else
    x

(* Rename a variable in an expression *)
let rec rename_var e old_name new_name =
  match e with
  | Var y -> if y = old_name then Var new_name else e
  | Star -> Star
  | Pi (y, tau1, tau2) ->
      let y', tau2' =
        if y = old_name then
          (new_name, tau2)
        else
          (y, rename_var tau2 old_name new_name)
      in
      Pi (y', rename_var tau1 old_name new_name, tau2')
  | Lambda (y, tau1, e2) ->
      let y', e2' =
        if y = old_name then
          (new_name, e2)
        else
          (y, rename_var e2 old_name new_name)
      in
      Lambda (y', rename_var tau1 old_name new_name, e2')
  | App (e1, e2) ->
      App (rename_var e1 old_name new_name, rename_var e2 old_name new_name)
  | Nat -> Nat
  | Zero -> Zero
  | Succ e1 ->
      Succ (rename_var e1 old_name new_name)
  | ElimNat (e1, e2, e3, e4) ->
      ElimNat (rename_var e1 old_name new_name, rename_var e2 old_name new_name,
               rename_var e3 old_name new_name, rename_var e4 old_name new_name)

(* Capture-avoiding substitution *)
let rec substitute e x e' =
  match e with
  | Var y ->
      if y = x then e' else e
  | Star -> Star
  | Pi (y, tau1, tau2) ->
      let tau1' = substitute tau1 x e' in
      if y = x then
        Pi (y, tau1', tau2)
      else if StringSet.mem y (free_vars e') then
        let used_vars = StringSet.union (free_vars tau1') (free_vars tau2) in
        let used_vars = StringSet.union used_vars (free_vars e') in
        let y' = fresh_var y used_vars in
        let tau2_renamed = rename_var tau2 y y' in
        let tau2' = substitute tau2_renamed x e' in
        Pi (y', tau1', tau2')
      else
        let tau2' = substitute tau2 x e' in
        Pi (y, tau1', tau2')
  | Lambda (y, tau1, e2) ->
      let tau1' = substitute tau1 x e' in
      if y = x then
        Lambda (y, tau1', e2)
      else if StringSet.mem y (free_vars e') then
        let used_vars = StringSet.union (free_vars tau1') (free_vars e2) in
        let used_vars = StringSet.union used_vars (free_vars e') in
        let y' = fresh_var y used_vars in
        let e2_renamed = rename_var e2 y y' in
        let e2' = substitute e2_renamed x e' in
        Lambda (y', tau1', e2')
      else
        let e2' = substitute e2 x e' in
        Lambda (y, tau1', e2')
  | App (e1, e2) ->
      App (substitute e1 x e', substitute e2 x e')
  | Nat -> Nat
  | Zero -> Zero
  | Succ e1 ->
      Succ (substitute e1 x e')
  | ElimNat (e1, e2, e3, e4) ->
      ElimNat (substitute e1 x e', substitute e2 x e',
               substitute e3 x e', substitute e4 x e')

(* Evaluation of expressions *)
let rec eval_once e =
  match e with
  | App (Lambda (x, _, e1), e2) ->
      substitute e1 x e2
  | ElimNat (e1, e2, e3, Zero) ->
      e2
  | ElimNat (e1, e2, e3, Succ n) ->
      let rec_call = ElimNat (e1, e2, e3, n) in
      App (App (e3, n), rec_call)
  | Pi (x, tau1, tau2) ->
      let tau1' = eval_once tau1 in
      if tau1' <> tau1 then
        Pi (x, tau1', tau2)
      else
        let tau2' = eval_once tau2 in
        if tau2' <> tau2 then
          Pi (x, tau1, tau2')
        else
          e
  | Lambda (x, tau1, e1) ->
      let e1' = eval_once e1 in
      if e1' <> e1 then
        Lambda (x, tau1, e1')
      else
        e
  | App (e1, e2) ->
      let e1' = eval_once e1 in
      if e1' <> e1 then
        App (e1', e2)
      else
        let e2' = eval_once e2 in
        if e2' <> e2 then
          App (e1, e2')
        else
          e
  | Succ e1 ->
      let e1' = eval_once e1 in
      if e1' <> e1 then
        Succ e1'
      else
        e
  | ElimNat (e1, e2, e3, e4) ->
      let e1' = eval_once e1 in
      if e1' <> e1 then
        ElimNat (e1', e2, e3, e4)
      else
        let e2' = eval_once e2 in
        if e2' <> e2 then
          ElimNat (e1, e2', e3, e4)
        else
          let e3' = eval_once e3 in
          if e3' <> e3 then
            ElimNat (e1, e2, e3', e4)
          else
            let e4' = eval_once e4 in
            if e4' <> e4 then
              ElimNat (e1, e2, e3, e4')
            else
              e
  | _ -> e  (* Star, Nat, Zero, Var *)

let rec eval e =
  let e' = eval_once e in
  if e' = e then
    e
  else
    eval e'


let () =
  let identity = Lambda ("x", Nat, Var "x") in
  let expr1 = App (identity, Zero) in
  Printf.printf "Dumped expression: %s\n" (dump_expr expr1)

let () =
  let double = Lambda ("x", Nat, Succ (Succ (Var "x"))) in
  let process_nat =
    Lambda ("n", Nat,
      ElimNat (
        Pi ("m", Nat, Star),
        Star,
        Lambda ("m", Nat, Lambda ("_", Pi ("_", Nat, Star), Star)),
        Var "n"
      )
    )
  in
  let expr = App (process_nat, App (double, Zero)) in
  Printf.printf "Dumped expression: %s\n" (dump_expr expr)


