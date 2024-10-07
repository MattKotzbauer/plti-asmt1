
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


type environment = (string * expr) list
let rec lookup env x =
  match env with
  | [] -> None
  | (y, ty) :: rest -> if x = y then Some ty else lookup rest x


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






