
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






