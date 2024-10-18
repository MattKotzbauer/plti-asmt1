from dataclasses import dataclass
from typing import List, Tuple, Set, Union

# Base expression class (e): elements are then defined as the same order as in the PDF
@dataclass
class Expr:
    pass

# Variable reference (x)
@dataclass
class Var(Expr):
    name: str

# Type of types (*)
@dataclass
class Type(Expr):
    pass

# Dependent function types (Pi-types)
@dataclass
class Pi(Expr):
    x: str
    tau1: Expr  # Domain type
    tau2: Expr  # Codomain type

# Function introduction (lambda abstraction)
@dataclass
class Lambda(Expr):
    x: str
    tau1: Expr  # Parameter type
    e2: Expr    # Function body

# Function elimination (application)
@dataclass
class App(Expr):
    e1: Expr  # Function
    e2: Expr  # Argument

# The natural number type
@dataclass
class Nat(Expr):
    pass

# The number zero
@dataclass
class Zero(Expr):
    pass

# Successor of a natural number
@dataclass
class Succ(Expr):
    e: Expr  # Predecessor

# Natural number elimination (recursion)
@dataclass
class ElimNat(Expr):
    e1: Expr  # Motive
    e2: Expr  # Base case
    e3: Expr  # Induction step
    e4: Expr  # Target natural number

# Environment: a list of variable bindings (name, type)
Environment = List[Tuple[str, Expr]]

def fresh_var(name: str, avoid_vars: Set[str]) -> str:
    # Generate a fresh variable name not in avoid_vars
    i = 1
    new_name = f"{name}_{i}"
    while new_name in avoid_vars:
        i += 1
        new_name = f"{name}_{i}"
    return new_name

def free_vars(e: Expr) -> Set[str]:
    # Compute the set of free variables in expression e
    if isinstance(e, Var):
        return {e.name}
    elif isinstance(e, Type):
        return set()
    elif isinstance(e, Pi):
        fv_tau1 = free_vars(e.tau1)
        fv_tau2 = free_vars(e.tau2)
        fv_tau2.discard(e.x)
        return fv_tau1.union(fv_tau2)
    elif isinstance(e, Lambda):
        fv_tau1 = free_vars(e.tau1)
        fv_e2 = free_vars(e.e2)
        fv_e2.discard(e.x)
        return fv_tau1.union(fv_e2)
    elif isinstance(e, App):
        return free_vars(e.e1).union(free_vars(e.e2))
    elif isinstance(e, Nat):
        return set()
    elif isinstance(e, Zero):
        return set()
    elif isinstance(e, Succ):
        return free_vars(e.e)
    elif isinstance(e, ElimNat):
        return free_vars(e.e1).union(free_vars(e.e2), free_vars(e.e3), free_vars(e.e4))
    else:
        raise TypeError(f"Unknown expression: {e}")

def substitute_var(e: Expr, old_name: str, new_name: str) -> Expr:
    # Substitute variable names to avoid capture (Alpha Conversion)
    if isinstance(e, Var):
        if e.name == old_name:
            return Var(new_name)
        else:
            return e
    elif isinstance(e, Type):
        return e
    elif isinstance(e, Pi):
        x1 = e.x
        tau1 = substitute_var(e.tau1, old_name, new_name)
        if x1 == old_name:
            x1 = new_name
        tau2 = substitute_var(e.tau2, old_name, new_name)
        return Pi(x1, tau1, tau2)
    elif isinstance(e, Lambda):
        x1 = e.x
        tau1 = substitute_var(e.tau1, old_name, new_name)
        if x1 == old_name:
            x1 = new_name
        e2 = substitute_var(e.e2, old_name, new_name)
        return Lambda(x1, tau1, e2)
    elif isinstance(e, App):
        e1 = substitute_var(e.e1, old_name, new_name)
        e2 = substitute_var(e.e2, old_name, new_name)
        return App(e1, e2)
    elif isinstance(e, Succ):
        e_inner = substitute_var(e.e, old_name, new_name)
        return Succ(e_inner)
    elif isinstance(e, ElimNat):
        e1 = substitute_var(e.e1, old_name, new_name)
        e2 = substitute_var(e.e2, old_name, new_name)
        e3 = substitute_var(e.e3, old_name, new_name)
        e4 = substitute_var(e.e4, old_name, new_name)
        return ElimNat(e1, e2, e3, e4)
    else:
        return e

def substitute(e1: Expr, x: str, e2: Expr) -> Expr:
    # Perform CAS for e1[x ↦ e2]
    if isinstance(e1, Var):
        if e1.name == x:
            return e2
        else:
            return e1
    elif isinstance(e1, Type):
        return e1
    elif isinstance(e1, Pi):
        x1 = e1.x
        tau1 = substitute(e1.tau1, x, e2)
        if x1 == x:
            # x1 is bound, x is shadowed (Rule: Type-$\Pi$)
            tau2 = e1.tau2
        elif x1 not in free_vars(e2):
            # Safe to substitute in tau2 (Rule: Type-$\Pi$)
            tau2 = substitute(e1.tau2, x, e2)
        else:
            # Need to rename x1 to avoid capture (Alpha Conversion)
            x1_new = fresh_var(x1, free_vars(e1.tau2).union(free_vars(e2)))
            tau2_renamed = substitute_var(e1.tau2, x1, x1_new)
            tau2 = substitute(tau2_renamed, x, e2)
            x1 = x1_new
        return Pi(x1, tau1, tau2)
    elif isinstance(e1, Lambda):
        x1 = e1.x
        tau1 = substitute(e1.tau1, x, e2)
        if x1 == x:
            # x1 is bound, x is shadowed (Rule: Type-$\lambda$)
            e3 = e1.e2
        elif x1 not in free_vars(e2):
            # Safe to substitute in e2 (Rule: Type-$\lambda$)
            e3 = substitute(e1.e2, x, e2)
        else:
            # Need to rename x1 to avoid capture (Alpha Conversion)
            x1_new = fresh_var(x1, free_vars(e1.e2).union(free_vars(e2)))
            e3_renamed = substitute_var(e1.e2, x1, x1_new)
            e3 = substitute(e3_renamed, x, e2)
            x1 = x1_new
        return Lambda(x1, tau1, e3)
    elif isinstance(e1, App):
        e3 = substitute(e1.e1, x, e2)
        e4 = substitute(e1.e2, x, e2)
        return App(e3, e4)
    elif isinstance(e1, Succ):
        e_inner = substitute(e1.e, x, e2)
        return Succ(e_inner)
    elif isinstance(e1, ElimNat):
        e3 = substitute(e1.e1, x, e2)
        e4 = substitute(e1.e2, x, e2)
        e5 = substitute(e1.e3, x, e2)
        e6 = substitute(e1.e4, x, e2)
        return ElimNat(e3, e4, e5, e6)
    else:
        return e1

def alpha_equal(e1: Expr, e2: Expr, mapping=None) -> bool:
    """Check if two expressions are alpha-equivalent."""
    if mapping is None:
        mapping = {}
    
    if isinstance(e1, Var) and isinstance(e2, Var):
        mapped = mapping.get(e1.name, e1.name)
        if mapped != e2.name:
            print(f"Var mismatch: {e1.name} mapped to {mapped} vs {e2.name}")
            return False
        return True
    elif isinstance(e1, Type) and isinstance(e2, Type):
        return True
    elif isinstance(e1, Pi) and isinstance(e2, Pi):
        # Directly map e1.x to e2.x
        mapping_copy = mapping.copy()
        mapping_copy[e1.x] = e2.x
        tau1_eq = alpha_equal(e1.tau1, e2.tau1, mapping_copy)
        tau2_eq = alpha_equal(e1.tau2, e2.tau2, mapping_copy)
        return tau1_eq and tau2_eq
    elif isinstance(e1, Lambda) and isinstance(e2, Lambda):
        # Directly map e1.x to e2.x
        mapping_copy = mapping.copy()
        mapping_copy[e1.x] = e2.x
        tau1_eq = alpha_equal(e1.tau1, e2.tau1, mapping_copy)
        e2_eq = alpha_equal(e1.e2, e2.e2, mapping_copy)
        return tau1_eq and e2_eq
    elif isinstance(e1, App) and isinstance(e2, App):
        e1_eq = alpha_equal(e1.e1, e2.e1, mapping)
        e2_eq = alpha_equal(e1.e2, e2.e2, mapping)
        return e1_eq and e2_eq
    elif isinstance(e1, Nat) and isinstance(e2, Nat):
        return True
    elif isinstance(e1, Zero) and isinstance(e2, Zero):
        return True
    elif isinstance(e1, Succ) and isinstance(e2, Succ):
        return alpha_equal(e1.e, e2.e, mapping)
    elif isinstance(e1, ElimNat) and isinstance(e2, ElimNat):
        e1_eq = alpha_equal(e1.e1, e2.e1, mapping)
        e2_eq = alpha_equal(e1.e2, e2.e2, mapping)
        e3_eq = alpha_equal(e1.e3, e2.e3, mapping)
        e4_eq = alpha_equal(e1.e4, e2.e4, mapping)
        return e1_eq and e2_eq and e3_eq and e4_eq
    else:
        print(f"Expression mismatch: {e1} vs {e2}")
        return False


def type_check(Gamma: Environment, e: Expr) -> Expr:
    # Type checker: type check e in environment Gamma and return its type
    if isinstance(e, Var):
       # Type-Var-Ref
        for name, tau in reversed(Gamma):
            if name == e.name:
                return tau
        raise TypeError(f"Variable {e.name} not found in context")
    elif isinstance(e, Type):
        # Type-$\star$
        return Type()
    elif isinstance(e, Pi):
        # Type-$\Pi$
        tau1_type = type_check(Gamma, e.tau1)
        if not isinstance(tau1_type, Type):
            raise TypeError(f"Domain of Pi type is not a type: {e.tau1}")
        Gamma2 = Gamma.copy()
        Gamma2.append((e.x, e.tau1))
        tau2_type = type_check(Gamma2, e.tau2)
        if not isinstance(tau2_type, Type):
            raise TypeError(f"Codomain of Pi type is not a type: {e.tau2}")
        return Type()
    elif isinstance(e, Lambda):
        # Type-$\lambda$
        tau1_type = type_check(Gamma, e.tau1)
        if not isinstance(tau1_type, Type):
            raise TypeError(f"Parameter type of Lambda is not a type: {e.tau1}")
        Gamma2 = Gamma.copy()
        Gamma2.append((e.x, e.tau1))
        tau2 = type_check(Gamma2, e.e2)
        tau2_type = type_check(Gamma2, tau2)
        if not isinstance(tau2_type, Type):
            raise TypeError(f"Body type of Lambda is not a type: {tau2}")
        return Pi(e.x, e.tau1, tau2)
    elif isinstance(e, App):
        # Type-App
        tau1 = type_check(Gamma, e.e1)
        if isinstance(tau1, Pi):
            tau2 = type_check(Gamma, e.e2)
            # Check Type equivalence using alpha_equal
            if not alpha_equal(tau2, tau1.tau1):
                raise TypeError(f"Type mismatch in application: {tau2} vs {tau1.tau1}")
            # Substitute e.e2 into tau2
            tau_result = substitute(tau1.tau2, tau1.x, e.e2)
            return tau_result
        else:
            raise TypeError(f"Attempting to apply non-function: {e.e1}")
    elif isinstance(e, Nat):
        # Type-$\mathbb{N}$
        return Type()
    elif isinstance(e, Zero):
        # Type-0
        return Nat()
    elif isinstance(e, Succ):
        # Type-$\mathtt{succ}$
        tau = type_check(Gamma, e.e)
        if not isinstance(tau, Nat):
            raise TypeError(f"Type error in Succ argument: expected Nat, got {tau}")
        return Nat()
    elif isinstance(e, ElimNat):
        # Type-$\mathtt{elimNat}$
        # Check Γ ⊢ e₁ : ℕ → ⋆ (Type-Pi Domain and Codomain)
        tau_e1 = type_check(Gamma, e.e1)
        if not (isinstance(tau_e1, Pi) and isinstance(tau_e1.tau1, Nat) and isinstance(tau_e1.tau2, Type)):
            raise TypeError(f"Motive of elimNat is not of type ℕ → ⋆: {e.e1}")
        
        # Check Γ ⊢ e₂ : e₁ 0 (Type-Eval and Type-App)
        e1_zero = App(e.e1, Zero())
        tau_e1_zero = type_check(Gamma, e1_zero)
        tau_e2 = type_check(Gamma, e.e2)
        if not alpha_equal(tau_e2, tau_e1_zero):
            raise TypeError(f"Type mismatch in elimNat base case: {tau_e2} vs {tau_e1_zero}")
        
        # Check Γ ⊢ e₃ : (x : ℕ) → e₁ x → e₁ (succ x) (Type-Pi)
        x = 'x'
        motive_x = App(e.e1, Var(x))
        motive_succ_x = App(e.e1, Succ(Var(x)))
        ind_case_type = Pi(x, Nat(), Pi('_', motive_x, motive_succ_x))
        tau_e3 = type_check(Gamma, e.e3)
        if not alpha_equal(tau_e3, ind_case_type):
            raise TypeError(f"Type mismatch in elimNat inductive case: {tau_e3} vs {ind_case_type}")
        
        # Check Γ ⊢ e₄ : ℕ (Type-Var-Ref)
        tau_e4 = type_check(Gamma, e.e4)
        if not isinstance(tau_e4, Nat):
            raise TypeError(f"Type error in elimNat target: expected Nat, got {tau_e4}")
        
        # The type is e₁ e₄ (Type-App)
        return App(e.e1, e.e4)
    else:
        raise TypeError(f"Unknown expression: {e}")

def eval_expr(e: Expr) -> Expr:
    # Evaluator: simplify expression e according to the evaluation rules
    while True:
        if isinstance(e, App) and isinstance(e.e1, Lambda):
            # Eval-App: (\lambda x. e1) e2 => e1[x ↦ e2]
            e = substitute(e.e1.e2, e.e1.x, e.e2)
        elif isinstance(e, ElimNat):
            if isinstance(e.e4, Zero):
                # Eval- elimNat e1 e2 e3 0 => e2
                e = e.e2
            elif isinstance(e.e4, Succ):
                # Eval- elimNat e1 e2 e3 (succ e4) => e3 e4 (elimNat e1 e2 e3 e4)
                e = App(App(e.e3, e.e4.e), ElimNat(e.e1, e.e2, e.e3, e.e4.e))
            else:
                # Evaluate the target of elimNat
                e4_eval = eval_expr(e.e4)
                if e4_eval != e.e4:
                    # If e4 can be evaluated further, apply Eval-$\mathtt{elimNat}$-target
                    e = ElimNat(e.e1, e.e2, e.e3, e4_eval)
                else:
                    break
        else:
            if isinstance(e, Lambda):
                # Eval-$\lambda$-Body: Evaluate the body of the lambda
                e2_eval = eval_expr(e.e2)
                if e2_eval != e.e2:
                    e = Lambda(e.x, e.tau1, e2_eval)
                else:
                    break
            elif isinstance(e, App):
                # Eval-Rator: Evaluate the function part
                e1_eval = eval_expr(e.e1)
                if e1_eval != e.e1:
                    e = App(e1_eval, e.e2)
                else:
                    # Eval-Rand: Evaluate the argument part
                    e2_eval = eval_expr(e.e2)
                    if e2_eval != e.e2:
                        e = App(e.e1, e2_eval)
                    else:
                        break
            elif isinstance(e, Succ):
                # Eval-$\mathtt{succ}$: Evaluate the inner expression
                e_inner = eval_expr(e.e)
                if e_inner != e.e:
                    e = Succ(e_inner)
                else:
                    break
            elif isinstance(e, Pi):
                # Eval-$\Pi$: Evaluate domain and codomain
                tau1_eval = eval_expr(e.tau1)
                if tau1_eval != e.tau1:
                    e = Pi(e.x, tau1_eval, e.tau2)
                else:
                    tau2_eval = eval_expr(e.tau2)
                    if tau2_eval != e.tau2:
                        e = Pi(e.x, e.tau1, tau2_eval)
                    else:
                        break
            elif isinstance(e, ElimNat):
                # Eval-$\mathtt{elimNat}$: Evaluate components
                e1_eval = eval_expr(e.e1)
                if e1_eval != e.e1:
                    e = ElimNat(e1_eval, e.e2, e.e3, e.e4)
                else:
                    e2_eval = eval_expr(e.e2)
                    if e2_eval != e.e2:
                        e = ElimNat(e.e1, e2_eval, e.e3, e.e4)
                    else:
                        e3_eval = eval_expr(e.e3)
                        if e3_eval != e.e3:
                            e = ElimNat(e.e1, e.e2, e3_eval, e.e4)
                        else:
                            e4_eval = eval_expr(e.e4)
                            if e4_eval != e.e4:
                                e = ElimNat(e.e1, e.e2, e.e3, e4_eval)
                            else:
                                break
            else:
                break
    return e

# Polymorphic Identity Check
def main():
    # Empty environment
    Gamma = []

    # Define polymorphic identity function
    id_expr = Lambda('A', Type(), Lambda('x', Var('A'), Var('x')))

    # Type check the identity function
    try:
        tau_id = type_check(Gamma, id_expr)
        print("Identity function type:", tau_id)
    except TypeError as e:
        print("Type error:", e)

    # Define an application of the identity function to a Nat
    id_nat = App(id_expr, Nat())
    id_nat_zero = App(id_nat, Zero())

    # Type check the application
    try:
        tau_id_nat_zero = type_check(Gamma, id_nat_zero)
        print("Type of id Nat 0:", tau_id_nat_zero)
    except TypeError as e:
        print("Type error:", e)

    # Evaluate the application
    result = eval_expr(id_nat_zero)
    print("Result of id Nat 0:", result)

# (Encapsulate execution)
if __name__ == "__main__":
    main()


