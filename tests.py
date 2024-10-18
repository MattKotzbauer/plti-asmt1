# (Test cases) 

import unittest
from driver import (
    Expr, Var, Type, Pi, Lambda, App, Nat, Zero, Succ, ElimNat,
    Environment, type_check, eval_expr, alpha_equal, substitute
)

class TestEvaluatorTypeChecker(unittest.TestCase):

    def setUp(self):
        # Initialize an empty environment for each test
        self.Gamma: Environment = []

    def test_identity_function(self):
        # Define the polymorphic identity function
        id_expr = Lambda('A', Type(), Lambda('x', Var('A'), Var('x')))

        # Type check the identity function
        tau_id = type_check(self.Gamma, id_expr)
        expected_type = Pi('A', Type(), Pi('x', Var('A'), Var('A')))
        self.assertTrue(alpha_equal(tau_id, expected_type),
                        f"Expected type {expected_type}, got {tau_id}")

        # Define an application of the identity function to Nat
        id_nat = App(id_expr, Nat())
        tau_id_nat = type_check(self.Gamma, id_nat)
        expected_tau_id_nat = Pi('x', Nat(), Nat())
        self.assertTrue(alpha_equal(tau_id_nat, expected_tau_id_nat),
                        f"Expected type {expected_tau_id_nat}, got {tau_id_nat}")

        # Apply id_nat to Zero
        id_nat_zero = App(id_nat, Zero())
        tau_id_nat_zero = type_check(self.Gamma, id_nat_zero)
        expected_tau_id_nat_zero = Nat()
        self.assertTrue(alpha_equal(tau_id_nat_zero, expected_tau_id_nat_zero),
                        f"Expected type {expected_tau_id_nat_zero}, got {tau_id_nat_zero}")

        # Evaluate id_nat_zero
        result = eval_expr(id_nat_zero)
        expected_result = Zero()
        self.assertTrue(alpha_equal(result, expected_result),
                        f"Expected result {expected_result}, got {result}")

    def test_constant_function(self):
        # Define a constant function: const = lambda (A : *) . lambda (x : A) . lambda (y : A). x
        const_expr = Lambda('A', Type(), Lambda('x', Var('A'),
                           Lambda('y', Var('A'), Var('x'))))

        # Type check the constant function
        tau_const = type_check(self.Gamma, const_expr)
        expected_type = Pi('A', Type(),
                           Pi('x', Var('A'),
                              Pi('y', Var('A'), Var('A'))))
        self.assertTrue(alpha_equal(tau_const, expected_type),
                        f"Expected type {expected_type}, got {tau_const}")

        # Apply const to Nat and two Zero
        const_nat = App(App(const_expr, Nat()), Zero())
        const_nat_zero = App(const_nat, Zero())
        tau_const_nat_zero = type_check(self.Gamma, const_nat_zero)
        expected_tau = Nat()
        self.assertTrue(alpha_equal(tau_const_nat_zero, expected_tau),
                        f"Expected type {expected_tau}, got {tau_const_nat_zero}")

        # Evaluate const Nat 0
        result = eval_expr(const_nat_zero)
        expected_result = Zero()
        self.assertTrue(alpha_equal(result, expected_result),
                        f"Expected result {expected_result}, got {result}")

    def test_pi_type(self):
        # Define a Pi-type: (A : *) -> (B : A) -> A
        pi_type = Pi('A', Type(), Pi('B', Var('A'), Var('A')))

        # Type check the Pi-type
        tau_pi = type_check(self.Gamma, pi_type)
        expected_type = Type()
        self.assertTrue(alpha_equal(tau_pi, expected_type),
                        f"Expected type {expected_type}, got {tau_pi}")

    def test_lambda_type_mismatch(self):
        # Define a lambda that returns a Nat: lambda (x : Nat). 0
        bad_lambda = Lambda('x', Nat(), Zero())

        # Type check should pass since Zero() is Nat and lambda expects to return Nat
        tau_lambda = type_check(self.Gamma, bad_lambda)
        expected_type = Pi('x', Nat(), Nat())
        self.assertTrue(alpha_equal(tau_lambda, expected_type),
                        f"Expected type {expected_type}, got {tau_lambda}")

    def test_application_type_error(self):
        # Attempt to apply Zero (which is Nat) as if it were a function
        application = App(Zero(), Zero())

        with self.assertRaises(TypeError):
            type_check(self.Gamma, application)

    def test_succ_evaluation(self):
        # Define succ(0)
        succ_zero = Succ(Zero())

        # Type check succ_zero
        tau_succ_zero = type_check(self.Gamma, succ_zero)
        expected_type = Nat()
        self.assertTrue(alpha_equal(tau_succ_zero, expected_type),
                        f"Expected type {expected_type}, got {tau_succ_zero}")

        # Evaluate succ_zero
        result = eval_expr(succ_zero)
        expected_result = Succ(Zero())
        self.assertTrue(alpha_equal(result, expected_result),
                        f"Expected result {expected_result}, got {result}")

    def test_elim_nat_zero(self):
        # Define elimNat e1 e2 e3 0
        e1 = Pi('x', Nat(), Type())
        e2 = Var('e2')  # Assume e2 has type e1 0
        # Correctly nest App for elimNat e1 e2 e3 x
        e3 = Lambda(
            'x', 
            Nat(), 
            Lambda(
                '_', 
                App(Var('e1'), Var('x')),
                App(
                    App(Var('e1'), Var('x')),
                    App(
                        App(
                            App(Var('elimNat'), Var('e1')),
                            Var('e2')
                        ),
                        Var('e3')
                    )
                )
            )
        )
        elim_nat_zero = ElimNat(e1, e2, e3, Zero())

        # Since e2 and e3 are variables without bindings, type checking should raise an error
        with self.assertRaises(TypeError):
            type_check(self.Gamma, elim_nat_zero)

    def test_nested_lambda(self):
        # Define a nested lambda: lambda (A : *) . lambda (B : A) . lambda (x : B). x
        nested_lambda = Lambda('A', Type(),
                            Lambda('B', Var('A'),
                                Lambda('x', Var('B'), Var('x'))))

        # Type check the nested lambda
        tau_nested = type_check(self.Gamma, nested_lambda)
        expected_type = Pi('A', Type(),
                           Pi('B', Var('A'),
                              Pi('x', Var('B'), Var('B'))))
        self.assertTrue(alpha_equal(tau_nested, expected_type),
                        f"Expected type {expected_type}, got {tau_nested}")

        # Apply the nested lambda to Nat, then to Zero, then to Zero again
        app1 = App(nested_lambda, Nat())
        app2 = App(app1, Zero())
        app3 = App(app2, Zero())
        tau_app3 = type_check(self.Gamma, app3)
        expected_tau = Nat()
        self.assertTrue(alpha_equal(tau_app3, expected_tau),
                        f"Expected type {expected_tau}, got {tau_app3}")

        # Evaluate the expression
        result = eval_expr(app3)
        expected_result = Zero()
        self.assertTrue(alpha_equal(result, expected_result),
                        f"Expected result {expected_result}, got {result}")

    def test_type_star(self):
        # Type-check Type
        tau_type = type_check(self.Gamma, Type())
        expected_type = Type()
        self.assertTrue(alpha_equal(tau_type, expected_type),
                        f"Expected type {expected_type}, got {tau_type}")

    def test_nat_type(self):
        # Type-check Nat
        tau_nat = type_check(self.Gamma, Nat())
        expected_type = Type()
        self.assertTrue(alpha_equal(tau_nat, expected_type),
                        f"Expected type {expected_type}, got {tau_nat}")

    def test_elim_nat_successor(self):
        # Define elimNat e1 e2 e3 (succ 0)
        e1 = Pi('x', Nat(), Type())
        e2 = Var('e2')  # Base case
        # Correctly nest App for elimNat e1 e2 e3 x
        e3 = Lambda(
            'x', 
            Nat(), 
            Lambda(
                '_', 
                App(Var('e1'), Var('x')),
                App(
                    App(Var('e1'), Var('x')),
                    App(
                        App(
                            App(Var('elimNat'), Var('e1')),
                            Var('e2')
                        ),
                        Var('e3')
                    )
                )
            )
        )
        target = Succ(Zero())
        elim_nat_succ = ElimNat(e1, e2, e3, target)

        # Type checking should raise an error due to unbound variables
        with self.assertRaises(TypeError):
            type_check(self.Gamma, elim_nat_succ)

    def test_alpha_equivalence(self):
        # Define two equivalent expressions differing only in bound variable names
        expr1 = Lambda('x', Nat(), Var('x'))
        expr2 = Lambda('y', Nat(), Var('y'))

        self.assertTrue(alpha_equal(expr1, expr2),
                        f"Expressions {expr1} and {expr2} should be alpha-equivalent")

        # Define two non-equivalent expressions
        expr3 = Lambda('x', Nat(), Var('x'))
        expr4 = Lambda('y', Nat(), Var('x'))  # Incorrectly references 'x'

        self.assertFalse(alpha_equal(expr3, expr4),
                         f"Expressions {expr3} and {expr4} should not be alpha-equivalent")


    expr1 = Lambda('x', Nat(), Var('x'))
    expr2 = Lambda('y', Nat(), Var('y'))
    print(alpha_equal(expr1, expr2))


if __name__ == '__main__':
    unittest.main()



