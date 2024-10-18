# test2.py

import unittest
from driver import (
    Expr, Var, Type, Pi, Lambda, App, Nat, Zero, Succ, ElimNat,
    Environment, type_check, eval_expr, alpha_equal, substitute
)

class TestAdditionCommutativity(unittest.TestCase):
    def setUp(self):
        # Initialize an empty environment for each test
        self.Gamma: Environment = []

        # Define the addition function: add : Nat -> Nat -> Nat
        # add x y = elimNat (\z: Nat -> Nat). y (\n: Nat. Succ (add n y)) x
        # Breakdown:
        # - e1: Pi('z', Nat(), Nat()) -- motive
        # - e2: Var('y') -- base case: add 0 y = y
        # - e3: Lambda('n', Nat(), Lambda('_', Pi('z', Nat(), Nat()), Succ(App(App(Var('add'), Var('n')), Var('y')))))
        #   Inductive step: add (Succ n) y = Succ (add n y)
        # - e4: Var('x') -- target natural number

        # Temporarily set 'add' as a variable to allow recursive definition
        # We'll define 'add' in Gamma to reference itself
        self.add_var = ('add', Pi('x', Nat(), Pi('y', Nat(), Nat())))
        self.Gamma.append(self.add_var)

        # Define e1: Pi('z', Nat(), Nat())
        e1 = Pi('z', Nat(), Nat())

        # Define e2: Var('y')
        e2 = Var('y')

        # Define e3: Lambda('n', Nat(), Lambda('_', Pi('z', Nat(), Nat()), Succ(App(App(Var('add'), Var('n')), Var('y')))))
        # This represents the inductive step: add (Succ n) y = Succ (add n y)
        inductive_step = Lambda(
            'n',
            Nat(),
            Lambda(
                '_',
                Pi('z', Nat(), Nat()),
                Succ(App(App(Var('add'), Var('n')), Var('y')))
            )
        )

        # Define e4: Var('x')
        e4 = Var('x')

        # Define the ElimNat expression for add
        self.add_expr = Lambda(
            'x',
            Nat(),
            Lambda(
                'y',
                Nat(),
                ElimNat(e1, e2, inductive_step, e4)
            )
        )

    def test_addition_commutativity(self):
        """
        Test that addition is commutative: add a b == add b a
        We'll test this for several pairs of natural numbers.
        """
        # Define some natural numbers
        zero = Zero()
        one = Succ(zero)
        two = Succ(one)
        three = Succ(two)

        # Define pairs to test commutativity
        test_pairs = [
            (zero, zero),
            (zero, one),
            (one, zero),
            (one, one),
            (one, two),
            (two, one),
            (two, two),
            (two, three),
            (three, two),
            (three, three)
        ]

        for a, b in test_pairs:
            with self.subTest(a=a, b=b):
                # Define add a b
                add_a_b = App(App(self.add_expr, a), b)

                # Define add b a
                add_b_a = App(App(self.add_expr, b), a)

                # Evaluate both expressions
                eval_add_a_b = eval_expr(add_a_b)
                eval_add_b_a = eval_expr(add_b_a)

                # Check that both evaluations result in the same expression
                self.assertTrue(alpha_equal(eval_add_a_b, eval_add_b_a),
                                f"Addition is not commutative for a={a}, b={b}: add a b={eval_add_a_b} != add b a={eval_add_b_a}")

    def test_addition_specific_cases(self):
        """
        Test specific cases of addition to ensure correctness.
        """
        # Define natural numbers
        zero = Zero()
        one = Succ(zero)
        two = Succ(one)
        three = Succ(two)

        # Define test cases as tuples: (a, b, expected_add_a_b)
        test_cases = [
            (zero, zero, zero),
            (zero, one, one),
            (one, zero, one),
            (one, one, two),
            (one, two, three),
            (two, one, three),
            (two, two, Succ(Succ(two))),
            (two, three, Succ(Succ(Succ(two)))),
            (three, two, Succ(Succ(Succ(two)))),
            (three, three, Succ(Succ(Succ(Succ(two)))))
        ]

        for a, b, expected in test_cases:
            with self.subTest(a=a, b=b):
                # Define add a b
                add_a_b = App(App(self.add_expr, a), b)

                # Evaluate add a b
                eval_add_a_b = eval_expr(add_a_b)

                # Check that the evaluation matches the expected result
                self.assertTrue(alpha_equal(eval_add_a_b, expected),
                                f"add({a}, {b}) expected to be {expected}, but got {eval_add_a_b}")

    def test_type_of_addition(self):
        """
        Ensure that the type of the addition function is Nat -> Nat -> Nat.
        """
        # Type check the addition function
        tau_add = type_check(self.Gamma, self.add_expr)

        # Define the expected type: Nat -> Nat -> Nat
        expected_type = Pi('x', Nat(), Pi('y', Nat(), Nat()))

        self.assertTrue(alpha_equal(tau_add, expected_type),
                        f"Expected type {expected_type}, got {tau_add}")

    def test_addition_type_error(self):
        """
        Attempt to type check an incorrect usage of addition to ensure type errors are raised.
        For example, applying add to a Nat and a Type.
        """
        # Define an incorrect argument: Type
        incorrect_arg = Type()

        # Define add Nat Type
        add_nat_type = App(self.add_expr, Nat())
        add_nat_type_incorrect = App(add_nat_type, incorrect_arg)

        # Type checking should raise a TypeError
        with self.assertRaises(TypeError):
            type_check(self.Gamma, add_nat_type_incorrect)

if __name__ == '__main__':
    unittest.main()

