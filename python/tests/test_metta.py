import unittest
from unittest.mock import patch

from hyperon import *

class MettaTest(unittest.TestCase):

    def test_context_import_failure_is_an_exception_and_rolls_back_exports(self):
        from hyperon.runner import RunContext
        metta = MeTTa(env_builder=Environment.test_env())
        export_calls = 0

        def refusing_export(tokenizer, runner):
            nonlocal export_calls
            export_calls += 1
            tokenizer.register_token('private-export', lambda _: S('exported'))
            if export_calls > 1:
                raise RuntimeError('export refused')

        dependency = metta.load_module_direct_from_func('refusing-export', refusing_export)

        def checking_context(loader_func, path, c_context):
            context = RunContext(c_context)
            context.init_self_module(GroundingSpaceRef(), None)
            with self.assertRaisesRegex(RuntimeError, 'export refused'):
                context.import_dependency(dependency)
            self.assertEqual(SExprParser('private-export').parse(context.tokenizer()), S('private-export'))
            with self.assertRaisesRegex(RuntimeError, 'no-such-module'):
                context.load_module('no-such-module')

        with patch('hyperon.runner._priv_load_module', side_effect=checking_context):
            module = metta.load_module_direct_from_func('checking-context-errors', lambda *_: None)
        self.assertTrue(module.is_valid())
        self.assertEqual(export_calls, 2)
        self.assertEqual(metta.run('!(+ 2 3)'), [[ValueAtom(5)]])

    def test_embedded_nul_in_error_message_does_not_abort(self):
        metta = MeTTa(env_builder=Environment.custom_env(is_test=True))
        rows = metta.run(r'!(register-module! "bad\x00path")')
        self.assertTrue(atom_is_error(rows[0][0]))
        self.assertIn('NUL byte', str(rows[0][0]))

        def failing_loader(tokenizer, runner):
            raise RuntimeError('before\0after')

        with self.assertRaises(RuntimeError) as failure:
            metta.load_module_direct_from_func('nul-error-loader', failing_loader)
        self.assertIn(r'before\0after', str(failure.exception))
        self.assertEqual(metta.run('!(+ 2 3)'), [[ValueAtom(5)]])

    def test_unicode_decimal_tokens_and_comparison_boundaries(self):
        metta = MeTTa(env_builder=Environment.test_env())
        self.assertEqual(metta.run('!(+ ٣ １２) ! 1٣ ! 𝟠 ! -۹ ! ١2.۵e-۱'),
            [[ValueAtom(15)], [ValueAtom(13)], [ValueAtom(8)], [ValueAtom(-9)], [ValueAtom(1.25)]])
        self.assertEqual(metta.run('!(== 9007199254740993 9007199254740992.0) !(> 9007199254740993 9007199254740992.0)'),
            [[ValueAtom(False)], [ValueAtom(True)]])
        self.assertEqual(metta.parse_single('²'), S('²'))

    def test_nul_string_is_not_truncated_by_c_string_serialization(self):
        metta = MeTTa(env_builder=Environment.test_env())
        atom = metta.parse_single(r'"before\x00after"')
        self.assertEqual(str(atom), r'"before\0after"')
        with self.assertRaisesRegex(RuntimeError, 'Could not convert atom'):
            atom.get_object()
        self.assertEqual(metta.run('!(+ 2 3)'), [[ValueAtom(5)]])

    def test_long_atom_rendering_retains_the_complete_value(self):
        name = 'long-' + 'α' * 5000
        self.assertEqual(str(S(name)), name)

    def test_cyclic_states_can_be_printed_compared_and_mutated(self):
        metta = MeTTa(env_builder=Environment.test_env())
        metta.run('!(bind! &left (new-state (leaf))) !(bind! &right (new-state (leaf)))')
        rows = metta.run('!(change-state! &left (wrap &left)) !(change-state! &right (wrap &right))')
        self.assertEqual(str(rows[0][0]), '(State (wrap (State <cycle>)))')
        self.assertEqual(metta.run('!(== &left &right)'), [[ValueAtom(True)]])
        metta.run('!(change-state! &right (other &right))')
        self.assertEqual(metta.run('!(== &left &right)'), [[ValueAtom(False)]])
        metta.run('!(change-state! &left (leaf)) !(change-state! &right (leaf))')
        self.assertEqual(metta.run('!(get-state &left)'), [[E(S('leaf'))]])

    def test_type_depth_limit_and_positive_goal_search(self):
        metta = MeTTa(env_builder=Environment.test_env())
        metta.run('(: a (F x)) (:< (F $x) (F (F $x))) (: f (-> (F (F x)) Ok)) (= (f $x) accepted) !(pragma! max-type-depth 2)')
        self.assertEqual(metta.run('!(f a)'), [[S('accepted')]])
        error = E(S('Error'), S('a'), E(S('TypeSearchLimit'), ValueAtom(2)))
        self.assertEqual(metta.run('!(get-type a)'), [[error]])
        self.assertEqual(metta.run('!(get-type-space &self a)'), [[error]])
        self.assertEqual(metta.run('(: g (-> Missing Ok)) !(g a)'), [[error]])
        self.assertEqual(metta.run('!(+ 2 3)'), [[ValueAtom(5)]])

    def test_delete_uninitialized_runner(self):
        runner = MeTTa.__new__(MeTTa)

        runner.__del__()

    def test_register_token_with_invalid_regex(self):
        metta = MeTTa(env_builder=Environment.test_env())

        with self.assertRaises(RuntimeError):
            metta.register_token("(unclosed", lambda token: S("x"))

        self.assertEqual(metta.run("!(+ 1 2)"), [[ValueAtom(3)]])

    def test_adding_tokens_while_parsing(self):
        metta = MeTTa(env_builder=Environment.test_env())

        atom = metta.parse_single('(A B)')
        self.assertEqual(atom, E(S('A'), S('B')))

        metta.register_atom('A', S('C'))
        atom = metta.parse_single('(A B)')
        self.assertEqual(atom, E(S('C'), S('B')))

        metta.register_atom('A', S('F'))
        atom = metta.parse_single('(A B)')
        self.assertEqual(atom, E(S('F'), S('B')))

    def test_metta_runner(self):
        program = '''
            (= (And T T) T)
            (= (frog $x)
                (And (croaks $x)
                     (eat_flies $x)))
            (= (croaks Fritz) T)
            (= (eat_flies Fritz) T)
            (= (green $x) (frog $x))
            !(green Fritz)
        '''
        runner = MeTTa(env_builder=Environment.test_env())
        result = runner.run(program)

        self.assertEqual([[S('T')]], result)

    def test_metta_evaluate_atom(self):
        program = '''
            (= (And T T) T)
            (= (frog $x)
                (And (croaks $x)
                     (eat_flies $x)))
            (= (croaks Fritz) T)
            (= (eat_flies Fritz) T)
            (= (green $x) (frog $x))
        '''
        runner = MeTTa(env_builder=Environment.test_env())
        runner.run(program)
        result = runner.evaluate_atom(E(S('green'), S('Fritz')))

        self.assertEqual([S('T')], result)

    def test_incremental_runner(self):
        program = '''
            !(+ 1 (+ 2 (+ 3 4)))
        '''
        runner = MeTTa(env_builder=Environment.test_env())
        runner_state = RunnerState(runner, program)

        step_count = 0
        while not runner_state.is_complete():
            runner_state.run_step()
            step_count += 1

        results = runner_state.current_results()
        self.assertEqual(repr(results), "[[10]]")

    def test_gnd_type_error(self):
        program = '''
          !(+ 2 "String")
        '''
        runner = MeTTa(env_builder=Environment.test_env())
        result = runner.run(program)

        self.assertEqual(runner.run('!(Error (+ 2 "String") (BadArgType 2 Number String))'), result)

    def test_runner_error(self):
        program = '''
          !(+ 2 3
        '''
        runner = MeTTa(env_builder=Environment.test_env())
        try:
            runner.run(program)
            self.assertTrue(False, "Parse error expected")
        except RuntimeError as e:
            self.assertEqual(e.args[0], 'Unexpected end of expression')

    def test_match_with_rust_grounded_atom(self):
        program = '''
          ; True is used as a Python grounded object
          (grounded True)
          ; import! is used as a Rust grounded object which can be
          ; received from Python
          !(match &self (grounded import!) Ok)
        '''
        runner = MeTTa(env_builder=Environment.test_env())
        result = runner.run(program)

        self.assertEqual([[]], result)

    def test_metta_evaluate_atom_using_stdlib(self):
        program = '''
            (= (f) (let ($x $y) (A B) $x))
        '''
        runner = MeTTa(env_builder=Environment.test_env())
        runner.run(program)

        result = runner.run('!(f)')
        self.assertEqual([[S('A')]], result)

        result = runner.evaluate_atom(E(S('f')))
        self.assertEqual([S('A')], result)
