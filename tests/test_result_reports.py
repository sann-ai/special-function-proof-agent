"""Reports preserve the target and distinguish candidates from accepted proofs."""
from pathlib import Path
import json
import tempfile
import unittest
from unittest.mock import patch

from special_function_agent.core import verify
from special_function_agent.parser import parse_identity
from special_function_agent.real_special import default_proof


class ResultReportTests(unittest.TestCase):
    def check_result(self, text, outcome, route='direct'):
        target = parse_identity(text)
        request = {**target, 'proof': default_proof(target, route)}
        return self.check_request(request, outcome)

    def check_request(self, request, outcome):
        target = {k: v for k, v in request.items() if k != 'proof'}
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'run'
            with patch('special_function_agent.real_numeric.diagnose',
                       return_value={'diagnostic': 'no_mismatch_found'}), \
                 patch('special_function_agent.real_special._run_lean', return_value=outcome) as lean:
                result = verify(request, output)
            saved = json.loads((output / 'request.json').read_text())
            self.assertEqual({k: v for k, v in saved.items() if k != 'proof'}, target)
            return result, (output / 'report.md').read_text(), (output / 'certificate.lean').exists(), lean.call_count

    def test_missing_condition_is_reported_without_adopting_it_or_running_lean(self):
        result, report, certificate, calls = self.check_result(
            'Gamma(x+1)=x*Gamma(x); x real', {'accepted': True})
        self.assertEqual(result['status'], 'needs_conditions')
        self.assertIn('x > 0', result['pending_domain_conditions'])
        self.assertIn('確認が必要な条件：', report)
        self.assertIn('x > 0', report)
        self.assertIn('元の入力に追加していません', report)
        self.assertFalse(certificate)
        self.assertEqual(calls, 0)

    def test_timed_out_steps_are_candidates_and_numerical_agreement_is_not_a_proof(self):
        result, report, certificate, calls = self.check_result(
            'Gamma(x+1)=x*Gamma(x); x>0',
            {'accepted': False, 'reason': 'timeout', 'stderr': 'timed out'}, 'steps')
        self.assertEqual(result['status'], 'unresolved')
        self.assertEqual(result['reason'], 'timeout')
        self.assertIn('構造化ステップ候補', report)
        self.assertNotIn('検査済み', report)
        self.assertIn('Lean検査：timeout', report)
        self.assertIn('timed out', report)
        self.assertIn('偽であることを意味しません', report)
        self.assertIn('一致や不一致だけで証明・反証とは判定しません', report)
        self.assertFalse(certificate)
        self.assertEqual(calls, 1)

    def test_missing_lean_environment_has_a_recovery_path(self):
        result, report, certificate, _ = self.check_result(
            'erf(-x)=-erf(x); x real',
            {'accepted': False, 'reason': 'lean_unavailable', 'stderr': 'lake missing'})
        self.assertEqual(result['reason'], 'lean_unavailable')
        self.assertIn('scripts/doctor.py', report)
        self.assertIn('lake missing', report)
        self.assertFalse(certificate)

    def test_audit_failure_is_explained_without_issuing_a_certificate(self):
        result, report, certificate, _ = self.check_result(
            'Gamma(x+1)=x*Gamma(x); x>0',
            {'accepted': False, 'reason': 'audit_rejected', 'audit_error': 'unexpected axiom'})
        self.assertEqual(result['status'], 'unresolved')
        self.assertIn('公理監査に通っていません', report)
        self.assertIn('unexpected axiom', report)
        self.assertFalse(certificate)

    def test_only_accepted_steps_are_labelled_checked_and_point_to_the_certificate(self):
        result, report, certificate, _ = self.check_result(
            'Gamma(x+1)=x*Gamma(x); x>0', {'accepted': True, 'axioms': []}, 'steps')
        self.assertEqual(result['status'], 'proved')
        self.assertTrue(result['full_function_proof'])
        self.assertIn('検査済み', report)
        self.assertIn('形式証明は certificate.lean', report)
        self.assertNotIn('構造化ステップ候補', report)
        self.assertTrue(certificate)

    def test_failed_defined_function_does_not_claim_a_saved_certificate(self):
        from test_defined_integration import source_target
        from special_function_agent.defined_proof import default_proof as defined_plan
        target = source_target()
        result, report, certificate, _ = self.check_request(
            {**target, 'proof': defined_plan(target, 'steps')},
            {'accepted': False, 'reason': 'timeout'})
        self.assertEqual(result['status'], 'unresolved')
        self.assertIn('研究関数の明示定義', report)
        self.assertNotIn('形式証明は certificate.lean', report)
        self.assertNotIn('analysis.json、certificate.lean に保存', report)
        self.assertFalse(certificate)

    def test_failed_research_lemma_application_does_not_claim_a_saved_certificate(self):
        from test_research_proof import gamma_package, gamma_plan
        result, report, certificate, _ = self.check_request(
            gamma_plan(gamma_package()), {'accepted': False, 'reason': 'lean_unavailable'})
        self.assertEqual(result['status'], 'unresolved')
        self.assertIn('研究補題の再利用', report)
        self.assertNotIn('形式証明は certificate.lean', report)
        self.assertNotIn('証明と依存関係は certificate.lean', report)
        self.assertFalse(certificate)


if __name__ == '__main__':
    unittest.main()
