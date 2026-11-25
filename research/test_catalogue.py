import re
"""Check the public research queue and the scope of its analytic targets."""

import json
import unittest
from pathlib import Path
from urllib.parse import urlparse


GAPS = json.loads(Path(__file__).with_name("gaps.json").read_text(encoding="utf-8"))["gaps"]
PROBLEMS = json.loads(Path(__file__).with_name("problems.json").read_text(encoding="utf-8"))


class CatalogueTests(unittest.TestCase):
    def test_problem_tasks_have_unique_names_and_respect_scope(self):
        all_gaps = GAPS + [gap for problem in PROBLEMS.values() for gap in problem["gaps"]]
        for key in ("id", "file", "module"):
            values = [gap[key] for gap in all_gaps]
            self.assertEqual(len(values), len(set(values)), key)
        for slug, problem in PROBLEMS.items():
            self.assertRegex(slug, r"^[a-z]+(?:-[a-z]+)*$")
            self.assertTrue(any(gap.get("parallel") is True for gap in problem["gaps"]), slug)
            for gap in problem["gaps"]:
                with self.subTest(problem=slug, gap=gap["id"]):
                    self.assertRegex(gap["id"], rf"^L-{slug}-[a-z0-9]+(?:-[a-z0-9]+)*$")
                    self.assertLessEqual(len(gap["id"]), 64)
                    name = gap["id"].replace("-", "_")
                    self.assertEqual(gap["file"], f"lean/PEqualNP/Outside/{name}.lean")
                    self.assertEqual(gap["module"], f"PEqualNP.Outside.{name}")
                    self.assertIn(gap["program"], {"foundation", "correlation"})
                    for lang in ("en", "zh"):
                        self.assertTrue(gap["plain_statement"][lang].strip())

    def test_roadmap_links_resolve_within_their_own_problem(self):
        for slug, problem in PROBLEMS.items():
            ids = {gap["id"] for gap in problem["gaps"]}
            for stage in problem["roadmap"]:
                with self.subTest(problem=slug, stage=stage["en"][0]):
                    self.assertTrue(stage["tasks"])
                    for task in stage["tasks"]:
                        self.assertIn(task["id"], ids)
                        for lang in ("zh", "en"):
                            self.assertTrue(task[lang].strip())

    def test_lease_ids_and_pr_paths(self):
        for key in ("id", "file", "module"):
            values = [gap[key] for gap in GAPS]
            self.assertEqual(len(values), len(set(values)), key)
        for gap in GAPS:
            with self.subTest(gap=gap["id"]):
                self.assertRegex(gap["id"], r"^L-goldbach-[a-z0-9]+(?:-[a-z0-9]+)*$")
                self.assertLessEqual(len(gap["id"]), 64)
                name = gap["id"].replace("-", "_")
                self.assertEqual(gap["module"], f"PEqualNP.Outside.{name}")
                self.assertEqual(gap["file"], f"lean/PEqualNP/Outside/{name}.lean")
                for lang in ("en", "zh"):
                    self.assertTrue(gap["plain_statement"][lang].strip())

    def test_goldbach_tracks_separate_sublemmas_from_the_endpoint(self):
        tracks = json.loads(Path(__file__).with_name("gaps.json").read_bytes())["tracks"]
        keys = {t["id"] for t in tracks}
        tasks = [g for g in GAPS if "track" in g]
        self.assertGreaterEqual(len(tasks), 100)
        self.assertEqual(len({g["statement"] for g in tasks}), len(tasks))
        self.assertEqual({g["track"] for g in tasks}, keys)
        for track in tracks:
            self.assertTrue(set(track["feeds"]) <= keys)
        self.assertTrue(all(g["role"] in {"lemma", "conditional", "target"} for g in tasks))
        self.assertEqual([g["id"] for g in GAPS if g.get("role") == "endpoint"],
                         ["L-goldbach-binary-pointwise-positivity"])

    def test_new_route_labels_and_dependencies(self):
        from graphlib import TopologicalSorter

        by_id = {g["id"]: g for g in GAPS}
        graph = TopologicalSorter()
        seen = set()
        for track, prefix in (("theta-reflection", "TH"), ("odd-character-interference", "OC")):
            cohort = [g for g in GAPS if g.get("track") == track]
            self.assertTrue(cohort)
            for g in cohort:
                title = g["plain_statement"]
                match = re.search(rf" · ({prefix}-[0-9]{{4}}) · ", title["zh"])
                self.assertTrue(match, g["id"])
                serial = match.group(1)
                self.assertNotIn(serial, seen)
                seen.add(serial)
                self.assertTrue(title["zh"].startswith("新路线 · "))
                self.assertIn(serial, title["en"])
                for dep in g["depends_on"]:
                    self.assertIn(dep, by_id)
                graph.add(g["id"], *g["depends_on"])
        list(graph.static_order())

    def test_mellin_windows_allow_nonzero_compactly_supported_functions(self):
        # At the pinned Mathlib revision the top ContDiff order denotes analyticity.
        mellin = {g["id"]: g["statement"] for g in GAPS
                  if g["id"].startswith("L-goldbach-mellin-")}
        witness = mellin["L-goldbach-mellin-admissible-witness"]
        self.assertIn("∃ φ : ℝ → ℝ, Adm φ", witness)
        self.assertIn("φ u=1", witness)
        for statement in mellin.values():
            self.assertNotRegex(statement, r"ContDiff\s+ℝ\s+⊤")

    def test_analytic_programs_and_context(self):
        self.assertEqual({g["program"] for g in GAPS},
                         {"foundation", "grh", "correlation", "exceptions"})
        for gap in GAPS:
            with self.subTest(gap=gap["id"]):
                self.assertNotIn("shard", gap)
                self.assertNotIn("coverage-", gap["id"])
                self.assertTrue(gap["brief"]["zh"].strip())
                self.assertTrue(gap["brief"]["en"].strip())
                source = urlparse(gap["source"])
                self.assertEqual(source.scheme, "https")
                self.assertTrue(source.netloc)
                self.assertIsInstance(gap.get("parallel", False), bool)

    def test_conditional_analytic_claims_preserve_their_inputs(self):
        by_id = {g["id"]: g["statement"] for g in GAPS}
        for suffix in ("rh-zeta-zero-sum", "rh-short-interval-large"):
            self.assertTrue(by_id[f"L-goldbach-{suffix}"].startswith("RiemannHypothesis →"))
        for suffix in ("grh-progression-error", "grh-goldbach-exception-density"):
            claim = by_id[f"L-goldbach-{suffix}"]
            self.assertTrue(claim.startswith("(∀ (Q : ℕ) [NeZero Q]"))
            self.assertIn("DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2) →", claim)

    def test_final_target_has_all_even_inputs_and_only_prime_weights(self):
        target = next(g for g in GAPS if g["id"] == "L-goldbach-binary-pointwise-positivity")
        self.assertTrue(target["parallel"])
        self.assertEqual(
            target["statement"],
            "∀ n : ℕ, 4 ≤ n → Even n → let w : ℕ → ℝ := fun k => "
            "if Nat.Prime k then Real.log (k : ℝ) else 0; "
            "0 < Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p))",
        )


if __name__ == "__main__":
    unittest.main()
