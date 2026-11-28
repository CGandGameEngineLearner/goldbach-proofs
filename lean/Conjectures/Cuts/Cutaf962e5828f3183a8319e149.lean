import Mathlib

/-!
Separate the analytic abundance estimate on one common interval from
the finite translation step. The latter is uniform in an arbitrary badness
predicate and uses the injective map n -> n - 2^e.
This refines the single-shift input of accepted PR #4458:
https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/4458
-/

-- child 1 zh: 在共同区间 [X/2,2X) 中，以 C X^(37/50) 控制二素数表示数低于 c X/log²X 的偶目标数。
-- child 1 en: Bound low-representation even targets in the common interval [X/2,2X) by C X^(37/50).
-- child 2 zh: 对任意性质 P，将允许的二幂移位异常集单射到共同区间的未移位偶目标集合，得到基数上界。
-- child 2 en: For every predicate P, inject each allowed binary-shift exceptional set into the unshifted even targets in the common interval.

set_option maxHeartbeats 800000 in
theorem Conjectures.Cuts.Cutaf962e5828f3183a8319e149
    (hglobal : by
      classical
      exact let G := fun m : ℕ => ((Finset.Icc 2 m).filter
        (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card;
        ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ T : ℕ, ∀ X ≥ T,
          (((Finset.Ico (X/2) (2*X)).filter (fun m => Even m ∧
            (G m:ℝ) < c*(X:ℝ)/(Real.log (X:ℝ))^2)).card : ℝ) ≤
              C*(X:ℝ)^((37:ℝ)/50))
    (htransport : by
      classical
      exact ∀ X e : ℕ, 4 ≤ X → e ∈ Finset.Icc 1 (Nat.log 2 X / 2) →
        ∀ P : ℕ → Prop, ∀ [DecidablePred P],
          ((Finset.Ico X (2*X)).filter (fun n => Even n ∧ P (n-2^e))).card ≤
            ((Finset.Ico (X/2) (2*X)).filter (fun m => Even m ∧ P m)).card) : (
have x1 : ℕ → ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.Icc (2 : ℕ) x1 | Nat.Prime x2 ∧ Nat.Prime (x1 - x2)}.card; ∃ (x2 : ℝ) (x3 : ℝ), (0 : ℝ) < x2 ∧ (0 : ℝ) < x3 ∧ ∃ (x4 : ℕ), ∀ x5 ≥ x4, ∀ x7 ∈ Finset.Icc (1 : ℕ) (Nat.log (2 : ℕ) x5 / (2 : ℕ)), ↑{x9 ∈ Finset.Ico x5 ((2 : ℕ) * x5) | Even x9 ∧ ↑(x1 (x9 - (2 : ℕ) ^ x7)) < x2 * ↑x5 / Real.log ↑x5 ^ (2 : ℕ)}.card ≤ x3 * ↑x5 ^ (37 / 50 : ℝ)
) := by
  classical
  dsimp only at hglobal ⊢
  obtain ⟨c, C, hc, hC, T, hT⟩ := hglobal
  refine ⟨c, C, hc, hC, max T 4, ?_⟩
  intro X hX e he
  have hTX : T ≤ X := (le_max_left T 4).trans hX
  have hX4 : 4 ≤ X := (le_max_right T 4).trans hX
  refine le_trans ?_ (hT X hTX)
  exact Nat.cast_le.mpr (htransport X e hX4 he (fun m =>
    ((((Finset.Icc 2 m).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card):ℝ) <
      c*(X:ℝ)/(Real.log (X:ℝ))^2))
