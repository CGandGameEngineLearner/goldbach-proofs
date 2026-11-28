import Mathlib

/-!
This split isolates the logarithmic union loss from the analytic input.
PR #4220 provides the background union-of-shifts strategy, with a weaker
exception exponent and only positivity of the representation count:
https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/4220
Here each shift has exponent 37/50; absorbing the number of shifts by
X^(1/100) gives exactly 3/4. The analytic premise is uniform in the shift.
-/

open Finset

-- child 1 zh: 对每个允许的二幂移位，一致地以 C X^(37/50) 控制二素数表示数低于 c X/log²X 的偶中心数。
-- child 1 en: Uniformly bound the low-representation exceptional centers for each allowed shift by C X^(37/50).
-- child 2 zh: 对充分大的自然数 X，允许的二幂移位个数 floor(log₂X/2) 不超过 X^(1/100)。
-- child 2 en: For all sufficiently large natural X, floor(log₂X/2) is at most X^(1/100).

theorem Conjectures.Cuts.Cut84746305524cdde26851e303
    (hsingle : by
      classical
      exact let G := fun m : ℕ => ((Finset.Icc 2 m).filter
        (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card;
        ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ T : ℕ, ∀ X ≥ T,
          ∀ e ∈ Finset.Icc 1 (Nat.log 2 X / 2),
            (((Finset.Ico X (2*X)).filter (fun n => Even n ∧
              (G (n-2^e):ℝ) < c*(X:ℝ)/(Real.log (X:ℝ))^2)).card : ℝ) ≤
                C * (X:ℝ)^((37:ℝ)/50))
    (hlog : ∃ T : ℕ, ∀ X ≥ T,
      (Nat.log 2 X / 2 : ℕ) ≤ (X:ℝ)^((1:ℝ)/100))
 : (
by
  classical
  exact let G := fun m : ℕ => ((Finset.Icc 2 m).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card; ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ T : ℕ, ∀ X ≥ T, let L := Nat.log 2 X / 2; let E := (Finset.Ico X (2*X)).filter (fun n => Even n ∧ ∃ e ∈ Finset.Icc 1 L, (G (n-2^e):ℝ) < c*(X:ℝ)/(Real.log (X:ℝ))^2); (E.card:ℝ) ≤ C*(X:ℝ)^((3:ℝ)/4)
) := by
  classical
  dsimp only at hsingle ⊢
  obtain ⟨c, C, hc, hC, T, hT⟩ := hsingle
  obtain ⟨U, hU⟩ := hlog
  refine ⟨c, C, hc, hC, max (max T U) 1, ?_⟩
  intro X hX
  have hTX : T ≤ X := (le_max_left T U).trans ((le_max_left (max T U) 1).trans hX)
  have hUX : U ≤ X := (le_max_right T U).trans ((le_max_left (max T U) 1).trans hX)
  have hX1 : 1 ≤ X := (le_max_right (max T U) 1).trans hX
  have hXp : (0:ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  let G := fun m : ℕ => ((Finset.Icc 2 m).filter
    (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card
  let L := Nat.log 2 X / 2
  let I := Finset.Icc 1 L
  let E := fun e => (Finset.Ico X (2*X)).filter (fun n => Even n ∧
    (G (n-2^e):ℝ) < c*(X:ℝ)/(Real.log (X:ℝ))^2)
  have hunion : ((Finset.Ico X (2*X)).filter (fun n => Even n ∧
      ∃ e ∈ Finset.Icc 1 L, (G (n-2^e):ℝ) < c*(X:ℝ)/(Real.log (X:ℝ))^2)) =
        I.biUnion E := by
    ext n
    simp only [mem_filter, mem_biUnion, E, I]
    constructor
    · rintro ⟨hn, hEven, e, he, hbad⟩
      exact ⟨e, he, hn, hEven, hbad⟩
    · rintro ⟨e, he, hn, hEven, hbad⟩
      exact ⟨hn, hEven, e, he, hbad⟩
  change (((Finset.Ico X (2*X)).filter (fun n => Even n ∧
      ∃ e ∈ Finset.Icc 1 L, (G (n-2^e):ℝ) < c*(X:ℝ)/(Real.log (X:ℝ))^2)).card : ℝ) ≤ _
  rw [hunion]
  have hcard : ((I.biUnion E).card:ℝ) ≤ ∑ e ∈ I, ((E e).card:ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  calc
    _ ≤ ∑ e ∈ I, ((E e).card:ℝ) := hcard
    _ ≤ ∑ _e ∈ I, C*(X:ℝ)^((37:ℝ)/50) := by
      apply Finset.sum_le_sum
      intro e he
      exact hT X hTX e he
    _ = (L:ℝ) * (C*(X:ℝ)^((37:ℝ)/50)) := by simp [I]
    _ ≤ (X:ℝ)^((1:ℝ)/100) * (C*(X:ℝ)^((37:ℝ)/50)) :=
      mul_le_mul_of_nonneg_right (hU X hUX)
        (mul_nonneg hC.le (Real.rpow_nonneg hXp.le _))
    _ = C * (X:ℝ)^((1:ℝ)/100 + (37:ℝ)/50) := by
      rw [Real.rpow_add hXp]
      ring
    _ = C * (X:ℝ)^((3:ℝ)/4) := by norm_num
