import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity

/-!
Type II bound in terms of frequency differences.

Cauchy-Schwarz controls the outer coefficient sequence. For each inner row,
the squared norm is expanded exactly as a bilinear sum. The two product
cutoffs meet in an initial segment of the m-block; on that segment the phase
reduces to powers of exp(2 pi i (k-l)t). The finite geometric-series bound
handles both the resonant and nonresonant cases, including empty blocks.
-/


namespace TypeIIBlock

/-- A geometric prefix on the unit circle, with powers starting at zero, is
bounded by its length or by the distance from `z` to one. -/
theorem geom_prefix_norm_le (z : ℂ) (n : ℕ) (hz : ‖z‖ = 1) :
    ‖∑ j ∈ Finset.range n, z ^ j‖ ≤
      if z = 1 then (n : ℝ) else min (n : ℝ) (2 / ‖1 - z‖) := by
  split_ifs with hz1
  · subst z
    simp
  · refine le_min ?_ ?_
    · calc
        ‖∑ j ∈ Finset.range n, z ^ j‖
            ≤ ∑ j ∈ Finset.range n, ‖z ^ j‖ := norm_sum_le _ _
        _ = ∑ _j ∈ Finset.range n, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro j _hj
          simp [norm_pow, hz]
        _ = (n : ℝ) := by simp
    · have hsub : 1 - z ≠ 0 := by
        intro h
        apply hz1
        linear_combination -h
      have hden : 0 < ‖1 - z‖ := norm_pos_iff.mpr hsub
      have hgeom := geom_sum_mul_neg z n
      have hnum : ‖1 - z ^ n‖ ≤ 2 := by
        calc
          ‖1 - z ^ n‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ n‖ := norm_sub_le _ _
          _ = 2 := by
            rw [norm_pow, hz, one_pow]
            norm_num
      apply (le_div_iff₀ hden).mpr
      calc
        ‖∑ j ∈ Finset.range n, z ^ j‖ * ‖1 - z‖
            = ‖(∑ j ∈ Finset.range n, z ^ j) * (1 - z)‖ := by
              rw [norm_mul]
        _ = ‖1 - z ^ n‖ := by rw [hgeom]
        _ ≤ 2 := hnum

/-- A block of consecutive powers on the unit circle has length at most `H`
and, away from `z = 1`, has the two-ended geometric-series bound.  This also
covers the empty block when `q ≤ p`. -/
theorem typeII_block_norm_le (z : ℂ) (p q H : ℕ) (hz : ‖z‖ = 1)
    (hH : q - p ≤ H) :
    ‖∑ m ∈ Finset.Ico p q, z ^ m‖ ≤
      if z = 1 then (H : ℝ) else min (H : ℝ) (2 / ‖1 - z‖) := by
  have hshift :
      (∑ m ∈ Finset.Ico p q, z ^ m) =
        z ^ p * ∑ j ∈ Finset.range (q - p), z ^ j := by
    rw [Finset.sum_Ico_eq_sum_range (fun m => z ^ m) p q]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [pow_add]
  calc
    ‖∑ m ∈ Finset.Ico p q, z ^ m‖
        = ‖z ^ p * ∑ j ∈ Finset.range (q - p), z ^ j‖ := by rw [hshift]
    _ = ‖∑ j ∈ Finset.range (q - p), z ^ j‖ := by
      rw [norm_mul, norm_pow, hz, one_pow, one_mul]
    _ ≤ if z = 1 then ((q - p : ℕ) : ℝ) else
        min ((q - p : ℕ) : ℝ) (2 / ‖1 - z‖) := geom_prefix_norm_le z (q - p) hz
    _ ≤ if z = 1 then (H : ℝ) else min (H : ℝ) (2 / ‖1 - z‖) := by
      split_ifs with hz1
      · exact_mod_cast hH
      · exact min_le_min (by exact_mod_cast hH) le_rfl

end TypeIIBlock


namespace TypeIIMainDraft

noncomputable section

open scoped BigOperators
open Complex

/-- The additive character used for the Type II phase. -/
def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- Geometric cancellation budget for a length-`H` block. -/
def cap (H : ℕ) (x : ℝ) : ℝ :=
  if E x = 1 then (H : ℝ) else min (H : ℝ) (2 / ‖1 - E x‖)

/-- The dyadic block of `m`-indices. -/
def block (M H : ℕ) : Finset ℕ := Finset.Ico M (M + H)

/-- The endpoint through which the congruence `m * k ≤ N` can hold. -/
def cutoff (N M H k : ℕ) : ℕ := if k = 0 then M + H else N / k + 1

/-- The common endpoint for two simultaneous congruence conditions.  The upper
cap by `M + H` keeps the block length at most `H`. -/
def pairCutoff (N M H k l : ℕ) : ℕ :=
  min (M + H) (min (cutoff N M H k) (cutoff N M H l))

/-- One summand in the inner Type II sum. -/
def step (N : ℕ) (b : ℕ → ℂ) (t : ℝ) (m k : ℕ) : ℂ :=
  if m * k ≤ N then b k * E ((m : ℝ) * k * t) else 0

/-- The complete inner sum at one `m`. -/
def row (N : ℕ) (K : Finset ℕ) (b : ℕ → ℂ) (t : ℝ) (m : ℕ) : ℂ :=
  ∑ k ∈ K, step N b t m k

/-- The `k,l` coefficient after summing the `m`-dependent product. -/
def pairSum (N M H : ℕ) (b : ℕ → ℂ) (t : ℝ) (k l : ℕ) : ℂ :=
  ∑ m ∈ block M H, step N b t m k * star (step N b t m l)

theorem norm_E (x : ℝ) : ‖E x‖ = 1 := by
  unfold E
  simpa only [mul_comm] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)

theorem E_add (x y : ℝ) : E (x + y) = E x * E y := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem conj_E (x : ℝ) : star (E x) = E (-x) := by
  unfold E
  change (starRingEnd ℂ) (Complex.exp (↑(2 * Real.pi * x) * Complex.I)) =
    Complex.exp (↑(2 * Real.pi * -x) * Complex.I)
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [show (2 * Real.pi * -x : ℝ) = -(2 * Real.pi * x) by ring]
  push_cast
  ring

theorem E_nat_mul (n : ℕ) (x : ℝ) : E ((n : ℝ) * x) = E x ^ n := by
  unfold E
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem E_int_mul (n : ℤ) (x : ℝ) : E ((n : ℝ) * x) = E x ^ n := by
  unfold E
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem phase_mul_conj (m k l : ℕ) (t : ℝ) :
    E ((m : ℝ) * k * t) * star (E ((m : ℝ) * l * t)) =
      E (((k : ℝ) - l) * t) ^ m := by
  calc
    E ((m : ℝ) * k * t) * star (E ((m : ℝ) * l * t))
        = E ((m : ℝ) * k * t) * E (-((m : ℝ) * l * t)) := by rw [conj_E]
    _ = E ((m : ℝ) * k * t + -((m : ℝ) * l * t)) := by rw [← E_add]
    _ = E ((m : ℝ) * (((k : ℝ) - l) * t)) := by
      congr 1
      ring
    _ = E (((k : ℝ) - l) * t) ^ m := E_nat_mul m (((k : ℝ) - l) * t)

theorem step_mul_star (N m k l : ℕ) (b : ℕ → ℂ) (t : ℝ) :
    step N b t m k * star (step N b t m l) =
      if m * k ≤ N ∧ m * l ≤ N then
        b k * star (b l) * E (((k : ℝ) - l) * t) ^ m
      else 0 := by
  by_cases hk : m * k ≤ N <;> by_cases hl : m * l ≤ N <;>
    simp [step, hk, hl]
  calc
    b k * E ((m : ℝ) * k * t) *
        (star (b l) * star (E ((m : ℝ) * l * t)))
        = b k * star (b l) *
            (E ((m : ℝ) * k * t) * star (E ((m : ℝ) * l * t))) := by ring
    _ = b k * star (b l) * E (((k : ℝ) - l) * t) ^ m := by
      rw [phase_mul_conj]

theorem mem_active_iff_lt_cutoff (N M H m k : ℕ) (hm : m ∈ block M H) :
    m * k ≤ N ↔ m < cutoff N M H k := by
  by_cases hk : k = 0
  · subst k
    simp only [mul_zero, zero_le, true_iff]
    simpa [cutoff, block] using (Finset.mem_Ico.mp hm).2
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    rw [cutoff, ite_eq_right hk]
    constructor
    · intro h
      have hmle : m ≤ N / k := (Nat.le_div_iff_mul_le hkpos).mpr h
      omega
    · intro hlt
      have hmle : m ≤ N / k := by omega
      exact (Nat.le_div_iff_mul_le hkpos).mp hmle

theorem active_pair_iff_lt_pairCutoff (N M H m k l : ℕ) (hm : m ∈ block M H) :
    (m * k ≤ N ∧ m * l ≤ N) ↔ m < pairCutoff N M H k l := by
  rw [mem_active_iff_lt_cutoff N M H m k hm,
    mem_active_iff_lt_cutoff N M H m l hm]
  rw [pairCutoff, Nat.lt_min, Nat.lt_min]
  have hw : m < M + H := (Finset.mem_Ico.mp hm).2
  tauto

theorem pairCutoff_le_window (N M H k l : ℕ) :
    pairCutoff N M H k l ≤ M + H := by
  simp [pairCutoff]

theorem pairCutoff_sub_le (N M H k l : ℕ) :
    pairCutoff N M H k l - M ≤ H := by
  have h := pairCutoff_le_window N M H k l
  omega

theorem pair_sum_eq_coeff_block (N M H k l : ℕ) (b : ℕ → ℂ) (t : ℝ) :
    pairSum N M H b t k l =
      b k * star (b l) *
        ∑ m ∈ Finset.Ico M (pairCutoff N M H k l),
          E (((k : ℝ) - l) * t) ^ m := by
  let active : ℕ → Prop := fun m => m * k ≤ N ∧ m * l ≤ N
  have hfilter :
      (block M H).filter active = Finset.Ico M (pairCutoff N M H k l) := by
    ext m
    simp only [block, Finset.mem_filter, Finset.mem_Ico, active]
    constructor
    · rintro ⟨hm, hcond⟩
      have hmblock : m ∈ block M H := Finset.mem_Ico.mpr hm
      exact ⟨hm.1,
        (active_pair_iff_lt_pairCutoff N M H m k l hmblock).1 hcond⟩
    · rintro ⟨hmM, hmq⟩
      have hmblock : m ∈ block M H := by
        exact Finset.mem_Ico.mpr ⟨hmM,
          lt_of_lt_of_le hmq (pairCutoff_le_window N M H k l)⟩
      exact ⟨Finset.mem_Ico.mp hmblock,
        (active_pair_iff_lt_pairCutoff N M H m k l hmblock).2 hmq⟩
  calc
    pairSum N M H b t k l
        = ∑ m ∈ (block M H).filter active,
            b k * star (b l) * E (((k : ℝ) - l) * t) ^ m := by
          rw [pairSum, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro m _hm
          simpa only [active] using step_mul_star N m k l b t
    _ = ∑ m ∈ Finset.Ico M (pairCutoff N M H k l),
          b k * star (b l) * E (((k : ℝ) - l) * t) ^ m := by rw [hfilter]
    _ = b k * star (b l) *
          ∑ m ∈ Finset.Ico M (pairCutoff N M H k l),
            E (((k : ℝ) - l) * t) ^ m := by
          rw [Finset.mul_sum]

theorem pair_sum_norm_le (N M H k l : ℕ) (b : ℕ → ℂ) (t : ℝ) :
    ‖pairSum N M H b t k l‖ ≤
      ‖b k‖ * ‖b l‖ * cap H (((k : ℝ) - l) * t) := by
  rw [pair_sum_eq_coeff_block]
  have hblock :
      ‖∑ m ∈ Finset.Ico M (pairCutoff N M H k l),
          E (((k : ℝ) - l) * t) ^ m‖ ≤
        cap H (((k : ℝ) - l) * t) := by
    simpa only [cap] using
      (TypeIIBlock.typeII_block_norm_le (E (((k : ℝ) - l) * t))
        M (pairCutoff N M H k l) H (norm_E (((k : ℝ) - l) * t))
        (pairCutoff_sub_le N M H k l))
  calc
    ‖b k * star (b l) *
        ∑ m ∈ Finset.Ico M (pairCutoff N M H k l),
          E (((k : ℝ) - l) * t) ^ m‖
        = ‖b k‖ * ‖b l‖ *
            ‖∑ m ∈ Finset.Ico M (pairCutoff N M H k l),
              E (((k : ℝ) - l) * t) ^ m‖ := by
          rw [norm_mul, norm_mul]
          have hstar : ‖star (b l)‖ = ‖b l‖ := by
            simpa only [Complex.star_def] using Complex.norm_conj (b l)
          rw [hstar]
    _ ≤ ‖b k‖ * ‖b l‖ * cap H (((k : ℝ) - l) * t) :=
      mul_le_mul_of_nonneg_left hblock (by positivity)

theorem row_energy_eq_pairSums (N M H : ℕ) (K : Finset ℕ)
    (b : ℕ → ℂ) (t : ℝ) :
    (∑ m ∈ block M H, ‖row N K b t m‖ ^ 2) =
      (∑ k ∈ K, ∑ l ∈ K, pairSum N M H b t k l).re := by
  calc
    (∑ m ∈ block M H, ‖row N K b t m‖ ^ 2)
        = ∑ m ∈ block M H, (row N K b t m * star (row N K b t m)).re := by
          apply Finset.sum_congr rfl
          intro m _hm
          rw [show row N K b t m * star (row N K b t m) =
              ((‖row N K b t m‖ : ℂ) ^ 2) by
            rw [Complex.star_def]
            exact Complex.mul_conj' (row N K b t m)]
          simp [pow_two]
    _ = (∑ m ∈ block M H,
          row N K b t m * star (row N K b t m)).re := by simp
    _ = (∑ m ∈ block M H, ∑ k ∈ K, ∑ l ∈ K,
          step N b t m k * star (step N b t m l)).re := by
          congr 1
          apply Finset.sum_congr rfl
          intro m _hm
          change (∑ k ∈ K, step N b t m k) *
              star (∑ k ∈ K, step N b t m k) = _
          rw [star_sum]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _hk
          rw [Finset.mul_sum]
    _ = (∑ k ∈ K, ∑ m ∈ block M H, ∑ l ∈ K,
          step N b t m k * star (step N b t m l)).re := by
          rw [Finset.sum_comm]
    _ = (∑ k ∈ K, ∑ l ∈ K, ∑ m ∈ block M H,
          step N b t m k * star (step N b t m l)).re := by
          congr 1
          apply Finset.sum_congr rfl
          intro k _hk
          rw [Finset.sum_comm]
    _ = (∑ k ∈ K, ∑ l ∈ K, pairSum N M H b t k l).re := by rfl

theorem row_energy_le_kernel (N M H : ℕ) (K : Finset ℕ)
    (b : ℕ → ℂ) (t : ℝ) :
    (∑ m ∈ block M H, ‖row N K b t m‖ ^ 2) ≤
      ∑ k ∈ K, ∑ l ∈ K,
        ‖b k‖ * ‖b l‖ * cap H (((k : ℝ) - l) * t) := by
  rw [row_energy_eq_pairSums]
  calc
    (∑ k ∈ K, ∑ l ∈ K, pairSum N M H b t k l).re
        = ∑ k ∈ K, ∑ l ∈ K, (pairSum N M H b t k l).re := by simp
    _ ≤ ∑ k ∈ K, ∑ l ∈ K, ‖pairSum N M H b t k l‖ := by
      apply Finset.sum_le_sum
      intro k _hk
      apply Finset.sum_le_sum
      intro l _hl
      exact Complex.re_le_norm _
    _ ≤ ∑ k ∈ K, ∑ l ∈ K,
          ‖b k‖ * ‖b l‖ * cap H (((k : ℝ) - l) * t) := by
      apply Finset.sum_le_sum
      intro k _hk
      apply Finset.sum_le_sum
      intro l _hl
      exact pair_sum_norm_le N M H k l b t

/-- The finite Type II block estimate: Cauchy--Schwarz on `m`, exact complex
inner-product expansion in `k,l`, and the unit-circle block estimate at each
pair difference. -/
theorem typeII_main_draft (N M H : ℕ) (K : Finset ℕ)
    (a b : ℕ → ℂ) (t : ℝ) :
    ‖∑ m ∈ Finset.Ico M (M + H),
        a m * ∑ k ∈ K,
          (if m * k ≤ N then b k * E ((m : ℝ) * k * t) else 0)‖ ^ 2 ≤
      (∑ m ∈ Finset.Ico M (M + H), ‖a m‖ ^ 2) *
        ∑ k ∈ K, ∑ l ∈ K,
          ‖b k‖ * ‖b l‖ * cap H (((k : ℝ) - l) * t) := by
  change ‖∑ m ∈ block M H, a m * row N K b t m‖ ^ 2 ≤
      (∑ m ∈ block M H, ‖a m‖ ^ 2) *
        ∑ k ∈ K, ∑ l ∈ K,
          ‖b k‖ * ‖b l‖ * cap H (((k : ℝ) - l) * t)
  have htriangle :
      ‖∑ m ∈ block M H, a m * row N K b t m‖ ≤
        ∑ m ∈ block M H, ‖a m‖ * ‖row N K b t m‖ := by
    calc
      ‖∑ m ∈ block M H, a m * row N K b t m‖
          ≤ ∑ m ∈ block M H, ‖a m * row N K b t m‖ := norm_sum_le _ _
      _ = ∑ m ∈ block M H, ‖a m‖ * ‖row N K b t m‖ := by
        apply Finset.sum_congr rfl
        intro m _hm
        rw [norm_mul]
  calc
    ‖∑ m ∈ block M H, a m * row N K b t m‖ ^ 2
        ≤ (∑ m ∈ block M H, ‖a m‖ * ‖row N K b t m‖) ^ 2 := by
          exact pow_le_pow_left₀ (norm_nonneg _) htriangle 2
    _ ≤ (∑ m ∈ block M H, ‖a m‖ ^ 2) *
          ∑ m ∈ block M H, ‖row N K b t m‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq (block M H)
        (fun m => ‖a m‖) (fun m => ‖row N K b t m‖)
    _ ≤ (∑ m ∈ block M H, ‖a m‖ ^ 2) *
          ∑ k ∈ K, ∑ l ∈ K,
            ‖b k‖ * ‖b l‖ * cap H (((k : ℝ) - l) * t) :=
      mul_le_mul_of_nonneg_left (row_energy_le_kernel N M H K b t) (by positivity)

end

end TypeIIMainDraft

theorem Conjectures.Goldbach.TypeIiSpacingBound :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let cap (H : ℕ) (x : ℝ) := if E x = 1 then (H : ℝ) else min (H : ℝ) (2 / ‖1 - E x‖); ∀ (N M H : ℕ) (K : Finset ℕ) (a b : ℕ → ℂ) (t : ℝ), let I := Finset.Ico M (M+H); ‖∑ m ∈ I, a m * ∑ k ∈ K, (if m*k ≤ N then b k * E ((m : ℝ) * (k : ℝ) * t) else 0)‖ ^ 2 ≤ (∑ m ∈ I, ‖a m‖ ^ 2) * (∑ k ∈ K, ∑ l ∈ K, ‖b k‖ * ‖b l‖ * cap H (((k : ℝ) - (l : ℝ)) * t)) := by
  dsimp only
  intro N M H K a b t
  change ‖∑ m ∈ TypeIIMainDraft.block M H, a m * TypeIIMainDraft.row N K b t m‖ ^ 2 ≤
    (∑ m ∈ TypeIIMainDraft.block M H, ‖a m‖ ^ 2) *
      (∑ k ∈ K, ∑ l ∈ K,
        ‖b k‖ * ‖b l‖ * TypeIIMainDraft.cap H (((k : ℝ) - l) * t))
  exact TypeIIMainDraft.typeII_main_draft N M H K a b t
