import Mathlib
import Conjectures.Goldbach.EstermannAlmostAllPolylog
import PEqualNP.Outside.L_goldbach_grh_goldbach_exception_density

namespace Conjectures.Goldbach

private def representationCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).card

private def unshiftedExceptions (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter (fun n => 4 ≤ n ∧ n % 2 = 0 ∧ representationCount n = 0)

private def shiftedExceptions (X : ℕ) : Finset ℕ :=
  (Finset.Ico X (2 * X)).filter (fun n =>
    Even n ∧ 0 < ((Finset.Icc 1 (Nat.log 2 X / 2)).filter
      (fun e => representationCount (n - 2 ^ e) = 0)).card)

private theorem shiftedExceptions_card_le (X : ℕ) (hX : 8 ≤ X) :
    (shiftedExceptions X).card ≤ (Nat.log 2 X / 2) * (unshiftedExceptions (2 * X)).card := by
  classical
  let shifts := Finset.Icc 1 (Nat.log 2 X / 2)
  let pairs := shifts.product (unshiftedExceptions (2 * X))
  let addShift := fun pair : ℕ × ℕ => pair.2 + 2 ^ pair.1
  have hsubset : shiftedExceptions X ⊆ pairs.image addShift := by
    intro n hn
    unfold shiftedExceptions at hn
    obtain ⟨hnInterval, hnEven, hnMissing⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnLower, hnUpper⟩ := Finset.mem_Ico.mp hnInterval
    obtain ⟨e, he⟩ := Finset.card_pos.mp hnMissing
    obtain ⟨heShift, heMissing⟩ := Finset.mem_filter.mp he
    obtain ⟨heLower, heUpper⟩ := Finset.mem_Icc.mp heShift
    have hpow : 2 ^ (e + 1) ≤ X :=
      (Nat.pow_le_pow_right (by decide) (show e + 1 ≤ Nat.log 2 X by omega)).trans
        (Nat.pow_log_le_self 2 (by omega))
    rw [pow_succ] at hpow
    have heEven : 2 ∣ (2 : ℕ) ^ e := dvd_pow_self 2 (by omega)
    have hsubEven : (n - 2 ^ e) % 2 = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp (Nat.dvd_sub (even_iff_two_dvd.mp hnEven) heEven)
    have hsub : n - 2 ^ e ∈ unshiftedExceptions (2 * X) := by
      unfold unshiftedExceptions
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega, hsubEven, heMissing⟩
    refine Finset.mem_image.mpr ⟨(e, n - 2 ^ e), Finset.mem_product.mpr ⟨heShift, hsub⟩, ?_⟩
    dsimp [addShift]
    omega
  calc
    _ ≤ (pairs.image addShift).card := Finset.card_le_card hsubset
    _ ≤ pairs.card := Finset.card_image_le
    _ = _ := by simp [pairs, shifts, Nat.card_Icc]

/-- Every ordinary exception in the translated dyadic interval contributes to
the shifted exceptional set through the shift `2^1`. -/
theorem dyadicExceptions_card_le_shifted (X : ℕ) (hX : 4 ≤ X) :
    ((Finset.Ico (X - 2) (2 * X - 2)).filter
      (fun n => 4 ≤ n ∧ n % 2 = 0 ∧ representationCount n = 0)).card ≤
    (shiftedExceptions X).card := by
  refine Finset.card_le_card_of_injOn (fun n : ℕ => n + 2) ?_ ?_
  · intro n hn
    obtain ⟨hnInterval, _, hnEven, hnMissing⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hn)
    obtain ⟨hnLower, hnUpper⟩ := Finset.mem_Ico.mp hnInterval
    change n + 2 ∈ shiftedExceptions X
    unfold shiftedExceptions
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_, ?_⟩
    · exact Nat.even_iff.mpr (by omega)
    · apply Finset.card_pos.mpr
      refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, ?_⟩, ?_⟩⟩
      · have hlog : 2 ≤ Nat.log 2 X := Nat.le_log_of_pow_le (by decide) (by simpa using hX)
        omega
      · simpa using hnMissing
  · intro a _ b _ h
    exact Nat.add_right_cancel h

private theorem shift_count_le_log_div (X : ℕ) (hX : 0 < X) :
    ((Nat.log 2 X / 2 : ℕ) : ℝ) ≤ Real.log (X : ℝ) / Real.log 2 := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (2 : ℝ) ^ Nat.log 2 X ≤ (X : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hX.ne'
  apply (le_div_iff₀ hlogTwo).mpr
  calc
    _ ≤ (Nat.log 2 X : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.div_le_self (Nat.log 2 X) 2) hlogTwo.le
    _ = Real.log ((2 : ℝ) ^ Nat.log 2 X) := (Real.log_pow 2 _).symm
    _ ≤ _ := Real.log_le_log (by positivity) hpow

/-- Any exponent strictly below `4/5` for the ordinary exceptional set implies
the registered bound. Pintz's exponent `18/25` qualifies
(https://arxiv.org/abs/1804.09084). -/
theorem binaryShiftExceptionUnion_of_exceptionBound
    {α : ℝ} (hα : α < 4/5)
    (h : ∃ (C : ℝ) (X₀ : ℕ), 0 < C ∧ ∀ X : ℕ, X₀ ≤ X →
      ((unshiftedExceptions X).card : ℝ) ≤ C * (X : ℝ) ^ α) :
    let G := fun m : ℕ =>
      ((Finset.range (m + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m - p))).card
    ∃ X₀ : ℕ, ∀ X ≥ X₀,
      let L := Nat.log 2 X / 2
      let E := (Finset.Ico X (2 * X)).filter (fun n =>
        Even n ∧ 0 < ((Finset.Icc 1 L).filter (fun e => G (n - 2 ^ e) = 0)).card)
      E.card ^ 5 ≤ X ^ 4 := by
  change ∃ X₀ : ℕ, ∀ X ≥ X₀, (shiftedExceptions X).card ^ 5 ≤ X ^ 4
  obtain ⟨C, X₀, hC, hcount⟩ := h
  let A := C * (2 : ℝ) ^ α
  have hA : 0 < A := by dsimp [A]; positivity
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_atTop (sub_pos.mpr hα)).const_mul_left (A / Real.log 2)).eventuallyLE
  refine ⟨max 8 (max X₀ ⌈T⌉₊), ?_⟩
  intro X hX
  have hXNonnegative : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hXPositive : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hXT : T ≤ (X : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr (by omega))
  let L := Nat.log 2 X / 2
  have hshiftFactor : A * (L : ℝ) ≤ (X : ℝ) ^ (4/5 - α) := by
    have hasymptotic := hT (X : ℝ) hXT
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hXNonnegative _)] at hasymptotic
    calc
      _ ≤ A * (Real.log X / Real.log 2) :=
        mul_le_mul_of_nonneg_left (shift_count_le_log_div X (by omega)) hA.le
      _ = (A / Real.log 2) * Real.log X := by ring
      _ ≤ _ := (Real.le_norm_self _).trans hasymptotic
  have hdouble := hcount (2 * X) (by omega)
  norm_num [Nat.cast_mul, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hXNonnegative] at hdouble
  have hcard : ((shiftedExceptions X).card : ℝ) ≤ (X : ℝ) ^ (4/5 : ℝ) := calc
    _ ≤ (L : ℝ) * ((unshiftedExceptions (2 * X)).card : ℝ) := by
      exact_mod_cast shiftedExceptions_card_le X (show 8 ≤ X by omega)
    _ ≤ (L : ℝ) * (C * ((2 : ℝ) ^ α * (X : ℝ) ^ α)) :=
      mul_le_mul_of_nonneg_left hdouble (Nat.cast_nonneg _)
    _ = (A * (L : ℝ)) * (X : ℝ) ^ α := by dsimp [A]; ring
    _ ≤ (X : ℝ) ^ (4/5 - α) * (X : ℝ) ^ α :=
      mul_le_mul_of_nonneg_right hshiftFactor (Real.rpow_nonneg hXNonnegative _)
    _ = _ := by rw [← Real.rpow_add hXPositive, sub_add_cancel]
  have hpower : ((shiftedExceptions X).card : ℝ) ^ 5 ≤ (X : ℝ) ^ (4 : ℕ) := calc
    _ ≤ ((X : ℝ) ^ (4/5 : ℝ)) ^ 5 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 5
    _ = _ := by
      rw [← Real.rpow_mul_natCast hXNonnegative,
        show (4/5 : ℝ) * (5 : ℕ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact_mod_cast hpower

/-- The verified Dirichlet GRH estimate gives the registered conclusion at
the ordinary exception exponent `1/2 + 1/4`. -/
theorem binaryShiftExceptionUnion_of_dirichletGRH
    (hGRH : ∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
      0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (shiftedExceptions X).card ^ 5 ≤ X ^ 4 := by
  apply binaryShiftExceptionUnion_of_exceptionBound (α := 3/4) (by norm_num)
  obtain ⟨C, N, hC, hcount⟩ :=
    PEqualNP.Outside.L_goldbach_grh_goldbach_exception_density hGRH (1 / 4) (by norm_num)
  refine ⟨C, N, hC, ?_⟩
  intro X hX
  have estimate := hcount X hX
  rw [show (1 / 2 : ℝ) + 1 / 4 = 3 / 4 by norm_num] at estimate
  exact estimate

/-- The unconditional Estermann bound supplies every fixed logarithmic saving
for the same shifted exceptional set. -/
theorem binaryShiftExceptions_card_le_polylog (A : ℝ) (hA : 0 < A) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ((shiftedExceptions X).card : ℝ) ≤
        (2 / Real.log 2) * (X : ℝ) * Real.log (X : ℝ) ^ (-A) := by
  obtain ⟨N, hcount⟩ := EstermannAlmostAllPolylog.1 (A + 1) (by linarith)
  have hEven (Y : ℕ) : unshiftedExceptions Y =
      (Finset.range (Y + 1)).filter (fun n => 4 ≤ n ∧ Even n ∧ representationCount n = 0) := by
    ext n
    simp only [unshiftedExceptions, Finset.mem_filter, Nat.even_iff]
  refine ⟨max 8 N, ?_⟩
  intro X hX
  have hXPos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  let L := Nat.log 2 X / 2
  have hdouble : ((unshiftedExceptions (2 * X)).card : ℝ) ≤
      2 * (X : ℝ) * Real.log (2 * (X : ℝ)) ^ (-(A + 1)) := by
    rw [hEven]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using! hcount (2 * X) (by omega)
  have hlogLe : Real.log (X : ℝ) ≤ Real.log (2 * (X : ℝ)) :=
    Real.log_le_log hXPos (by linarith)
  have hpower : Real.log (2 * (X : ℝ)) ^ (-(A + 1)) ≤
      Real.log (X : ℝ) ^ (-(A + 1)) :=
    Real.rpow_le_rpow_of_nonpos hlogX hlogLe (by linarith)
  have habsorb : Real.log (X : ℝ) * Real.log (X : ℝ) ^ (-(A + 1)) =
      Real.log (X : ℝ) ^ (-A) := calc
    _ = Real.log (X : ℝ) ^ (1 : ℝ) * Real.log (X : ℝ) ^ (-(A + 1)) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hlogX, show 1 + -(A + 1) = -A by ring]
  calc
    _ ≤ (L : ℝ) * ((unshiftedExceptions (2 * X)).card : ℝ) := by
      exact_mod_cast shiftedExceptions_card_le X (show 8 ≤ X by omega)
    _ ≤ (L : ℝ) * (2 * (X : ℝ) * Real.log (2 * (X : ℝ)) ^ (-(A + 1))) :=
      mul_le_mul_of_nonneg_left hdouble (Nat.cast_nonneg _)
    _ ≤ (Real.log (X : ℝ) / Real.log 2) * (2 * (X : ℝ) * Real.log (X : ℝ) ^ (-(A + 1))) :=
      mul_le_mul (shift_count_le_log_div X (by omega))
        (mul_le_mul_of_nonneg_left hpower (by positivity))
        (mul_nonneg (by positivity) (Real.rpow_nonneg (hlogX.le.trans hlogLe) _))
        (div_nonneg hlogX.le hlogTwo.le)
    _ = (2 / Real.log 2) * (X : ℝ) * (Real.log (X : ℝ) * Real.log (X : ℝ) ^ (-(A + 1))) :=
      by ring
    _ = _ := by rw [habsorb]

end Conjectures.Goldbach
