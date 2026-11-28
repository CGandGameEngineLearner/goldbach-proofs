import Mathlib

open Finset MeasureTheory
open scoped ComplexConjugate

-- child 1 zh: 按最高位分组，证明相邻位不同的允许词计数和频率转移递推。
-- child 1 en: Count the adjacent-distinct words and derive their frequency transfer recursion by the top digit.
-- child 2 zh: 对至少三种数字的转移递推，证明它与偶数哥猜例外集的傅里叶配对有幂次节省。
-- child 2 en: Obtain a relative power saving for the Goldbach exception pairing with the transfer recursion on alphabets of at least three digits.

theorem Conjectures.Cuts.Cut1419c6766e02de58b7725cff
    (transfer : (by
      let phase := fun (n : ℕ) (t : ℝ) =>
        Complex.exp (((2*Real.pi*((n:ℝ)*t):ℝ):ℂ)*Complex.I)
      let words := fun (b : ℕ) (D : Finset ℕ) (k : ℕ) =>
        (Finset.range (b^k)).filter (fun n : ℕ =>
          (∀ i < k, (n/b^i)%b ∈ D) ∧
          ∀ i < k-1, (n/b^i)%b ≠ (n/b^(i+1))%b)
      let row := fun (b : ℕ) (D : Finset ℕ) (j : ℕ) =>
        Nat.rec (motive := fun _ => ℕ → ℝ → ℂ) phase
          (fun i prev a t =>
            phase (a*b^(i+1)) t * ∑ c ∈ D.filter (fun c => c ≠ a), prev c t) j
      exact ∀ b : ℕ, 2 ≤ b → ∀ D : Finset ℕ, D ⊆ Finset.range b →
        2 ≤ D.card → ∀ j : ℕ,
        (∀ t, ∑ n ∈ words b D (j+1), phase n t = ∑ a ∈ D, row b D j a t) ∧
        (words b D (j+1)).card = D.card * (D.card-1)^j))
    (bound : (by
      let phase := fun (n : ℕ) (t : ℝ) =>
        Complex.exp (((2*Real.pi*((n:ℝ)*t):ℝ):ℂ)*Complex.I)
      let row := fun (b : ℕ) (D : Finset ℕ) (j : ℕ) =>
        Nat.rec (motive := fun _ => ℕ → ℝ → ℂ) phase
          (fun i prev a t =>
            phase (a*b^(i+1)) t * ∑ c ∈ D.filter (fun c => c ≠ a), prev c t) j
      let exception := fun n : ℕ =>
        Even n ∧ ¬ ∃ p < n+1, Nat.Prime p ∧ Nat.Prime (n-p)
      exact ∀ b : ℕ, 2 ≤ b → ∀ D : Finset ℕ, D ⊆ Finset.range b →
        3 ≤ D.card → ∃ δ C : ℝ, 0<δ ∧ δ<1 ∧ 0<C ∧ ∀ j : ℕ,
        (∫ t in (0:ℝ)..1, (∑ a ∈ D, row b D j a t) *
          conj (∑ n ∈ (Finset.range (b^(j+1))).filter exception, phase n t)).re ≤
          C * (1+((D.card * (D.card-1)^j : ℕ) : ℝ))^(1-δ))) :
(by
  classical
  exact ∀ b : ℕ, 2≤b → ∀ D : Finset ℕ, D ⊆ Finset.range b → 2≤D.card → ∃ δ C : ℝ, 0<δ ∧ δ<1 ∧ 0<C ∧ ∀ k : ℕ, let S := (Finset.range (b^k)).filter (fun n : ℕ => (∀ i < k, (n/b^(i))%b ∈ D) ∧ ∀ i, i+1<k → (n/b^(i))%b≠(n/b^(i+1))%b); (((S).filter (fun n : ℕ => Even n ∧ ¬ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n))).card:ℝ) ≤ C*(1+(S.card:ℝ))^(1-δ)) := by
  let words := fun (b : ℕ) (D : Finset ℕ) (k : ℕ) =>
    (Finset.range (b^k)).filter (fun n : ℕ =>
      (∀ i < k, (n/b^i)%b ∈ D) ∧
      ∀ i < k-1, (n/b^i)%b ≠ (n/b^(i+1))%b)
  let finiteException := fun n : ℕ =>
    Even n ∧ ¬ ∃ p < n+1, Nat.Prime p ∧ Nat.Prime (n-p)
  classical
  -- Orthogonality follows repository PR 4419 and its Apache-2.0 source BinaryShiftFourierFourth.
  let realPhase (u : ℝ) : ℂ :=
    Complex.exp (((2 * Real.pi * u : ℝ) : ℂ) * Complex.I)

  let phase (n : ℕ) (t : ℝ) : ℂ :=
    Complex.exp (((2 * Real.pi * ((n : ℝ)*t) : ℝ) : ℂ) * Complex.I)

  have realPhase_add (u v : ℝ) : realPhase (u+v) = realPhase u * realPhase v := by
    dsimp only [realPhase]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

  have realPhase_conj (u : ℝ) : conj (realPhase u) = realPhase (-u) := by
    dsimp only [realPhase]
    rw [← Complex.exp_conj]
    congr 1
    push_cast
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring

  have integer_mode_integral (m : ℤ) :
      (∫ t in (0 : ℝ)..1, realPhase ((m : ℝ)*t)) = if m = 0 then 1 else 0 := by
    by_cases hm : m = 0
    · subst m
      simp [realPhase]
    let c : ℂ := (m : ℂ) * (2 * Real.pi * Complex.I)
    have hphase (t : ℝ) : realPhase ((m : ℝ)*t) = Complex.exp (c*(t : ℂ)) := by
      dsimp only [realPhase, c]
      congr 1
      push_cast
      ring
    have hc : c ≠ 0 := by
      dsimp [c]
      exact mul_ne_zero (by exact_mod_cast hm)
        (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
          Complex.I_ne_zero)
    simp_rw [hphase]
    rw [integral_exp_mul_complex hc]
    simp [hm, c, Complex.exp_int_mul_two_pi_mul_I]

  have orthogonality (n r : ℕ) :
      (∫ t in (0 : ℝ)..1, phase n t * conj (phase r t)) = if n = r then 1 else 0 := by
    have hphase (t : ℝ) :
        phase n t * conj (phase r t) = realPhase ((((n : ℤ) - (r : ℤ) : ℤ) : ℝ)*t) := by
      change realPhase ((n : ℝ)*t) * conj (realPhase ((r : ℝ)*t)) = _
      rw [realPhase_conj, ← realPhase_add]
      congr 1
      push_cast
      ring
    simp_rw [hphase]
    rw [integer_mode_integral]
    by_cases h : n = r
    · subst r
      simp
    · have hne : (n : ℤ) - (r : ℤ) ≠ 0 := by omega
      simp [h, hne]

  have pairing (S R : Finset ℕ) :
      ((S.filter (fun n => n ∈ R)).card : ℝ) =
        (∫ t in (0 : ℝ)..1, (∑ n ∈ S, phase n t) * conj (∑ r ∈ R, phase r t)).re := by
    have hexpand (t : ℝ) :
        (∑ n ∈ S, phase n t) * conj (∑ r ∈ R, phase r t) =
          ∑ n ∈ S, ∑ r ∈ R, phase n t * conj (phase r t) := by
      rw [map_sum, sum_mul]
      simp only [mul_sum]
    have hcont (n r : ℕ) : Continuous (fun t => phase n t * conj (phase r t)) := by
      dsimp only [phase]
      fun_prop
    have hcontSum (n : ℕ) : Continuous (fun t => ∑ r ∈ R, phase n t * conj (phase r t)) := by
      dsimp only [phase]
      fun_prop
    have hrow (n : ℕ) :
        (∫ t in (0 : ℝ)..1, ∑ r ∈ R, phase n t * conj (phase r t)) =
          if n ∈ R then (1 : ℂ) else 0 := by
      rw [intervalIntegral.integral_finsetSum (fun r (_ : r ∈ R) =>
        (hcont n r).intervalIntegrable ..)]
      simp [orthogonality]
    simp_rw [hexpand]
    rw [intervalIntegral.integral_finsetSum (fun n (_ : n ∈ S) =>
      (hcontSum n).intervalIntegrable ..)]
    simp_rw [hrow]
    rw [Finset.sum_boole]
    simp

  intro b hb D hD hsize
  let originalWords (k : ℕ) :=
    (Finset.range (b^k)).filter (fun n : ℕ =>
      (∀ i < k, (n/b^i)%b ∈ D) ∧
      ∀ i, i+1<k → (n/b^i)%b ≠ (n/b^(i+1))%b)
  let exception (n : ℕ) := Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n
  have words_eq (k : ℕ) : originalWords k = words b D k := by
    ext n
    simp only [originalWords, words, Finset.mem_filter]
    have h : (∀ i, i + 1 < k → n / b^i % b ≠ n / b^(i+1) % b) ↔
        (∀ i < k-1, n / b^i % b ≠ n / b^(i+1) % b) := by
      constructor <;> intro h i hi <;> exact h i (by omega)
    rw [h]
  have exception_iff (n : ℕ) : finiteException n ↔ exception n := by
    unfold finiteException exception
    apply and_congr_right'
    apply not_congr
    constructor
    · rintro ⟨p, hp, hp', hq⟩
      exact ⟨p, n - p, hp', hq, by omega⟩
    · rintro ⟨p, q, hp, hq, hpq⟩
      exact ⟨p, by omega, hp, by rwa [show n-p = q by omega]⟩
  change ∃ δ C : ℝ, 0<δ ∧ δ<1 ∧ 0<C ∧ ∀ k : ℕ,
    ((Finset.filter exception (originalWords k)).card : ℝ) ≤
      C*(1+((originalWords k).card:ℝ))^(1-δ)
  simp_rw [words_eq]
  have size_zero : (words b D 0).card ≤ 1 := by simp [words]
  have power_ge_one (s : Finset ℕ) {δ : ℝ} (hδ : δ < 1) :
      1 ≤ (1+(s.card:ℝ))^(1-δ) :=
    Real.one_le_rpow (le_add_of_nonneg_right (Nat.cast_nonneg _)) (sub_nonneg.mpr hδ.le)
  have small_word_bound (k : ℕ) {c : ℕ} {δ C : ℝ}
      (hc : (words b D k).card ≤ c) (hδ : δ < 1) (hC : (c : ℝ) ≤ C) :
      ((Finset.filter exception (words b D k)).card : ℝ) ≤ C*(1+((words b D k).card:ℝ))^(1-δ) := by
    have hCard := (Finset.card_filter_le (s := words b D k) (p := exception)).trans hc
    have hCast : ((Finset.filter exception (words b D k)).card : ℝ) ≤ c := by exact_mod_cast hCard
    have hNonneg : 0 ≤ C := (Nat.cast_nonneg _).trans hC
    exact (hCast.trans hC).trans (le_mul_of_one_le_right hNonneg (power_ge_one _ hδ))
  by_cases hlarge : 3 ≤ D.card
  · obtain ⟨δ, C, hδ, hδ', hC, hB⟩ := bound b hb D hD hlarge
    refine ⟨δ, C+1, hδ, hδ', by positivity, ?_⟩
    intro k
    cases k with
    | zero =>
      exact small_word_bound 0 size_zero hδ' (by norm_num; linarith only [hC])
    | succ j =>
      have hT := transfer b hb D hD hsize j
      obtain ⟨hSpectrum, hCount⟩ := hT
      have hCount' : (words b D (j+1)).card = D.card*(D.card-1)^j := hCount
      let R := (Finset.range (b^(j+1))).filter finiteException
      have hR : (words b D (j+1)).filter (fun n => n ∈ R) = (words b D (j+1)).filter exception := by
        ext n
        simp only [Finset.mem_filter, R, and_congr_right_iff]
        intro hn
        constructor
        · exact fun h => (exception_iff n).mp h.2
        · exact fun he => ⟨(Finset.mem_filter.mp hn).1, (exception_iff n).mpr he⟩
      have hPair := pairing (words b D (j+1)) R
      rw [hR] at hPair
      let row (j : ℕ) :=
        Nat.rec (motive := fun _ => ℕ → ℝ → ℂ) phase
          (fun i prev a t =>
            phase (a*b^(i+1)) t * ∑ c ∈ D.filter (fun c => c ≠ a), prev c t) j
      have hSpectrum' (t : ℝ) :
          (∑ n ∈ words b D (j+1), phase n t) = ∑ a ∈ D, row j a t := hSpectrum t
      simp_rw [hSpectrum'] at hPair
      have hAnalytic := hB j
      rw [← hCount'] at hAnalytic
      rw [hPair]
      exact hAnalytic.trans (mul_le_mul_of_nonneg_right (by linarith only)
        (by positivity))
  · have htwo : D.card = 2 := by omega
    refine ⟨1/2, 2, by norm_num, by norm_num, by norm_num, ?_⟩
    intro k
    cases k with
    | zero => exact small_word_bound 0 (c := 2) (size_zero.trans (by decide)) (by norm_num) (by norm_num)
    | succ j =>
      have hCount : (words b D (j+1)).card = D.card*(D.card-1)^j :=
        (transfer b hb D hD hsize j).2
      apply small_word_bound (c := 2)
      · rw [hCount, htwo]
        simp
      · norm_num
      · norm_num
