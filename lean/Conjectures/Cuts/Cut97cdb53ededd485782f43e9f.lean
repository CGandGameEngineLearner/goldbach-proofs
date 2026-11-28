import Mathlib

open MeasureTheory

/- The Fourier orthogonality calculation and measurable-set split are adapted
from the Apache-2.0 licensed goldbach-proofs module
PEqualNP.Outside.L_goldbach_arc_coefficient_sum, at commit c3b16276d1c3c0be2c342ccba1a5a03016c498d3.
Here the two factors are restricted to the same reflected central interval. -/

-- child 1 zh: 对充分大的二幂靶点，中心窗截断素数和的主弧傅里叶系数实部具有一致的正线性下界。
-- child 1 en: On all sufficiently large dyadic targets, the major-arc Fourier coefficient of the centrally clipped prime sum has a uniform positive linear real part.
-- child 2 zh: 保持同一中心窗截断和同一二幂靶点，在主弧补集上的系数实部具有任意小的单侧线性亏损。
-- child 2 en: For the same central truncation and dyadic target, the complementary coefficient has a lower bound of minus epsilon times the target for every positive epsilon.

theorem Conjectures.Cuts.Cut97cdb53ededd485782f43e9f
    (majorFloor :
      let E := fun t : ℝ => Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
      let v := fun n p : ℕ => if n ≤ 3*p ∧ 3*p ≤ 2*n ∧ Nat.Prime p then Real.log (p : ℝ) else 0
      let Q := fun n : ℕ => (Nat.log 2 (n+2))^2
      let A := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ a.Coprime q ∧
        |t - (a : ℝ) / q| ≤ (Q n : ℝ) / ((q : ℝ) * n)}
      let f := fun (n : ℕ) (t : ℝ) =>
        (∑ p ∈ Finset.range (n+1), (v n p : ℂ) * E ((p : ℝ)*t))^2 * E (-(n : ℝ)*t)
      ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∀ k ≥ K, let n : ℕ := 2^k;
        c * (n : ℝ) ≤ (intervalIntegral ((A n).indicator (f n)) 0 1 volume).re)
    (minorFloor :
      let E := fun t : ℝ => Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
      let v := fun n p : ℕ => if n ≤ 3*p ∧ 3*p ≤ 2*n ∧ Nat.Prime p then Real.log (p : ℝ) else 0
      let Q := fun n : ℕ => (Nat.log 2 (n+2))^2
      let A := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ a.Coprime q ∧
        |t - (a : ℝ) / q| ≤ (Q n : ℝ) / ((q : ℝ) * n)}
      let f := fun (n : ℕ) (t : ℝ) =>
        (∑ p ∈ Finset.range (n+1), (v n p : ℂ) * E ((p : ℝ)*t))^2 * E (-(n : ℝ)*t)
      ∀ e : ℝ, 0 < e → ∃ K : ℕ, ∀ k ≥ K, let n : ℕ := 2^k;
        -(e * (n : ℝ)) ≤ (intervalIntegral ((A n)ᶜ.indicator (f n)) 0 1 volume).re) :
    (let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0; ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀, let n : ℕ := 2^k; c*(n : ℝ) ≤ ∑ p ∈ (Finset.range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n), w p * w (n-p)) := by
  intro w
  obtain ⟨c, hc, K₁, h₁⟩ := majorFloor
  obtain ⟨K₂, h₂⟩ := minorFloor (c/2) (half_pos hc)
  refine ⟨c/2, half_pos hc, max K₁ K₂, fun k hk => ?_⟩
  intro n
  let E := fun t : ℝ => Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
  let v := fun p : ℕ => if n ≤ 3*p ∧ 3*p ≤ 2*n ∧ Nat.Prime p then Real.log (p : ℝ) else 0
  let Q := (Nat.log 2 (n+2))^2
  let A := {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ a.Coprime q ∧
    |t - (a : ℝ) / q| ≤ (Q : ℝ) / ((q : ℝ) * n)}
  let f := fun t : ℝ =>
    (∑ p ∈ Finset.range (n+1), (v p : ℂ) * E ((p : ℝ)*t))^2 * E (-(n : ℝ)*t)
  have hA : MeasurableSet A := by
    simp only [A, Set.ofPred_exists]
    refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
    by_cases h : 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ a.Coprime q
    · obtain ⟨hq, hQ, ha, hca⟩ := h
      have hmeas : MeasurableSet {t : ℝ | |t - (a : ℝ) / q| ≤ (Q : ℝ) / (q * n)} :=
        measurableSet_le
          (show Continuous (fun t : ℝ => |t - (a : ℝ) / q|) by fun_prop).measurable
          measurable_const
      convert hmeas using 1
      ext t
      exact ⟨fun h => h.2.2.2.2, fun h => ⟨hq, hQ, ha, hca, h⟩⟩
    · convert MeasurableSet.empty (α := ℝ) using 1
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun ht => h ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1⟩
  have hf : IntervalIntegrable f volume (0 : ℝ) 1 := by
    apply Continuous.intervalIntegrable
    dsimp [f, E]
    fun_prop
  have hi {U : Set ℝ} (hU : MeasurableSet U) :
      IntervalIntegrable (U.indicator f) volume 0 1 :=
    ⟨hf.1.indicator hU, hf.2.indicator hU⟩
  have hsplit : intervalIntegral (A.indicator f) 0 1 volume +
      intervalIntegral (Aᶜ.indicator f) 0 1 volume = intervalIntegral f 0 1 volume := by
    rw [← intervalIntegral.integral_add (hi hA) (hi hA.compl)]
    apply congrArg (fun g : ℝ → ℂ => intervalIntegral g 0 1 volume)
    funext t
    by_cases ht : t ∈ A <;> simp [ht]
  have phaseAdd (u t : ℝ) : E (u+t) = E u * E t := by
    unfold E
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have mode (m : ℤ) :
      (∫ t in (0 : ℝ)..1, E ((m : ℝ)*t)) = if m = 0 then 1 else 0 := by
    by_cases hm : m = 0
    · subst m
      simp [E]
    let z : ℂ := (m : ℂ) * (2 * Real.pi * Complex.I)
    have hE (t : ℝ) : E ((m : ℝ)*t) = Complex.exp (z * (t : ℂ)) := by
      unfold E z
      congr 1
      push_cast
      ring
    have hz : z ≠ 0 := by
      dsimp [z]
      exact mul_ne_zero (by exact_mod_cast hm)
        (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
    simp_rw [hE]
    rw [integral_exp_mul_complex hz]
    simp [hm, z, Complex.exp_int_mul_two_pi_mul_I]
  let I := Finset.range (n+1)
  let term := fun (p q : ℕ) (t : ℝ) =>
    ((v p : ℂ) * (v q : ℂ)) * E (((((p : ℤ) + q - n) : ℤ) : ℝ)*t)
  have hcont (p q : ℕ) : Continuous (term p q) := by
    dsimp [term, E]
    fun_prop
  have hpoint (t : ℝ) : f t = ∑ p ∈ I, ∑ q ∈ I, term p q t := by
    dsimp only [f]
    simp only [sq, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    dsimp [term]
    push_cast
    rw [show ((p : ℝ) + q - n) * t = ((p : ℝ)*t + q*t) + -(n : ℝ)*t by ring,
      phaseAdd, phaseAdd]
    ring
  have hrow (p : ℕ) (hp : p ∈ I) :
      (∫ t in (0 : ℝ)..1, ∑ q ∈ I, term p q t) = (v p : ℂ) * (v (n-p) : ℂ) := by
    rw [intervalIntegral.integral_finsetSum (fun q _ => (hcont p q).intervalIntegrable _ _)]
    have hp' : p < n+1 := Finset.mem_range.mp hp
    have hsub : n-p ∈ I := Finset.mem_range.mpr (by omega)
    simp only [term, intervalIntegral.integral_const_mul, mode]
    rw [Finset.sum_eq_single_of_mem (n-p) hsub]
    · simp [show (p : ℤ) + ((n-p : ℕ) : ℤ) - n = 0 by omega]
    · intro q _ hne
      simp [show (p : ℤ) + q - n ≠ 0 by omega]
  have hconv : intervalIntegral f 0 1 volume =
      ((∑ p ∈ I, v p * v (n-p) : ℝ) : ℂ) := by
    rw [show f = (fun t => ∑ p ∈ I, ∑ q ∈ I, term p q t) from funext hpoint]
    rw [intervalIntegral.integral_finsetSum (fun p _ =>
      (continuous_finsetSum I (fun q _ => hcont p q)).intervalIntegrable _ _)]
    push_cast
    exact Finset.sum_congr rfl hrow
  have hcentral : (∑ p ∈ I, v p * v (n-p)) =
      ∑ p ∈ I.filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n), w p * w (n-p) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases h : n ≤ 3*p ∧ 3*p ≤ 2*n
    · have hp' := Finset.mem_range.mp hp
      have hr : n ≤ 3*(n-p) ∧ 3*(n-p) ≤ 2*n := by omega
      obtain ⟨hl, hu⟩ := h
      obtain ⟨hrl, hru⟩ := hr
      simp [v, w, hl, hu, hrl, hru]
    · have hv0 : v p = 0 := by
        apply ite_eq_right
        exact fun hv => h ⟨hv.1, hv.2.1⟩
      simp [hv0, h]
  have hM : c * (n : ℝ) ≤ (intervalIntegral (A.indicator f) 0 1 volume).re :=
    h₁ k ((le_max_left ..).trans hk)
  have hm : -(c/2 * (n : ℝ)) ≤ (intervalIntegral (Aᶜ.indicator f) 0 1 volume).re :=
    h₂ k ((le_max_right ..).trans hk)
  have htotal := congrArg Complex.re (hsplit.trans (hconv.trans (congrArg (fun x : ℝ => (x : ℂ)) hcentral)))
  simp only [Complex.add_re, Complex.ofReal_re] at htotal
  rw [← htotal]
  linarith only [hM, hm]
