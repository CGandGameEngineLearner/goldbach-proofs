import Mathlib

open Finset

namespace Conjectures.Goldbach.RectangularDivisorBudget_aux

noncomputable section

def harmonicBox (M : ℕ) : ℝ := ∑ d ∈ Finset.Icc 1 M, (d:ℝ)⁻¹

def invHit (q u : ℕ) : ℝ := if q ∣ u then (u:ℝ)⁻¹ else 0

theorem invHit_nonneg (q u : ℕ) : 0 ≤ invHit q u := by
  unfold invHit
  split_ifs <;> positivity

theorem harmonicBox_nonneg (M : ℕ) : 0 ≤ harmonicBox M :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem hitHarmonic (M q : ℕ) (hq : 0 < q) :
    (∑ u ∈ Finset.Icc 1 M, invHit q u) ≤ (q:ℝ)⁻¹ * harmonicBox M := by
  let S := Finset.Icc 1 (M/q)
  have hs : (Finset.Icc 1 M).filter (q ∣ ·) = S.image (fun k => q * k) := by
    ext u
    constructor
    · intro h
      obtain ⟨huk, huq⟩ := Finset.mem_filter.mp h
      obtain ⟨k, rfl⟩ := huq
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp huk
      exact Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨by cases k <;> simp_all,
        (Nat.le_div_iff_mul_le hq).mpr (by simpa [mul_comm] using h2)⟩, rfl⟩
    · intro h
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hq hk1,
        by simpa [mul_comm] using (Nat.le_div_iff_mul_le hq).mp hk2⟩, dvd_mul_right _ _⟩
  unfold invHit
  rw [← Finset.sum_filter, hs,
    Finset.sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hq h)]
  simp only [Nat.cast_mul, mul_inv, ← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right (Nat.div_le_self _ _)) (fun _ _ _ => by positivity)

theorem rect (A D : ℕ) (T : ℕ → ℝ) (hT : ∀ q, 0 ≤ T q) :
    (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D,
        ((∑ q ∈ (u.gcd v).divisors, T q)*(u:ℝ)⁻¹*(v:ℝ)⁻¹)) ≤
      (∑ q ∈ Finset.Icc 1 (min A D), T q*(q:ℝ)⁻¹^2) *
        (∑ u ∈ Finset.Icc 1 A, (u:ℝ)⁻¹) * (∑ v ∈ Finset.Icc 1 D, (v:ℝ)⁻¹) := by
  have he (u v : ℕ) (hu : u ∈ Finset.Icc 1 A) (hv : v ∈ Finset.Icc 1 D) :
      (∑ q ∈ (u.gcd v).divisors, T q)*(u:ℝ)⁻¹*(v:ℝ)⁻¹
        = ∑ q ∈ Finset.Icc 1 (min A D), T q * invHit q u * invHit q v := by
    have hu0 : 0 < u := (Finset.mem_Icc.mp hu).1
    have hv0 : 0 < v := (Finset.mem_Icc.mp hv).1
    have hu2 : u ≤ A := (Finset.mem_Icc.mp hu).2
    have hv2 : v ≤ D := (Finset.mem_Icc.mp hv).2
    have hg0 : 0 < u.gcd v := Nat.gcd_pos_of_pos_left _ hu0
    have hdiv : (u.gcd v).divisors
        = (Finset.Icc 1 (min A D)).filter (fun q => q ∣ u ∧ q ∣ v) := by
      ext q
      rw [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · intro h
        have hqu : q ∣ u := h.1.trans (Nat.gcd_dvd_left u v)
        have hqv : q ∣ v := h.1.trans (Nat.gcd_dvd_right u v)
        refine ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hqu hu0, ?_⟩, hqu, hqv⟩
        exact le_min ((Nat.le_of_dvd hu0 hqu).trans hu2) ((Nat.le_of_dvd hv0 hqv).trans hv2)
      · intro h
        exact ⟨Nat.dvd_gcd h.2.1 h.2.2, hg0.ne'⟩
    rw [hdiv, Finset.sum_filter, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases ha : q ∣ u <;> by_cases hb : q ∣ v <;> simp [invHit, ha, hb]
  calc (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D,
          ((∑ q ∈ (u.gcd v).divisors, T q)*(u:ℝ)⁻¹*(v:ℝ)⁻¹))
      = ∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D,
          ∑ q ∈ Finset.Icc 1 (min A D), T q * invHit q u * invHit q v :=
        Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => he u v hu hv
    _ = ∑ u ∈ Finset.Icc 1 A, ∑ q ∈ Finset.Icc 1 (min A D),
          ∑ v ∈ Finset.Icc 1 D, T q * invHit q u * invHit q v :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ q ∈ Finset.Icc 1 (min A D), ∑ u ∈ Finset.Icc 1 A,
          ∑ v ∈ Finset.Icc 1 D, T q * invHit q u * invHit q v := Finset.sum_comm
    _ = ∑ q ∈ Finset.Icc 1 (min A D),
          T q * (∑ u ∈ Finset.Icc 1 A, invHit q u) * (∑ v ∈ Finset.Icc 1 D, invHit q v) := by
      apply Finset.sum_congr rfl
      intro q hq
      calc ∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D, T q * invHit q u * invHit q v
          = (∑ u ∈ Finset.Icc 1 A, T q * invHit q u) * (∑ v ∈ Finset.Icc 1 D, invHit q v) :=
            (Finset.sum_mul_sum _ _ (fun u => T q * invHit q u) (fun v => invHit q v)).symm
        _ = T q * (∑ u ∈ Finset.Icc 1 A, invHit q u) * (∑ v ∈ Finset.Icc 1 D, invHit q v) := by
            have e : (∑ u ∈ Finset.Icc 1 A, T q * invHit q u)
                = T q * (∑ u ∈ Finset.Icc 1 A, invHit q u) :=
              (Finset.mul_sum _ _ _).symm
            rw [e]
    _ ≤ ∑ q ∈ Finset.Icc 1 (min A D),
          T q * ((q:ℝ)⁻¹ * harmonicBox A) * ((q:ℝ)⁻¹ * harmonicBox D) := by
      apply Finset.sum_le_sum
      intro q hq
      have hq1 : 0 < q := (Finset.mem_Icc.mp hq).1
      have hA := hitHarmonic A q hq1
      have hD := hitHarmonic D q hq1
      have hD0 : 0 ≤ ∑ v ∈ Finset.Icc 1 D, invHit q v :=
        Finset.sum_nonneg fun v _ => invHit_nonneg q v
      have hb : 0 ≤ T q * ((q:ℝ)⁻¹ * harmonicBox A) :=
        mul_nonneg (hT q) (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg q))
          (harmonicBox_nonneg A))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hA (hT q)) hD hD0 hb
    _ = (∑ q ∈ Finset.Icc 1 (min A D), T q*(q:ℝ)⁻¹^2) * harmonicBox A * harmonicBox D := by
      have h2 (q : ℕ) (hq : q ∈ Finset.Icc 1 (min A D)) :
          T q * ((q:ℝ)⁻¹ * harmonicBox A) * ((q:ℝ)⁻¹ * harmonicBox D)
            = (T q*(q:ℝ)⁻¹^2) * (harmonicBox A * harmonicBox D) := by ring
      calc ∑ q ∈ Finset.Icc 1 (min A D),
              T q * ((q:ℝ)⁻¹ * harmonicBox A) * ((q:ℝ)⁻¹ * harmonicBox D)
          = ∑ q ∈ Finset.Icc 1 (min A D),
              (T q*(q:ℝ)⁻¹^2) * (harmonicBox A * harmonicBox D) :=
            Finset.sum_congr rfl fun q hq => h2 q hq
        _ = (∑ q ∈ Finset.Icc 1 (min A D), T q*(q:ℝ)⁻¹^2)
              * (harmonicBox A * harmonicBox D) := (Finset.sum_mul _ _ _).symm
        _ = _ := by ring

end

end Conjectures.Goldbach.RectangularDivisorBudget_aux

theorem Conjectures.Goldbach.RectangularDivisorBudget : ∀ (A D : ℕ) (T : ℕ→ℝ), (∀ q,0≤T q) → (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D, ((∑ q ∈ (u.gcd v).divisors,T q)*(u:ℝ)⁻¹*(v:ℝ)⁻¹)) ≤ (∑ q ∈ Finset.Icc 1 (min A D),T q*(q:ℝ)⁻¹^2)* (∑ u ∈ Finset.Icc 1 A,(u:ℝ)⁻¹)*(∑ v ∈ Finset.Icc 1 D,(v:ℝ)⁻¹) := by
  intro A D T hT
  exact Conjectures.Goldbach.RectangularDivisorBudget_aux.rect A D T hT
