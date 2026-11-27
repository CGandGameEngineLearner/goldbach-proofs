import Mathlib

namespace Conjectures.Goldbach.PacketEvenLagSupport_aux

lemma weight_even_zero {k : ℕ} (hk : Even k) (hk2 : k ≠ 2) :
    (if Nat.Prime k then Real.log (k:ℝ) else 0) = 0 := by
  have hnp : ¬ Nat.Prime k := fun hp => hk2 ((Nat.Prime.even_iff hp).mp hk)
  simp [hnp]

lemma high_even_zero {n k : ℕ} (hn : 8 ≤ n) (hk : Even k) :
    ((if Nat.Prime k then Real.log (k:ℝ) else 0) -
      (if k^3 ≤ n then (if Nat.Prime k then Real.log (k:ℝ) else 0) else 0)) = 0 := by
  by_cases hle : k^3 ≤ n
  · simp [hle]
  · have hw : (if Nat.Prime k then Real.log (k:ℝ) else 0) = 0 := by
      by_cases hk2 : k = 2
      · have h8 : k^3 = 8 := by rw [hk2]; norm_num
        exact absurd (le_trans (le_of_eq h8) hn) hle
      · exact weight_even_zero hk hk2
    simp [hle, hw]

lemma model_even_zero {k : ℕ} (hk : Even k) :
    (if Nat.Coprime k 30 then (30:ℝ)/8 else 0) = 0 := by
  have hnc : ¬ Nat.Coprime k 30 := by
    intro hc
    have h2 : Nat.Coprime k 2 := Nat.Coprime.of_dvd_right ⟨15, by norm_num⟩ hc
    exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_right.mp h2)) hk
  simp [hnc]

lemma odd_lag_sum_zero {n h : ℕ} (hh : Odd h) (f : ℕ → ℝ) (hf : ∀ k, Even k → f k = 0) :
    ∑ k ∈ Finset.range (n + 1 - h), f k * f (k + h) = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  by_cases he : Even k
  · rw [hf k he, zero_mul]
  · rw [hf (k + h) ((Nat.not_even_iff_odd.mp he).add_odd hh), mul_zero]

theorem claim : ∀ n : ℕ, 8 ≤ n → ∀ h : ℕ, Odd h →
    (∑ k ∈ Finset.range (n+1-h),
        ((if Nat.Prime k then Real.log (k:ℝ) else 0) -
            (if k^3 ≤ n then (if Nat.Prime k then Real.log (k:ℝ) else 0) else 0)) *
        ((if Nat.Prime (k+h) then Real.log ((k+h:ℕ):ℝ) else 0) -
            (if (k+h)^3 ≤ n then
              (if Nat.Prime (k+h) then Real.log ((k+h:ℕ):ℝ) else 0) else 0))) = 0 ∧
    (∑ k ∈ Finset.range (n+1-h),
        (if Nat.Coprime k 30 then (30:ℝ)/8 else 0) *
        (if Nat.Coprime (k+h) 30 then (30:ℝ)/8 else 0)) = 0 := by
  intro n hn h hh
  refine ⟨?_, ?_⟩
  · refine odd_lag_sum_zero hh
      (fun k => (if Nat.Prime k then Real.log (k:ℝ) else 0) -
        (if k^3 ≤ n then (if Nat.Prime k then Real.log (k:ℝ) else 0) else 0)) ?_
    intro k hk
    exact high_even_zero hn hk
  · refine odd_lag_sum_zero hh (fun k => if Nat.Coprime k 30 then (30:ℝ)/8 else 0) ?_
    intro k hk
    exact model_even_zero hk

end Conjectures.Goldbach.PacketEvenLagSupport_aux

theorem Conjectures.Goldbach.PacketEvenLagSupport :
let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume; let A := fun (n h : ℕ) (a : ℕ → ℝ) => ∑ k ∈ Finset.range (n+1-h), a k * a (k+h); let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0; let short := fun (n : ℕ) (a : ℕ → ℝ) => A n 0 a * V n 0 + 2*(∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h); let long := fun (n : ℕ) (a : ℕ → ℝ) => 2*(∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h); ∀ n : ℕ, 8 ≤ n → ∀ h : ℕ, Odd h → A n h (high n) = 0 ∧ A n h model = 0 := by
  exact Conjectures.Goldbach.PacketEvenLagSupport_aux.claim
