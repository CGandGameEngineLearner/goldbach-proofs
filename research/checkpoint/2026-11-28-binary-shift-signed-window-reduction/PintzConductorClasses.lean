import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Finset
namespace Goldbach.PintzClasses
open scoped Classical

def active (C : Finset ℕ) (d m : ℕ) := C.filter (fun r => r ∣ d*m)

noncomputable def largeClass (C : Finset ℕ) (d X : ℕ) (θ : ℝ) :=
  (Icc 1 X).filter (fun m => (X:ℝ)^θ < ((active C d m).lcm id : ℕ))

theorem reduced_conductor {q d m : ℕ} (hd : 0 < d) :
    q ∣ d*m ↔ q / q.gcd d ∣ m := by
  let g := q.gcd d
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ hd
  have hq : g*(q/g) = q := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have hh : g*(d/g) = d := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have hcan : q ∣ d*m ↔ q/g ∣ (d/g)*m := by
    calc
      q ∣ d*m ↔ g*(q/g) ∣ (g*(d/g))*m := by rw [hq,hh]
      _ ↔ q/g ∣ (d/g)*m := by rw [mul_assoc g (d/g) m, Nat.mul_dvd_mul_iff_left hg]
  rw [hcan]
  exact ⟨(Nat.coprime_div_gcd_div_gcd hg).dvd_of_dvd_mul_left,
    fun h => dvd_mul_of_dvd_right h _⟩

theorem scaled_multiples (X q d : ℕ) (hd : 0 < d) :
    ((Icc 1 X).filter (fun m => q ∣ d*m)).card * q ≤ X*d := by
  let g := q.gcd d
  let r := q/g
  let A := (Icc 1 X).filter (fun m => q ∣ d*m)
  have hs : A ⊆ (range X.succ).filter (fun k => k ≠ 0 ∧ r ∣ k) := by
    intro k hk
    obtain ⟨hkI,hkq⟩ := mem_filter.mp hk
    obtain ⟨hklo,hkhi⟩ := mem_Icc.mp hkI
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),by omega,(reduced_conductor hd).mp hkq⟩
  have hA : A.card ≤ X/r := (card_le_card hs).trans_eq (Nat.card_multiples' X r)
  have hX : A.card*r ≤ X := (Nat.mul_le_mul_right r hA).trans (Nat.div_mul_le_self ..)
  have hq : r*g = q := Nat.div_mul_cancel (Nat.gcd_dvd_left ..)
  have hg : g ≤ d := Nat.le_of_dvd hd (Nat.gcd_dvd_right ..)
  change A.card*q ≤ X*d
  calc
    _ = A.card*r*g := by rw [mul_assoc,hq]
    _ ≤ X*g := Nat.mul_le_mul_right _ hX
    _ ≤ _ := Nat.mul_le_mul_left _ hg

/-- Pintz, Exceptional set II, (2.26)–(2.30). The conductor family may depend on the scale. -/
theorem largeClass_bound (C : Finset ℕ) {d X : ℕ} (hd : 0<d) (hX : 0<X) (θ : ℝ) :
    ((largeClass C d X θ).card:ℝ) ≤ (2:ℝ)^C.card * d * (X:ℝ)^(1-θ) := by
  let Q (s : Finset ℕ) := s.lcm id
  let fiber (s : Finset ℕ) := (Icc 1 X).filter (fun m => Q s ∣ d*m ∧ (X:ℝ)^θ < (Q s:ℝ))
  have hs : largeClass C d X θ ⊆ C.powerset.biUnion fiber := by
    intro m hm
    obtain ⟨hmI,hq⟩ := mem_filter.mp hm
    refine mem_biUnion.mpr ⟨active C d m,mem_powerset.mpr (filter_subset ..), mem_filter.mpr ⟨hmI,?_,hq⟩⟩
    exact lcm_dvd_iff.mpr fun r hr => (mem_filter.mp hr).2
  have hf (s : Finset ℕ) : ((fiber s).card:ℝ) ≤ d*(X:ℝ)^(1-θ) := by
    by_cases hq : (X:ℝ)^θ < (Q s:ℝ)
    · have h := scaled_multiples X (Q s) d hd
      have hh : ((fiber s).card:ℝ) * (Q s:ℝ) ≤ (X:ℝ)*d := by
        simpa [fiber,hq] using (show ((((Icc 1 X).filter (fun m => Q s ∣ d*m)).card:ℝ) * (Q s:ℝ) ≤ (X:ℝ)*d) by exact_mod_cast h)
      have hXp : (0:ℝ)<X := by exact_mod_cast hX
      apply le_of_mul_le_mul_right (a := (X:ℝ)^θ) _ (Real.rpow_pos_of_pos hXp _)
      calc
        _ ≤ ((fiber s).card:ℝ)*(Q s:ℝ) := mul_le_mul_of_nonneg_left hq.le (by positivity)
        _ ≤ (X:ℝ)*d := hh
        _ = _ := by rw [mul_assoc, ← Real.rpow_add hXp, sub_add_cancel,Real.rpow_one]; ring
    · simp [fiber,hq]; positivity
  have hcard := (card_le_card hs).trans card_biUnion_le
  calc
    _ ≤ ∑ s ∈ C.powerset, ((fiber s).card:ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ _s ∈ C.powerset, (d:ℝ)*(X:ℝ)^(1-θ) := sum_le_sum fun s _ => hf s
    _ = _ := by simp [mul_assoc]

end Goldbach.PintzClasses
