import Mathlib
import Conjectures.Goldbach.RoughFifthMass
import Conjectures.Goldbach.SelbergSharpLargeSieve

open scoped Classical
open Finset OAI.LargePrimeGaps
open Conjectures.Goldbach.SelbergSharpLargeSieve_aux.GoldbachBDHSharp.OAI.Ostmann

namespace SharpMultiplicativeInterval

private theorem intervalSum {G : Type*} [AddCommMonoid G] (M L : ℕ) (f : ℕ → G) :
    (∑ j : Fin L, f (M+j.val)) = ∑ n ∈ Ico M (M+L), f n := by
  rw [Fin.sum_univ_eq_sum_range (fun j => f (M+j)) L, Finset.sum_Ico_eq_sum_range]
  simp

private theorem paddedSum {G : Type*} [AddCommMonoid G] (M L : ℕ) (f : ℕ → G) :
    (∑ n : Fin (M+L), if M ≤ n.val then f n.val else 0) = ∑ n ∈ Ico M (M+L), f n := by
  rw [Fin.sum_univ_eq_sum_range (fun n => if M ≤ n then f n else 0) (M+L), ← Finset.sum_filter]
  congr 1
  ext n
  simp [and_comm]

private theorem denominatorSum (Q : ℕ) (f : ℕ → ℝ) :
    (∑ q : Fin Q, f (q.val+1)) = ∑ q ∈ Icc 1 Q, f q := by
  have he : Icc 1 Q = Ico 1 (1+Q) := by ext q; simp; omega
  rw [he, ← intervalSum]
  simp [Nat.add_comm]

private theorem phase_eq (n : ℝ) (r : ℝ) :
    bvExp (n*r) = sieveHalfPhase (2*(n:ℝ)*r) := by
  unfold bvExp sieveHalfPhase
  push_cast
  congr 1
  ring

theorem sharp (M L Q : ℕ) (a : ℕ → ℂ) :
    (∑ q ∈ Icc 1 Q, ((q:ℝ)/q.totient) * ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive),
      ‖∑ n ∈ Ico M (M+L), a n * χ (n : ZMod q)‖^2) ≤
      ((L:ℝ)+(Q:ℝ)^2) * ∑ n ∈ Ico M (M+L), ‖a n‖^2 := by
  classical
  by_cases hQ : Q=0
  · subst Q
    simp
    positivity
  let I := (q : Fin Q) × (ZMod (q.val+1))ˣ
  let x : I → ℝ := fun i => (fareyFrequency i : ℝ)
  let δ := 1/(Q:ℝ)^2
  have hden (i : I) : (fareyFrequency i).den ≤ Q := by
    rcases i with ⟨q,u⟩
    rw [fareyFrequency, unitFrequency_den]
    exact q.isLt
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsep : CircleSeparated x δ := by
    intro s t hst m
    simpa only [x,δ,fareyFrequency,Nat.cast_pow] using rational_frequency_separation
      (unitFrequency_bounds s.2) (unitFrequency_bounds t.2)
      (fun he => hst (fareyFrequency_injective Q he)) (hden s) (hden t) m
  let pad : Fin (M+L) → ℂ := fun n => if M ≤ n.val then a n.val else 0
  have hχ {q : ℕ} (χ : DirichletCharacter ℂ q) :
      sequenceCharacterSum pad χ = ∑ n ∈ Ico M (M+L), a n * χ (n : ZMod q) := by
    unfold sequenceCharacterSum
    simpa only [pad,ite_mul,zero_mul] using paddedSum M L (fun n => a n * χ (n : ZMod q))
  have hu {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) :
      modularFourierSum (q:=q) pad (u : ZMod q) =
      ∑ j : Fin L, a (M+j.val) * sieveHalfPhase (2*((M:ℝ)+j.val)*(unitFrequency u:ℝ)) := by
    rw [modularFourierSum_eq_bvExp]
    simp only [pad,ite_mul,zero_mul]
    rw [paddedSum M L (fun n => a n * bvExp ((n:ℝ)*(unitFrequency u:ℝ))), ← intervalSum]
    simp only [Nat.cast_add,phase_eq]
  have hs := separated_additive_sieve x δ hδ hsep L (M:ℝ) (fun j => a (M+j.val))
  have hδ' : 1/δ = (Q:ℝ)^2 := by simp [δ]
  rw [hδ'] at hs
  change (∑ i : I, ‖∑ j : Fin L, a (M+j.val)*sieveHalfPhase (2*((M:ℝ)+j.val)*x i)‖^2) ≤
    ((L:ℝ)+(Q:ℝ)^2) * ∑ j : Fin L, ‖a (M+j.val)‖^2 at hs
  rw [intervalSum M L (fun n => ‖a n‖^2)] at hs
  rw [← denominatorSum]
  have bound (q : Fin Q) := primitive_character_energy_le (q:=q.val+1) pad
  simp only [hχ] at bound
  refine (Finset.sum_le_sum (fun q _ => bound q)).trans ?_
  rw [Fintype.sum_sigma] at hs
  simpa only [hu,x,fareyFrequency] using hs

end SharpMultiplicativeInterval

theorem Conjectures.Goldbach.SharpMultiplicativeLargeSieve : (letI := Classical.propDecidable; ∀ (M L Q : ℕ) (a : ℕ → ℂ), ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (Nat.totient q : ℝ)) * ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive), ‖∑ n ∈ Finset.Ico M (M + L), a n * χ (n : ZMod q)‖ ^ 2 ≤ ((L : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ico M (M + L), ‖a n‖ ^ 2) := by
  classical
  exact SharpMultiplicativeInterval.sharp
