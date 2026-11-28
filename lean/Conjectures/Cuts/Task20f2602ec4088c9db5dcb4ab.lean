import Mathlib
import Conjectures.Goldbach.SharpSingularSeriesRatios
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachLocalProduct TwistedGoldbachConductorRatio DirichletCharacter Finset
open B13BilateralVaughanReductionProof.BombieriVinogradov.LargeSieve
open scoped Classical BigOperators

namespace PartnerCount
theorem jacobi_transform {q : ℕ} [NeZero q] (A B : DirichletCharacter ℂ q) (m : ZMod q) :
    J A B m = unitCharacterSum (fun u : (ZMod q)ˣ => A (m-u)) B := by
  classical
  letI : Fintype (ZMod q)ˣ := Fintype.ofFinite _
  let e : ZMod q ≃ ZMod q :=
    ⟨fun x=>m-x, fun x=>m-x, fun x=>sub_sub_cancel m x, fun x=>sub_sub_cancel m x⟩
  have sw := Equiv.sum_comp e (fun x : ZMod q=>B x*A (m-x))
  change (∑x : ZMod q,B (m-x)*A (m-(m-x)))=_ at sw
  simp only [sub_sub_cancel] at sw
  calc
    J A B m = ∑ x : ZMod q, B (m-x)*A x := by
      unfold J;apply sum_congr rfl;intro x _;ring
    _ = ∑ x : ZMod q, B x*A (m-x) := sw
    _ = ∑ u : (ZMod q)ˣ, B (u:ZMod q)*A (m-u) := (sum_units_eq_sum_residues B _).symm
    _ = _ := by unfold unitCharacterSum;apply sum_congr rfl;intro x _;ring

end PartnerCount


namespace PartnerCount
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachLocalProduct TwistedGoldbachConductorRatio DirichletCharacter

theorem principal_norm_dvd {p k : ℕ} [NeZero (p^k)] (hp : p.Prime) (hk : 0 < k)
    (m : ℕ) (hm : p ∣ m) :
    ‖J (1 : DirichletCharacter ℂ (p^k)) 1 (m:ZMod (p^k))‖ = ((p^k:ℕ).totient:ℝ) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  let Target : ℕ → Prop := fun q => ∀ [NeZero q],
    ‖J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)‖=(q.totient:ℝ)
  have eq : p^j.succ = p*p^j := pow_succ' ..
  have old : Target (p*p^j) := by
    intro inst
    have tot : (p*p^j).totient = p^j*(p-1) := by rw [←eq,Nat.totient_prime_pow_succ hp]
    rw [tot]
    simpa only [hm,ite_true,Nat.cast_mul,Nat.cast_sub hp.one_le,Nat.cast_one] using
      ordinary_prime_power (p:=p) j m
  have result : Target (p^j.succ) := by rw [eq];exact old
  exact @result inferInstance

end PartnerCount


theorem Conjectures.Cuts.Task20f2602ec4088c9db5dcb4ab : (∀ (x1 x2 x3 : ℕ) [x4 : NeZero (x1 ^ x2)],   Nat.Prime x1 →     (0 : ℕ) < x2 →       Even x3 →         x1 ∣ x3 →           ∀ (x9 : DirichletCharacter ℂ (x1 ^ x2)) (x10 : Finset (DirichletCharacter ℂ (x1 ^ x2))),             have x11 : DirichletCharacter ℂ (x1 ^ x2) → DirichletCharacter ℂ (x1 ^ x2) → ℂ := fun (x11 x12 : DirichletCharacter ℂ (x1 ^ x2)) => ∑ x13 : ZMod (x1 ^ x2), x11 x13 * x12 (↑x3 - x13);             ∑ x12 ∈ x10, ‖x11 x9 x12 / x11 (1 : DirichletCharacter ℂ (x1 ^ x2)) (1 : DirichletCharacter ℂ (x1 ^ x2))‖ ^ (3 : ℕ) ≤ (1 : ℝ)) := by

  classical
  intro p k m inst hp hk _ hm A s
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  let q := p ^ k
  let a (u : (ZMod q)ˣ) : ℂ := A ((m : ZMod q) - (u : ZMod q))
  let v (χ : DirichletCharacter ℂ q) : ℝ := ‖unitCharacterSum a χ‖
  let D : ℝ := q.totient
  have hd : 0 < D := by dsimp [D, q]; exact_mod_cast Nat.totient_pos.mpr (pow_pos hp.pos k)
  have bound (S : Finset (DirichletCharacter ℂ q)) : ∑ χ ∈ S, v χ ^ 2 ≤ D ^ 2 := by
    calc
      _ ≤ ∑ χ : DirichletCharacter ℂ q, v χ ^ 2 :=
        Finset.sum_le_univ_sum_of_nonneg (fun χ => sq_nonneg _)
      _ = D * ∑ u : (ZMod q)ˣ, ‖a u‖ ^ 2 := by
        convert characterParseval_normSq a using 1 <;> congr 2 <;> ext u <;> simp
      _ ≤ D * ∑ _u : (ZMod q)ˣ, (1 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hd.le
        apply Finset.sum_le_sum
        intro u _
        have h := DirichletCharacter.norm_le_one A ((m : ZMod q) - (u : ZMod q))
        exact (pow_le_one₀ (norm_nonneg _) h)
      _ = _ := by simp [D, ZMod.card_units_eq_totient, pow_two]
  have point (χ : DirichletCharacter ℂ q) : v χ / D ≤ 1 := by
    have h : v χ ^ 2 ≤ D ^ 2 := by simpa using bound {χ}
    apply (div_le_one hd).mpr
    nlinarith [show 0 ≤ v χ from norm_nonneg _]
  have hn : ‖J (1 : DirichletCharacter ℂ q) 1 (m : ZMod q)‖ = D :=
    PartnerCount.principal_norm_dvd hp hk m hm
  change ∑ χ ∈ s, ‖J A χ (m : ZMod q) / J 1 1 (m : ZMod q)‖ ^ 3 ≤ 1
  calc
    _ = ∑ χ ∈ s, (v χ / D) ^ 3 := by
      apply Finset.sum_congr rfl
      intro χ _
      rw [norm_div, hn, PartnerCount.jacobi_transform]
    _ ≤ ∑ χ ∈ s, (v χ / D) ^ 2 := by
      apply Finset.sum_le_sum
      intro χ _
      rw [pow_succ]
      exact mul_le_of_le_one_right (sq_nonneg _) (point χ)
    _ = (∑ χ ∈ s, v χ ^ 2) / D ^ 2 := by simp_rw [div_pow]; rw [Finset.sum_div]
    _ ≤ 1 := (div_le_one (sq_pos_of_pos hd)).mpr (bound s)
