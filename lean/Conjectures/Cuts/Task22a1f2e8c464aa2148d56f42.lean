import Mathlib

open Finset

theorem Conjectures.Cuts.Task22a1f2e8c464aa2148d56f42 :
∀ (x1 : ℕ) (x2 : ℕ → Polynomial ℕ),   have x3 : Finset ℕ :=     {x3 ∈ Finset.range (x1 + (1 : ℕ)) |       Nat.Prime x3 ∧         have x4 : ℕ := (x3 + (2 : ℕ)).minFac;         have x5 : ℕ := (x3 + (2 : ℕ)) / x4;         Nat.Prime x5 ∧ x4 ^ (4 : ℕ) ≤ x5 ∧ x5 ≤ x4 ^ (5 : ℕ)};   have x4 : Finset (ℕ × ℕ) := {x4 ∈ (Finset.range (x1 + (3 : ℕ))).product (Finset.range (x1 + (3 : ℕ))) | Nat.Prime x4.1 ∧ Nat.Prime x4.2 ∧ x4.1 ^ (4 : ℕ) ≤ x4.2 ∧ x4.2 ≤ x4.1 ^ (5 : ℕ) ∧ x4.1 * x4.2 ≤ x1 + (2 : ℕ) ∧ Nat.Prime (x4.1 * x4.2 - (2 : ℕ))};   ∑ x5 ∈ x3, x2 (x5 + (2 : ℕ)) = ∑ x5 ∈ x4, x2 (x5.1 * x5.2) := by
  intro N w
  dsimp only
  let d (p : ℕ) := (p+2).minFac
  let b (p : ℕ) := (p+2)/d p
  have hd (p : ℕ) : (d p).Prime := Nat.minFac_prime (by omega)
  have hdb (p : ℕ) : d p * b p = p+2 := Nat.mul_div_cancel' (Nat.minFac_dvd _)
  apply Finset.sum_bij (fun p _ => (d p, b p))
  · intro p hp
    obtain ⟨hr,hp',hb,hlo,hhi⟩ := mem_filter.mp hp
    have hb' : (b p).Prime := hb
    have hN := mem_range.mp hr
    have hprod := hdb p
    have hdle : d p ≤ p+2 := Nat.le_of_dvd (by omega) (Nat.minFac_dvd _)
    have hble : b p ≤ p+2 := Nat.div_le_self _ _
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩,
      hd p,hb',hlo,hhi,by simpa [hprod] using (show p+2≤N+2 by omega),by simpa [hprod] using hp'⟩
  · intro p hp q hq he
    have hh := congrArg (fun z : ℕ × ℕ => z.1*z.2) he
    change d p*b p=d q*b q at hh
    rw [hdb,hdb] at hh
    omega
  · rintro ⟨a,c⟩ hc
    obtain ⟨_,ha,hc',hlo,hhi,hle,hprime⟩ := mem_filter.mp hc
    dsimp only at ha hc' hlo hhi hle hprime
    have hac : a ≤ c := (Nat.le_self_pow (by decide : (4:ℕ) ≠ 0) a).trans hlo
    have hs : 2 ≤ a*c := ha.two_le.trans (Nat.le_mul_of_pos_right a hc'.pos)
    let p := a*c-2
    have he : p+2=a*c := by dsimp [p]; omega
    have hda : d p ≤ a := Nat.minFac_le_of_dvd ha.two_le (he ▸ dvd_mul_right a c)
    have hdvd : d p ∣ a*c := he ▸ Nat.minFac_dvd _
    have deq : d p=a := by
      rcases (hd p).dvd_mul.mp hdvd with hu | hv
      · exact (Nat.prime_dvd_prime_iff_eq (hd p) ha).mp hu
      · have := (Nat.prime_dvd_prime_iff_eq (hd p) hc').mp hv
        omega
    have beq : b p=c := by
      apply Nat.eq_of_mul_eq_mul_left ha.pos
      simpa only [deq] using (hdb p).trans he
    refine ⟨p,mem_filter.mpr ⟨mem_range.mpr (by omega),hprime,?_⟩,?_⟩
    · change (b p).Prime ∧ d p ^ 4 ≤ b p ∧ b p ≤ d p ^ 5
      simpa only [deq,beq] using And.intro hc' (And.intro hlo hhi)
    · exact Prod.ext deq beq
  · intro p hp
    exact congrArg w (hdb p).symm
