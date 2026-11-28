import Mathlib

theorem Conjectures.Cuts.Taskd21678ec247090d5559ae520 : (let ch := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length ≤ 2
  ∀ t : ℕ, 1 ≤ t → ((∃ p q : ℕ, ch p ∧ ch q ∧ p+q=6*t+4 ∧ ch (q+6)) ↔
    (ch (6*t+1) ∧ ch (6*t+7)) ∨ ∃ a b : ℕ, a+b+1=t ∧ ch (6*a+5) ∧ ch (6*b+5) ∧ ch (6*b+11))) := by
  intro ch t ht
  have residue (p : ℕ) (h : p.Prime) (h2 : p≠2) (h3 : p≠3) : p % 6=1 ∨ p % 6=5 := by
    have nd2 : ¬2∣p := fun hd => h2 ((Nat.prime_dvd_prime_iff_eq (by decide) h).mp hd).symm
    have nd3 : ¬3∣p := fun hd => h3 ((Nat.prime_dvd_prime_iff_eq (by decide) h).mp hd).symm
    omega
  constructor
  · rintro ⟨p,q,hp,hq,he,hs⟩
    by_cases h : p=3
    · left
      have eq : q=6*t+1 := by omega
      exact ⟨eq ▸ hq,(show q+6=6*t+7 by omega) ▸ hs⟩
    · have pp := hp.1
      have qp := hq.1
      have qq := hs.1
      have p2 : p≠2 := by
        intro h2
        have d : 2∣q := by omega
        have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 2) qp).mp d
        omega
      have q2 : q≠2 := by
        intro h2
        have d : 2∣p := by omega
        have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 2) pp).mp d
        omega
      have q3 : q≠3 := by
        rintro rfl
        exact (by decide : ¬ Nat.Prime 9) qq
      have rp := residue p pp p2 h
      have rq := residue q qp q2 q3
      have ep : 6*(p/6)+5=p := by omega
      have eq : 6*(q/6)+5=q := by omega
      right
      exact ⟨p/6,q/6,by omega,ep.symm ▸ hp,eq.symm ▸ hq,(show 6*(q/6)+11=q+6 by omega).symm ▸ hs⟩
  · rintro (⟨hq,hs⟩|⟨a,b,e,hp,hq,hs⟩)
    · have hthree : ch 3 := by
        refine ⟨by decide,?_⟩
        change (Nat.primeFactorsList 5).length ≤ 2
        rw [Nat.primeFactorsList_prime (by decide : Nat.Prime 5)]
        decide
      refine ⟨3,6*t+1,hthree,hq,by omega,?_⟩
      simpa only [show 6*t+1+6=6*t+7 by omega] using hs
    · refine ⟨6*a+5,6*b+5,hp,hq,by omega,?_⟩
      simpa only [show 6*b+5+6=6*b+11 by omega] using hs
