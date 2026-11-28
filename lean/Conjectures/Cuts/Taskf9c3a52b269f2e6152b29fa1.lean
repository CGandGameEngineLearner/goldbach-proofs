import Mathlib

private theorem minPair {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a≤b) :
    (a*b).minFac=a := by
  have hp : ((a*b).minFac).Prime := Nat.minFac_prime (by have := ha.two_le; have := hb.two_le; nlinarith)
  have hle := Nat.minFac_le_of_dvd ha.two_le (show a∣a*b from dvd_mul_right _ _)
  rcases hp.dvd_mul.mp (Nat.minFac_dvd (a*b)) with h|h
  · exact (Nat.prime_dvd_prime_iff_eq hp ha).mp h
  · have := (Nat.prime_dvd_prime_iff_eq hp hb).mp h
    omega

theorem Conjectures.Cuts.Taskf9c3a52b269f2e6152b29fa1 : (∀ p : ℕ, (∃ a b : ℕ, Nat.Prime a ∧ Nat.Prime b ∧ a*b=p+2 ∧ a^5≤p+2 ∧ p+2≤a^6) ↔
    (let a := (p+2).minFac
      let b := (p+2)/a
      Nat.Prime b ∧ a^4≤b ∧ b≤a^5)) := by
  intro p
  constructor
  · rintro ⟨a,b,ha,hb,hm,hl,hu⟩
    rw [← hm] at hl hu ⊢
    have lo : a^4 ≤ b := by
      apply Nat.le_of_mul_le_mul_left _ ha.pos
      simpa only [← pow_succ' a 4] using hl
    have hi : b ≤ a^5 := by
      apply Nat.le_of_mul_le_mul_left _ ha.pos
      simpa only [← pow_succ' a 5] using hu
    have ab : a≤b := (Nat.le_self_pow (by decide : 4≠0) _).trans lo
    dsimp only
    rw [minPair ha hb ab,Nat.mul_div_cancel_left _ ha.pos]
    exact ⟨hb,lo,hi⟩
  · dsimp only
    let a := (p+2).minFac
    let b := (p+2)/a
    rintro ⟨hb,hl,hu⟩
    have hm : a*b=p+2 := Nat.mul_div_cancel' (Nat.minFac_dvd _)
    refine ⟨a,b,Nat.minFac_prime (by omega),hb,hm,?_,?_⟩
    · calc
        a^5 = a*a^4 := pow_succ' _ _
        _ ≤ a*b := Nat.mul_le_mul_left a hl
        _ = _ := hm
    · calc
        p+2 = a*b := hm.symm
        _ ≤ a*a^5 := Nat.mul_le_mul_left a hu
        _ = _ := (pow_succ' _ _).symm
