import Mathlib

theorem Conjectures.Cuts.Taskd9a10c67c5cbd6c98efa985d : (∀ m : ℕ, (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=2*m ∧ (Nat.dist p q)^4 ≤ (2*m)^3) ↔
    ∃ r : ℕ, r ≤ m ∧ 2*r^4 ≤ m^3 ∧ Nat.Prime (m-r) ∧ Nat.Prime (m+r)) := by
  intro m
  have forward (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (he : p+q=2*m)
      (hle : p ≤ q) (hg : (Nat.dist p q)^4 ≤ (2*m)^3) :
      ∃ r : ℕ, r ≤ m ∧ 2*r^4 ≤ m^3 ∧ Nat.Prime (m-r) ∧ Nat.Prime (m+r) := by
    let r := m-p
    have pp : m-r=p := by dsimp [r];omega
    have qq : m+r=q := by dsimp [r];omega
    have d : Nat.dist p q=2*r := by rw [Nat.dist_eq_sub_of_le hle];dsimp [r];omega
    rw [d,mul_pow,mul_pow] at hg
    refine ⟨r,Nat.sub_le _ _,?_,pp.symm ▸ hp,qq.symm ▸ hq⟩
    norm_num at hg
    omega
  constructor
  · rintro ⟨p,q,hp,hq,he,hg⟩
    rcases le_total p q with h|h
    · exact forward p q hp hq he h hg
    · exact forward q p hq hp (by omega) h (by simpa only [Nat.dist_comm q p] using hg)
  · rintro ⟨r,hr,hpow,hp,hq⟩
    refine ⟨m-r,m+r,hp,hq,by omega,?_⟩
    rw [Nat.dist_eq_sub_of_le (by omega),show m+r-(m-r)=2*r by omega,mul_pow,mul_pow]
    norm_num
    omega
