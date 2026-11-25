import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_5_10 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*252)+210*(∑ i,b i)≤(∑ i,Nat.choose (b i) 5)+q*2100 := by
  intro q b
  have hT : Nat.choose 10 4 = 210 := by
    rw [Nat.choose_eq_factorial_div_factorial] <;> norm_num
  have hT' : Nat.choose 10 5 = 252 := by
    rw [Nat.choose_eq_factorial_div_factorial] <;> norm_num
  have hle : 252 ≤ 2100 := by norm_num
  have key : ∀ x : ℕ, 210 * x ≤ Nat.choose x 5 + (2100 - 252) := by
    intro x
    by_cases hx : x ≤ 10
    · have head : ∀ n, ∀ y, 10 - y = n → y ≤ 10 → 210 * y ≤ Nat.choose y 5 + (2100 - 252) := by
        intro n
        induction n with
        | zero =>
          intro y hy _
          have hyT : y = 10 := by omega
          subst hyT
          norm_num [hT', hT]
        | succ n ih =>
          intro y hy hleB
          have hstep : 210 * (y + 1) ≤ Nat.choose (y + 1) 5 + (2100 - 252) :=
            ih (y + 1) (by omega) (by omega)
          have hpas : Nat.choose (y + 1) 5 = Nat.choose y 4 + Nat.choose y 5 :=
            Nat.choose_succ_succ y 4
          have hmono : Nat.choose y 4 ≤ 210 := by
            have h1 : Nat.choose y 4 ≤ Nat.choose 10 4 :=
              Nat.choose_le_choose 4 hleB
            omega
          rw [hpas] at hstep
          have hmul : 210 * (y + 1) = 210 * y + 210 := by ring
          rw [hmul] at hstep
          omega
      exact head (10 - x) x rfl hx
    · have hxB : 10 ≤ x := by omega
      have tail : ∀ x, 10 ≤ x → 210 * x ≤ Nat.choose x 5 + (2100 - 252) := by
        intro x hx2
        induction x, hx2 using Nat.le_induction with
        | base => norm_num [hT', hT]
        | succ y hy ih =>
          have hmono : 210 ≤ Nat.choose y 4 := by
            have h1 : Nat.choose 10 4 ≤ Nat.choose y 4 :=
              Nat.choose_le_choose 4 hy
            omega
          have hpas : Nat.choose (y + 1) 5 = Nat.choose y 4 + Nat.choose y 5 :=
            Nat.choose_succ_succ y 4
          rw [hpas]
          have hmul : 210 * (y + 1) = 210 * y + 210 := by ring
          rw [hmul]
          omega
      exact tail x hxB
  have h1 : 210 * (∑ i, b i) ≤ ∑ i, (Nat.choose (b i) 5 + (2100 - 252)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => key (b i))
  have h2 : ∑ i, (Nat.choose (b i) 5 + (2100 - 252))
      = (∑ i, Nat.choose (b i) 5) + q * (2100 - 252) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [h2] at h1
  have h3 : q * 252 + q * (2100 - 252) = q * 2100 := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hle]
  omega
