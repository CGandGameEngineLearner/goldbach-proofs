import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_5_14 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*2002)+1001*(∑ i,b i)≤(∑ i,Nat.choose (b i) 5)+q*14014 := by
  intro q b
  have hT : Nat.choose 14 4 = 1001 := by
    rw [Nat.choose_eq_factorial_div_factorial] <;> norm_num
  have hT' : Nat.choose 14 5 = 2002 := by
    rw [Nat.choose_eq_factorial_div_factorial] <;> norm_num
  have hle : 2002 ≤ 14014 := by norm_num
  have key : ∀ x : ℕ, 1001 * x ≤ Nat.choose x 5 + (14014 - 2002) := by
    intro x
    by_cases hx : x ≤ 14
    · have head : ∀ n, ∀ y, 14 - y = n → y ≤ 14 → 1001 * y ≤ Nat.choose y 5 + (14014 - 2002) := by
        intro n
        induction n with
        | zero =>
          intro y hy _
          have hyT : y = 14 := by omega
          subst hyT
          norm_num [hT', hT]
        | succ n ih =>
          intro y hy hleB
          have hstep : 1001 * (y + 1) ≤ Nat.choose (y + 1) 5 + (14014 - 2002) :=
            ih (y + 1) (by omega) (by omega)
          have hpas : Nat.choose (y + 1) 5 = Nat.choose y 4 + Nat.choose y 5 :=
            Nat.choose_succ_succ y 4
          have hmono : Nat.choose y 4 ≤ 1001 := by
            have h1 : Nat.choose y 4 ≤ Nat.choose 14 4 :=
              Nat.choose_le_choose 4 hleB
            omega
          rw [hpas] at hstep
          have hmul : 1001 * (y + 1) = 1001 * y + 1001 := by ring
          rw [hmul] at hstep
          omega
      exact head (14 - x) x rfl hx
    · have hxB : 14 ≤ x := by omega
      have tail : ∀ x, 14 ≤ x → 1001 * x ≤ Nat.choose x 5 + (14014 - 2002) := by
        intro x hx2
        induction x, hx2 using Nat.le_induction with
        | base => norm_num [hT', hT]
        | succ y hy ih =>
          have hmono : 1001 ≤ Nat.choose y 4 := by
            have h1 : Nat.choose 14 4 ≤ Nat.choose y 4 :=
              Nat.choose_le_choose 4 hy
            omega
          have hpas : Nat.choose (y + 1) 5 = Nat.choose y 4 + Nat.choose y 5 :=
            Nat.choose_succ_succ y 4
          rw [hpas]
          have hmul : 1001 * (y + 1) = 1001 * y + 1001 := by ring
          rw [hmul]
          omega
      exact tail x hxB
  have h1 : 1001 * (∑ i, b i) ≤ ∑ i, (Nat.choose (b i) 5 + (14014 - 2002)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => key (b i))
  have h2 : ∑ i, (Nat.choose (b i) 5 + (14014 - 2002))
      = (∑ i, Nat.choose (b i) 5) + q * (14014 - 2002) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [h2] at h1
  have h3 : q * 2002 + q * (14014 - 2002) = q * 14014 := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hle]
  omega
