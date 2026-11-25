import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_2_15 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*105)+15*(∑ i,b i)≤(∑ i,Nat.choose (b i) 2)+q*225 := by
  intro q b
  have hT : Nat.choose 15 1 = 15 := by rw [Nat.choose_eq_factorial_div_factorial] <;> norm_num
  have hT' : Nat.choose 15 2 = 105 := by rw [Nat.choose_eq_factorial_div_factorial] <;> norm_num
  have key : ∀ x : ℕ, 15 * x ≤ Nat.choose x 2 + 120 := by
    intro x
    by_cases hx : x ≤ 15
    · have head : ∀ n, ∀ y, 15 - y = n → y ≤ 15 → 15 * y ≤ Nat.choose y 2 + 120 := by
        intro n
        induction n with
        | zero =>
          intro y hy _
          have hyT : y = 15 := by omega
          subst hyT
          rw [hT']
          norm_num
        | succ n ih =>
          intro y hy hle
          have hylt : y < 15 := by omega
          have hstep : 15 * (y + 1) ≤ Nat.choose (y + 1) 2 + 120 := ih (y + 1) (by omega) (by omega)
          have hpas : Nat.choose (y + 1) 2 = Nat.choose y 1 + Nat.choose y 2 :=
            Nat.choose_succ_succ y 1
          have hmono : Nat.choose y 1 ≤ 15 := by
            have h1 : Nat.choose y 1 ≤ Nat.choose 15 1 := Nat.choose_le_choose 1 (by omega)
            omega
          rw [hpas] at hstep
          have hmul : 15 * (y + 1) = 15 * y + 15 := by ring
          rw [hmul] at hstep
          omega
      exact head (15 - x) x rfl hx
    · have hxT : 15 ≤ x := by omega
      have tail : ∀ x, 15 ≤ x → 15 * x ≤ Nat.choose x 2 + 120 := by
        intro x hx2
        induction x, hx2 using Nat.le_induction with
        | base =>
          rw [hT']
          norm_num
        | succ y hy ih =>
          have hmono : 15 ≤ Nat.choose y 1 := by
            have h1 : Nat.choose 15 1 ≤ Nat.choose y 1 := Nat.choose_le_choose 1 hy
            omega
          have hpas : Nat.choose (y + 1) 2 = Nat.choose y 1 + Nat.choose y 2 :=
            Nat.choose_succ_succ y 1
          rw [hpas]
          have hmul : 15 * (y + 1) = 15 * y + 15 := by ring
          rw [hmul]
          omega
      exact tail x hxT
  have h1 : 15 * (∑ i, b i) ≤ ∑ i, (Nat.choose (b i) 2 + 120) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => key (b i))
  have h2 : ∑ i, (Nat.choose (b i) 2 + 120) = (∑ i, Nat.choose (b i) 2) + q * 120 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [h2] at h1
  have h3 : q * 105 + q * 120 = q * 225 := by ring
  omega
