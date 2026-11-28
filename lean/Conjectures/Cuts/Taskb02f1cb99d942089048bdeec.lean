import Mathlib

open scoped BigOperators

private def binTerm (n i : ℕ) := n.choose i * 85^i * 915^(n-i)

private theorem bin_adj {n i : ℕ} (h : i < n) :
    binTerm n (i+1) * (915*(i+1)) = binTerm n i * (85*(n-i)) := by
  have pw : 915^(n-i) = 915^(n-(i+1))*915 := by
    rw [←pow_succ]; congr 1;omega
  unfold binTerm
  rw [pw,pow_succ 85]
  calc _ = (n.choose (i+1)*(i+1))*(85^i*85*915^(n-(i+1))*915) := by ring
       _ = _ := by rw [Nat.choose_succ_right_eq];ring

private theorem bin_up {t i : ℕ} (h : i < 85*t) :
    binTerm (1000*t) i ≤ binTerm (1000*t) (i+1) := by
  have hn : i<1000*t := by omega
  have cmp : 915*(i+1) ≤ 85*(1000*t-i) := by omega
  apply Nat.le_of_mul_le_mul_right (c := 915*(i+1))
  · rw [bin_adj hn]
    exact Nat.mul_le_mul_left _ cmp
  · positivity

private theorem bin_down {t i : ℕ} (h : 85*t ≤ i) (hn : i < 1000*t) :
    binTerm (1000*t) (i+1) ≤ binTerm (1000*t) i := by
  have cmp : 85*(1000*t-i) ≤ 915*(i+1) := by omega
  apply Nat.le_of_mul_le_mul_right (c := 915*(i+1))
  · rw [bin_adj hn]
    exact Nat.mul_le_mul_left _ cmp
  · positivity

private theorem binMode (t i : ℕ) (hi : i≤1000*t) :
    (1000*t).choose i * 85^i * 915^(1000*t-i) ≤
      (1000*t).choose (85*t) * 85^(85*t) * 915^(915*t) := by
  rw [show 915*t=1000*t-85*t by omega]
  change binTerm _ _ ≤ binTerm _ _
  rcases le_total i (85*t) with h | h
  · induction h using Nat.decreasingInduction with
    | self => exact le_rfl
    | of_succ j hj ih => exact (bin_up hj).trans (ih (by omega))
  · induction h with
    | refl => exact le_rfl
    | @step j hj ih => exact (bin_down hj (by omega)).trans (ih (by omega))



theorem Conjectures.Cuts.Taskb02f1cb99d942089048bdeec : (∀ (x1 : ℕ), (2 : ℕ) ^ ((419 : ℕ) * x1) ≤ ((1000 : ℕ) * x1 + (1 : ℕ)) * ((1000 : ℕ) * x1).choose ((85 : ℕ) * x1)) := by

  intro t
  have checkpoint : (2:ℕ)^419 * (85^85 * 915^915) ≤ 1000^1000 := by decide +kernel
  have lower := Nat.pow_le_pow_left checkpoint t
  simp only [mul_pow, ← pow_mul] at lower
  let weight : ℕ := 85^(85*t) * 915^(915*t)
  have upper : (1000 : ℕ)^(1000*t) ≤
      (1000*t+1) * (1000*t).choose (85*t) * weight := by
    calc
      _ = (85+915 : ℕ)^(1000*t) := rfl
      _ = _ := add_pow 85 915 (1000*t)
      _ ≤ ∑ _i ∈ Finset.range (1000*t+1),
            ((1000*t).choose (85*t) * 85^(85*t) * 915^(915*t)) := by
        apply Finset.sum_le_sum
        intro i hi
        have le := binMode t i (by simpa using Finset.mem_range.mp hi)
        simpa only [Nat.cast_id, mul_comm, mul_left_comm, mul_assoc] using le
      _ = _ := by simp [weight, mul_assoc]
  apply Nat.le_of_mul_le_mul_right (c := weight) _ (by dsimp [weight]; positivity)
  exact le_trans lower upper
