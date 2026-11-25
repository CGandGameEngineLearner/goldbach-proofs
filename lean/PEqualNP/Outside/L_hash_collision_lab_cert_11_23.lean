import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_11_23 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*1352078)+1144066*(∑ i,b i)≤(∑ i,Nat.choose (b i) 11)+q*26313518 := by
  have h23_11 : Nat.choose 23 11 = 1352078 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    decide +kernel
  have h23_10 : Nat.choose 23 10 = 1144066 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    decide +kernel
  have hge : ∀ k : ℕ, 1352078 + 1144066 * (23 + k) ≤ Nat.choose (23 + k) 11 + 26313518 := by
    intro k
    induction k with
    | zero =>
      rw [Nat.add_zero, h23_11]
    | succ k ih =>
      have hsucc : Nat.choose (23 + (k + 1)) 11 = Nat.choose (23 + k) 10 + Nat.choose (23 + k) 11 := by
        rw [show 23 + (k + 1) = (23 + k) + 1 by omega]
        exact Nat.choose_succ_succ' (23 + k) 10
      have hmono : 1144066 ≤ Nat.choose (23 + k) 10 := by
        rw [← h23_10]
        exact Nat.choose_le_choose 10 (Nat.le_add_right 23 k)
      calc 1352078 + 1144066 * (23 + (k + 1))
        _ = (1352078 + 1144066 * (23 + k)) + 1144066 := by ring
        _ ≤ (Nat.choose (23 + k) 11 + 26313518) + Nat.choose (23 + k) 10 := Nat.add_le_add ih hmono
        _ = Nat.choose (23 + (k + 1)) 11 + 26313518 := by rw [hsucc]; ring
  have hle : ∀ k : ℕ, k ≤ 23 → 1352078 + 1144066 * (23 - k) ≤ Nat.choose (23 - k) 11 + 26313518 := by
    intro k hk
    induction k with
    | zero =>
      rw [Nat.sub_zero, h23_11]
    | succ k ih =>
      have ih' := ih (Nat.le_of_succ_le hk)
      have hsub : 23 - k = (23 - (k + 1)) + 1 := by omega
      have hsucc : Nat.choose (23 - k) 11 = Nat.choose (23 - (k + 1)) 10 + Nat.choose (23 - (k + 1)) 11 := by
        rw [hsub]
        exact Nat.choose_succ_succ' (23 - (k + 1)) 10
      have hmono : Nat.choose (23 - (k + 1)) 10 ≤ 1144066 := by
        rw [← h23_10]
        exact Nat.choose_le_choose 10 (Nat.sub_le 23 (k + 1))
      have hmul : 1144066 * (23 - k) = 1144066 * (23 - (k + 1)) + 1144066 := by
        rw [hsub, Nat.mul_add, Nat.mul_one]
      rw [hsucc, hmul] at ih'
      omega
  have hpt : ∀ n : ℕ, 1352078 + 1144066 * n ≤ Nat.choose n 11 + 26313518 := by
    intro n
    by_cases hn : 23 ≤ n
    · have h := hge (n - 23)
      rwa [show 23 + (n - 23) = n by omega] at h
    · have h := hle (23 - n) (Nat.sub_le 23 n)
      rwa [show 23 - (23 - n) = n by omega] at h
  intro q b
  have hsum : ∑ i : Fin q, (1352078 + 1144066 * b i) ≤ ∑ i : Fin q, (Nat.choose (b i) 11 + 26313518) :=
    Finset.sum_le_sum (fun i _ => hpt (b i))
  have hlhs : q * 1352078 + 1144066 * (∑ i : Fin q, b i) = ∑ i : Fin q, (1352078 + 1144066 * b i) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul, Finset.mul_sum]
  have hrhs : (∑ i : Fin q, Nat.choose (b i) 11) + q * 26313518 = ∑ i : Fin q, (Nat.choose (b i) 11 + 26313518) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul]
  rw [hlhs, hrhs]
  exact hsum
