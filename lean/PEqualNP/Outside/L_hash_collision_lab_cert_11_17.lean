import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_11_17 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*12376)+19448*(∑ i,b i)≤(∑ i,Nat.choose (b i) 11)+q*330616 := by
  have h17_11 : Nat.choose 17 11 = 12376 := by decide
  have h17_10 : Nat.choose 17 10 = 19448 := by decide
  have hge : ∀ k : ℕ, 12376 + 19448 * (17 + k) ≤ Nat.choose (17 + k) 11 + 330616 := by
    intro k
    induction k with
    | zero =>
      rw [Nat.add_zero, h17_11]
    | succ k ih =>
      have hsucc : Nat.choose (17 + (k + 1)) 11 = Nat.choose (17 + k) 10 + Nat.choose (17 + k) 11 := by
        rw [show 17 + (k + 1) = (17 + k) + 1 by omega]
        exact Nat.choose_succ_succ' (17 + k) 10
      have hmono : 19448 ≤ Nat.choose (17 + k) 10 := by
        rw [← h17_10]
        exact Nat.choose_le_choose 10 (Nat.le_add_right 17 k)
      calc 12376 + 19448 * (17 + (k + 1))
        _ = (12376 + 19448 * (17 + k)) + 19448 := by ring
        _ ≤ (Nat.choose (17 + k) 11 + 330616) + Nat.choose (17 + k) 10 := Nat.add_le_add ih hmono
        _ = Nat.choose (17 + (k + 1)) 11 + 330616 := by rw [hsucc]; ring
  have hle : ∀ k : ℕ, k ≤ 17 → 12376 + 19448 * (17 - k) ≤ Nat.choose (17 - k) 11 + 330616 := by
    intro k hk
    induction k with
    | zero =>
      rw [Nat.sub_zero, h17_11]
    | succ k ih =>
      have ih' := ih (Nat.le_of_succ_le hk)
      have hsub : 17 - k = (17 - (k + 1)) + 1 := by omega
      have hsucc : Nat.choose (17 - k) 11 = Nat.choose (17 - (k + 1)) 10 + Nat.choose (17 - (k + 1)) 11 := by
        rw [hsub]
        exact Nat.choose_succ_succ' (17 - (k + 1)) 10
      have hmono : Nat.choose (17 - (k + 1)) 10 ≤ 19448 := by
        rw [← h17_10]
        exact Nat.choose_le_choose 10 (Nat.sub_le 17 (k + 1))
      have hmul : 19448 * (17 - k) = 19448 * (17 - (k + 1)) + 19448 := by
        rw [hsub, Nat.mul_add, Nat.mul_one]
      rw [hsucc, hmul] at ih'
      omega
  have hpt : ∀ n : ℕ, 12376 + 19448 * n ≤ Nat.choose n 11 + 330616 := by
    intro n
    by_cases hn : 17 ≤ n
    · have h := hge (n - 17)
      rwa [show 17 + (n - 17) = n by omega] at h
    · have h := hle (17 - n) (Nat.sub_le 17 n)
      rwa [show 17 - (17 - n) = n by omega] at h
  intro q b
  have hsum : ∑ i : Fin q, (12376 + 19448 * b i) ≤ ∑ i : Fin q, (Nat.choose (b i) 11 + 330616) :=
    Finset.sum_le_sum (fun i _ => hpt (b i))
  have hlhs : q * 12376 + 19448 * (∑ i : Fin q, b i) = ∑ i : Fin q, (12376 + 19448 * b i) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul, Finset.mul_sum]
  have hrhs : (∑ i : Fin q, Nat.choose (b i) 11) + q * 330616 = ∑ i : Fin q, (Nat.choose (b i) 11 + 330616) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul]
  rw [hlhs, hrhs]
  exact hsum
