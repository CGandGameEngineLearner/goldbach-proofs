import Mathlib

open Finset

theorem PEqualNP.Outside.L_hash_collision_lab_cert_9_18 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*48620)+43758*(∑ i,b i)≤(∑ i,Nat.choose (b i) 9)+q*787644 := by
  classical
  intro q b
  have hpoint : ∀ m:ℕ, 43758*m + 48620 ≤ Nat.choose m 9 + 787644 := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      by_cases hm : m ≤ 19
      · interval_cases m <;> norm_num [Nat.choose]
      · have hm19 : 19 < m := by omega
        obtain ⟨k, rfl⟩ : ∃ k, m = k+1 := by use m-1; omega
        have hk19 : 19 ≤ k := by omega
        rw [Nat.choose_succ_succ]
        have h8 : 43758 ≤ Nat.choose k 8 := by
          have : Nat.choose 18 8 ≤ Nat.choose k 8 := Nat.choose_le_choose 8 (by omega)
          norm_num at this ⊢
          exact this
        have ihk := ih k (by omega)
        change 43758*(k+1) + 48620 ≤ Nat.choose k 8 + Nat.choose k 9 + 787644
        omega
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => hpoint (b i))
  -- hsum: Σ_i (43758*b_i + 48620) ≤ Σ_i (choose(b_i,9) + 787644)
  have hleft : (∑ i : Fin q, (43758*b i + 48620)) = 43758*(∑ i, b i) + q*48620 := by
    simp [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Fintype.card_fin]
  have hright : (∑ i : Fin q, (Nat.choose (b i) 9 + 787644)) = (∑ i, Nat.choose (b i) 9) + q*787644 := by
    simp [Finset.sum_add_distrib, Finset.sum_const, Fintype.card_fin]
  rw [hleft, hright] at hsum
  omega
