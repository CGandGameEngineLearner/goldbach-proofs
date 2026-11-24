import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_heavy_buckets :
    ∀ (n:ℕ) (b:Fin n→ℕ), ((Finset.univ:Finset (Fin n)).filter (fun i => 3≤b i)).card≤∑ i,Nat.choose (b i) 3 := by
  intro n b
  -- 步骤 1:基数 = 筛出集合上的 ∑ 1
  have hcard : ((Finset.univ:Finset (Fin n)).filter (fun i => 3≤b i)).card
      = ∑ i ∈ (Finset.univ:Finset (Fin n)).filter (fun i => 3≤b i), (1:ℕ) := by
    first
      · exact Finset.card_eq_sum_ones _
      · simp [Finset.sum_const, smul_eq_mul, mul_one]
  -- 步骤 2:筛出的 i 有 3 ≤ b i,故 1 ≤ Nat.choose (b i) 3,逐点求和
  have h1 : ∑ i ∈ (Finset.univ:Finset (Fin n)).filter (fun i => 3≤b i), (1:ℕ)
      ≤ ∑ i ∈ (Finset.univ:Finset (Fin n)).filter (fun i => 3≤b i), Nat.choose (b i) 3 := by
    apply Finset.sum_le_sum
    intro i hi
    show (1:ℕ) ≤ Nat.choose (b i) 3
    have h3 : 3 ≤ b i := (Finset.mem_filter.mp hi).2
    first
      · exact Nat.choose_pos h3
      · have h33 : (1:ℕ) = Nat.choose 3 3 := by decide
        rw [h33]
        exact Nat.choose_le_choose h3
  -- 步骤 3:Finset.sum_le_sum_of_subset 把右端扩到 Finset.univ
  calc ((Finset.univ:Finset (Fin n)).filter (fun i => 3≤b i)).card
      = ∑ i ∈ (Finset.univ:Finset (Fin n)).filter (fun i => 3≤b i), (1:ℕ) := hcard
    _ ≤ ∑ i ∈ (Finset.univ:Finset (Fin n)).filter (fun i => 3≤b i), Nat.choose (b i) 3 := h1
    _ ≤ ∑ i, Nat.choose (b i) 3 :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
