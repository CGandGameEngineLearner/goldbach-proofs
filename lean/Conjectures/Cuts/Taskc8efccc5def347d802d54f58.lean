import Mathlib

theorem Conjectures.Cuts.Taskc8efccc5def347d802d54f58 : (∀ (x1 x2 : ℕ) (x3 : Finset ℕ), (0 : ℕ) < x2 → x3 ⊆ Finset.range (x1 + (1 : ℕ)) → {x6 ∈ x3 | x2 ∣ x6 + (2 : ℕ)}.card = {x6 ∈ Finset.range ((x1 + (2 : ℕ)) / x2 + (1 : ℕ)) | (2 : ℕ) ≤ x2 * x6 ∧ x2 * x6 - (2 : ℕ) ∈ x3}.card) := by
  intro N d S hd hS
  have recover (n : ℕ) (h : d ∣ n + 2) : d * ((n + 2) / d) = n + 2 := by
    rw [Nat.mul_comm, Nat.div_mul_cancel h]
  refine Finset.card_bij' (fun n _ => (n + 2) / d) (fun k _ => d * k - 2) ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hnS, hdiv⟩ := Finset.mem_filter.mp hn
    have hnN := Finset.mem_range.mp (hS hnS)
    have hquot : (n + 2) / d ≤ (N + 2) / d := Nat.div_le_div_right (by omega)
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_, ?_⟩
    · rw [recover n hdiv]
      omega
    · simpa only [recover n hdiv, Nat.add_sub_cancel] using hnS
  · intro k hk
    obtain ⟨_, hlow, hmem⟩ := Finset.mem_filter.mp hk
    refine Finset.mem_filter.mpr ⟨hmem, ⟨k, ?_⟩⟩
    exact Nat.sub_add_cancel hlow
  · intro n hn
    change d * ((n + 2) / d) - 2 = n
    rw [recover n (Finset.mem_filter.mp hn).2, Nat.add_sub_cancel]
  · intro k hk
    change (d * k - 2 + 2) / d = k
    rw [Nat.sub_add_cancel (Finset.mem_filter.mp hk).2.1, Nat.mul_comm d k,
      Nat.mul_div_cancel _ hd]
