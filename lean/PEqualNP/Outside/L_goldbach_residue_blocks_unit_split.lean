import Mathlib

theorem PEqualNP.Outside.L_goldbach_residue_blocks_unit_split :
    ∀ (q X : ℕ) (w : ℕ → ℂ), (∑ k ∈ Finset.range X,w k)=(∑ k ∈ (Finset.range X).filter (fun k => Nat.Coprime k q),w k)+(∑ k ∈ (Finset.range X).filter (fun k => ¬ Nat.Coprime k q),w k) := by
  intro q X w
  -- 经典 filter 分拆恒等式：∑ s = ∑ (s.filter p) + ∑ (s.filter ¬p)。
  -- Mathlib 中该引理名随版本略有差异，按可能性依次尝试（任一成立即闭目标）；
  -- 全部失败则退回手证：sum_union + filter_union_filter_neg_eq。
  first
  | rw [Finset.sum_filter_add_filter_neg_sum]
  | rw [Finset.sum_filter_add_filter_neg_eq]
  | rw [Finset.sum_filter_add_sum_filter_neg]
  | rw [Finset.sum_filter_add_sum_filter_neg_eq]
  |
    have hd : Disjoint ((Finset.range X).filter (fun k => Nat.Coprime k q))
        ((Finset.range X).filter (fun k => ¬ Nat.Coprime k q)) :=
      Finset.disjoint_right.mpr fun a ha h'a =>
        (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp h'a).2
    rw [← Finset.sum_union hd, Finset.filter_union_filter_neg_eq]
