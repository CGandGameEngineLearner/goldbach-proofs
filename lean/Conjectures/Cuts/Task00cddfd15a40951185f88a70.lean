import Mathlib

theorem Conjectures.Cuts.Task00cddfd15a40951185f88a70 : (∀ (x1 : Finset (ℕ × ℕ)), ∃ x2 ⊆ x1, {x3 ∈ (x2 ×ˢ x2) ×ˢ x2 | (x3.1.1.1 < x3.1.2.1 ∨ x3.1.1.1 = x3.1.2.1 ∧ x3.1.1.2 < x3.1.2.2) ∧ (x3.1.2.1 < x3.2.1 ∨ x3.1.2.1 = x3.2.1 ∧ x3.1.2.2 < x3.2.2) ∧ ((↑x3.1.2.1 : ℤ) - (↑x3.1.1.1 : ℤ)) * ((↑x3.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) = ((↑x3.1.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) * ((↑x3.2.1 : ℤ) - (↑x3.1.1.1 : ℤ))} = ∅ ∧ x1.card ≤ x2.card + {x3 ∈ (x1 ×ˢ x1) ×ˢ x1 | (x3.1.1.1 < x3.1.2.1 ∨ x3.1.1.1 = x3.1.2.1 ∧ x3.1.1.2 < x3.1.2.2) ∧ (x3.1.2.1 < x3.2.1 ∨ x3.1.2.1 = x3.2.1 ∧ x3.1.2.2 < x3.2.2) ∧ ((↑x3.1.2.1 : ℤ) - (↑x3.1.1.1 : ℤ)) * ((↑x3.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) = ((↑x3.1.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) * ((↑x3.2.1 : ℤ) - (↑x3.1.1.1 : ℤ))}.card) := by
  -- 定义有限格点集上的严格字典序共线三元组集合
  let col (T : Finset (ℕ × ℕ)) :=
    {x3 ∈ (T ×ˢ T) ×ˢ T |
      (x3.1.1.1 < x3.1.2.1 ∨ x3.1.1.1 = x3.1.2.1 ∧ x3.1.1.2 < x3.1.2.2) ∧
      (x3.1.2.1 < x3.2.1 ∨ x3.1.2.1 = x3.2.1 ∧ x3.1.2.2 < x3.2.2) ∧
      ((↑x3.1.2.1 : ℤ) - (↑x3.1.1.1 : ℤ)) * ((↑x3.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) =
        ((↑x3.1.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) * ((↑x3.2.1 : ℤ) - (↑x3.1.1.1 : ℤ))}
  intro T0
  -- 对有限集 T 做强归纳（Finset.strongInduction）
  refine Finset.strongInduction (p := fun T => ∃ S ⊆ T, col S = ∅ ∧ T.card ≤ S.card + (col T).card) ?_ T0
  intro T ih
  by_cases hEmpty : col T = ∅
  · -- 若 T 本身不含共线三元组，直接取 S = T
    exact ⟨T, Finset.Subset.refl T, hEmpty, by omega⟩
  · -- 否则取出任意一个共线三元组 p = ((a, b), c) ∈ col T，并从 T 中删去点 a
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
    have hpMem : p ∈ (T ×ˢ T) ×ˢ T := (Finset.mem_filter.mp hp).1
    have ha : p.1.1 ∈ T := (Finset.mem_product.mp (Finset.mem_product.mp hpMem).1).1
    let T' := T.erase p.1.1
    have hT'sub : T' ⊆ T := Finset.erase_subset p.1.1 T
    have hT'ssub : T' ⊂ T := Finset.erase_ssubset ha
    -- 对严格子集 T' 应用强归纳假设
    obtain ⟨S, hST', hSempty, hScard⟩ := ih T' hT'ssub
    -- 证明 col T' 是 col T 的严格子集（至少少了三元组 p）
    have hColSub : col T' ⊆ col T := by
      intro q hq
      rw [Finset.mem_filter] at hq ⊢
      refine ⟨?_, hq.2⟩
      rcases Finset.mem_product.mp hq.1 with ⟨hq12, hq3⟩
      rcases Finset.mem_product.mp hq12 with ⟨hq1, hq2⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hT'sub hq1, hT'sub hq2⟩, hT'sub hq3⟩
    have hpNotMem : p ∉ col T' := by
      intro hp'
      have hp'Mem : p ∈ (T' ×ˢ T') ×ˢ T' := (Finset.mem_filter.mp hp').1
      have ha' : p.1.1 ∈ T' := (Finset.mem_product.mp (Finset.mem_product.mp hp'Mem).1).1
      exact Finset.notMem_erase p.1.1 T ha'
    have hColSSub : col T' ⊂ col T :=
      Finset.ssubset_iff_of_subset hColSub |>.mpr ⟨p, hp, hpNotMem⟩
    have hColLt : (col T').card < (col T).card := Finset.card_lt_card hColSSub
    have hCardErase : T'.card + 1 = T.card := Finset.card_erase_add_one ha
    exact ⟨S, hST'.trans hT'sub, hSempty, by omega⟩
