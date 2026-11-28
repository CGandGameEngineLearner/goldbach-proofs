import Mathlib

theorem Conjectures.Cuts.Task4f94483b395cb9bff7594f6e : (by
  classical
  exact ∀ (X Y : ℕ) (R : Finset ℕ) (P : ℕ → Bool), R ⊆ Finset.range 42 →
    ((Finset.Icc X Y).filter (fun n => n % 42 ∈ R ∧ P n)).card =
    ∑ r ∈ R, ((Finset.range (Y/42+1)).filter (fun k => X ≤ 42*k+r ∧ 42*k+r ≤ Y ∧ P (42*k+r))).card) := by
  classical
  intro X Y R P hr
  let U := (Finset.Icc X Y).filter (fun n => n % 42 ∈ R ∧ P n)
  have hmap : (U : Set ℕ).MapsTo (fun n => n % 42) R := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2.1
  change U.card = _
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro r hrR
  have hlt := Finset.mem_range.mp (hr hrR)
  let V := (Finset.range (Y/42+1)).filter (fun k => X≤42*k+r ∧ 42*k+r≤Y ∧ P (42*k+r))
  have im : V.image (fun k => 42*k+r) = U.filter (fun n=>n % 42=r) := by
    ext n
    constructor
    · intro hn
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨_,hl,hu,hp⟩ := Finset.mem_filter.mp hk
      have heq : (42*k+r) % 42=r := by omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hl,hu⟩,heq.symm ▸ hrR,hp⟩,heq⟩
    · intro hn
      obtain ⟨hnU,heq⟩ := Finset.mem_filter.mp hn
      obtain ⟨hwin,_,hp⟩ := Finset.mem_filter.mp hnU
      obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hwin
      have he : 42*(n/42)+r=n := by omega
      exact Finset.mem_image.mpr ⟨n/42,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),he.symm ▸ hl,he.symm ▸ hu,he.symm ▸ hp⟩,he⟩
  rw [← im]
  exact Finset.card_image_of_injective _ (by intro i j hij; dsimp at hij; omega)
