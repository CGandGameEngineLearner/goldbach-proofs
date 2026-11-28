import Mathlib

theorem Conjectures.Cuts.Taskdc6324ac04f6b983d18396d1 : (∀ (x1 : ℕ), {x2 ∈ Finset.range (x1 + (1 : ℕ)) | IsPrimePow x2 ∧ ¬Nat.Prime x2}.card ≤ (x1.sqrt + (1 : ℕ)) * (Nat.log (2 : ℕ) x1 + (1 : ℕ))) := by
  intro N
  classical
  let box := (Finset.range (Nat.sqrt N + 1)) ×ˢ (Finset.range (Nat.log 2 N + 1))
  have cover : ((Finset.range (N+1)).filter (fun m => IsPrimePow m ∧ ¬ Nat.Prime m)) ⊆
      box.image (fun pe : ℕ × ℕ => pe.1 ^ pe.2) := by
    intro m hm
    obtain ⟨hR, hpow, hcomp⟩ := Finset.mem_filter.mp hm
    have hmN : m ≤ N := by simpa using Finset.mem_range.mp hR
    obtain ⟨e, helog, hepos, p, _, heq, hp⟩ := (isPrimePow_nat_iff_bounded_log m).mp hpow
    have hne : e ≠ 1 := by
      rintro rfl
      exact hcomp (by simpa [heq] using hp)
    have he : 2 ≤ e := by omega
    have hbase : p ≤ N.sqrt := Nat.le_sqrt'.mpr (calc
      p^2 ≤ p^e := Nat.pow_le_pow_right hp.one_lt.le he
      _ = m := heq.symm
      _ ≤ N := hmN)
    have hexp : e ≤ Nat.log 2 N := helog.trans (Nat.log_mono_right hmN)
    exact Finset.mem_image.mpr ⟨(p,e), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, heq.symm⟩
  calc
    _ ≤ (box.image (fun pe : ℕ × ℕ => pe.1 ^ pe.2)).card := Finset.card_le_card cover
    _ ≤ box.card := Finset.card_image_le
    _ = _ := by simp [box]
