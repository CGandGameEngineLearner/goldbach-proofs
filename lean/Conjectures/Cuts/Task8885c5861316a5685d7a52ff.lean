import Mathlib

open Finset

theorem Conjectures.Cuts.Task8885c5861316a5685d7a52ff :
    have x1 : ℕ → ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range (x1 + (1 : ℕ)) | Nat.Prime x2 ∧ Nat.Prime (x1 - x2)}.card; ∀ (x2 : ℕ),   (16 : ℕ) ≤ x2 →     have x4 : ℕ := Nat.log (2 : ℕ) x2 / (2 : ℕ);     have x5 : Finset ℕ := {x5 ∈ Finset.Ico x2 ((2 : ℕ) * x2) | Even x5 ∧ (0 : ℕ) < {x6 ∈ Finset.Icc (1 : ℕ) x4 | x1 (x5 - (2 : ℕ) ^ x6) = (0 : ℕ)}.card};     x5.card ≤ x4 * {x6 ∈ Finset.Icc (4 : ℕ) ((2 : ℕ) * x2) | Even x6 ∧ x1 x6 = (0 : ℕ)}.card := by
  intro G X hX L E
  let Bad := (Icc 4 (2 * X)).filter (fun m => Even m ∧ G m = 0)
  let S := Icc 1 L
  let Shift := fun e : ℕ => Bad.image (fun m => m + 2 ^ e)
  have hlog : 4 ≤ Nat.log 2 X :=
    Nat.le_log_of_pow_le (by decide) (show 2 ^ 4 ≤ X from hX)
  have hXpos : X ≠ 0 := by omega
  have hCover : E ⊆ S.biUnion Shift := by
    intro n hn
    obtain ⟨hnWindow, hnEven, hFailure⟩ := mem_filter.mp hn
    obtain ⟨hnLower, hnUpper⟩ := mem_Ico.mp hnWindow
    obtain ⟨e, he⟩ := card_pos.mp hFailure
    obtain ⟨heS, heBad⟩ := mem_filter.mp he
    obtain ⟨heLower, heUpper⟩ := mem_Icc.mp heS
    have heLog : e + 1 ≤ Nat.log 2 X := by
      change e ≤ Nat.log 2 X / 2 at heUpper
      omega
    have hPower : 2 ^ e * 2 ≤ X := calc
      _ = 2 ^ (e + 1) := (pow_succ 2 e).symm
      _ ≤ 2 ^ Nat.log 2 X := Nat.pow_le_pow_right (by decide) heLog
      _ ≤ X := Nat.pow_log_le_self 2 hXpos
    have heEven : Even (2 ^ e) := (Nat.even_pow' (by omega : e ≠ 0)).mpr (by decide)
    have hmEven : Even (n - 2 ^ e) := by
      obtain ⟨a, ha⟩ := hnEven
      obtain ⟨b, hb⟩ := heEven
      exact ⟨a - b, by omega⟩
    have hmLower : 4 ≤ n - 2 ^ e := by omega
    have hmUpper : n - 2 ^ e ≤ 2 * X := by omega
    have hm : n - 2 ^ e ∈ Bad := mem_filter.mpr
      ⟨mem_Icc.mpr ⟨hmLower, hmUpper⟩, hmEven, heBad⟩
    exact mem_biUnion.mpr ⟨e, heS, mem_image.mpr ⟨n - 2 ^ e, hm, Nat.sub_add_cancel (by omega)⟩⟩
  calc
    E.card ≤ (S.biUnion Shift).card := card_le_card hCover
    _ ≤ ∑ e ∈ S, (Shift e).card := card_biUnion_le
    _ ≤ ∑ _e ∈ S, Bad.card := sum_le_sum (fun _ _ => card_image_le)
    _ = S.card * Bad.card := by rw [sum_const, smul_eq_mul]
    _ = L * Bad.card := by simp [S, Nat.card_Icc]
