import Mathlib
import Conjectures.Goldbach.EstermannAlmostAllPolylog

theorem Conjectures.Cuts.Task8885c5861316a5685d7a52ff : (have x1 : ℕ → ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range (x1 + (1 : ℕ)) | Nat.Prime x2 ∧ Nat.Prime (x1 - x2)}.card; ∀ (x2 : ℕ),   (16 : ℕ) ≤ x2 →     have x4 : ℕ := Nat.log (2 : ℕ) x2 / (2 : ℕ);     have x5 : Finset ℕ := {x5 ∈ Finset.Ico x2 ((2 : ℕ) * x2) | Even x5 ∧ (0 : ℕ) < {x6 ∈ Finset.Icc (1 : ℕ) x4 | x1 (x5 - (2 : ℕ) ^ x6) = (0 : ℕ)}.card};     x5.card ≤ x4 * {x6 ∈ Finset.Icc (4 : ℕ) ((2 : ℕ) * x2) | Even x6 ∧ x1 x6 = (0 : ℕ)}.card) := by
  intro rf X hX
  dsimp only
  set L : ℕ := Nat.log 2 X / 2 with hL
  set S : Finset ℕ := (Finset.Ico X (2 * X)).filter
    (fun n => Even n ∧ 0 < ((Finset.Icc 1 L).filter (fun j => rf (n - 2 ^ j) = 0)).card) with hS
  set E : Finset ℕ := (Finset.Icc 4 (2 * X)).filter (fun m => Even m ∧ rf m = 0) with hE
  have hpow : 2 ^ Nat.log 2 X ≤ X := Nat.pow_log_le_self 2 (by omega)
  have hlog4 : 4 ≤ Nat.log 2 X := by
    have h16 : 2 ^ 4 ≤ X := by norm_num; omega
    exact Nat.le_log_of_pow_le (by norm_num) h16
  have hL1 : L + 1 ≤ Nat.log 2 X := by omega
  have h2L : 2 * 2 ^ L ≤ X := by
    have h : 2 ^ (L + 1) ≤ 2 ^ Nat.log 2 X := Nat.pow_le_pow_right (by norm_num) hL1
    have h' : 2 ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ]; ring
    rw [h'] at h
    exact le_trans h hpow
  have hT : ∀ j ∈ Finset.Icc 1 L,
      ((Finset.Ico X (2 * X)).filter (fun n => Even n ∧ rf (n - 2 ^ j) = 0)).card ≤ E.card := by
    intro j hj
    obtain ⟨hj1, hjL⟩ := Finset.mem_Icc.mp hj
    have h2j : 2 ^ j ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hjL
    have h2jX : 2 * 2 ^ j ≤ X := by nlinarith
    set D : ℕ := 2 ^ j with hD
    have hDX : 2 * D ≤ X := by rw [hD]; exact h2jX
    have h2D : 2 ∣ D := by
      rw [hD]
      refine ⟨2 ^ (j - 1), ?_⟩
      rw [← pow_succ']
      congr 1
      omega
    refine Finset.card_le_card_of_injOn (fun n => n - D) ?_ ?_
    · intro a ha
      obtain ⟨haI, haEven, har⟩ := Finset.mem_filter.mp ha
      obtain ⟨haX, haU⟩ := Finset.mem_Ico.mp haI
      have hlow : 4 ≤ a - D := by omega
      have hup : a - D ≤ 2 * X := by omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlow, hup⟩, ?_, har⟩
      have h2a : 2 ∣ a := even_iff_two_dvd.mp haEven
      have hdvd : 2 ∣ a - D := Nat.dvd_sub h2a h2D
      exact even_iff_two_dvd.mpr hdvd
    · intro a ha b hb hab
      obtain ⟨haI, -⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbI, -⟩ := Finset.mem_filter.mp hb
      have haX : X ≤ a := (Finset.mem_Ico.mp haI).1
      have hbX : X ≤ b := (Finset.mem_Ico.mp hbI).1
      simp only at hab
      omega
  have hsub : S ⊆ (Finset.Icc 1 L).biUnion
      (fun j => (Finset.Ico X (2 * X)).filter (fun n => Even n ∧ rf (n - 2 ^ j) = 0)) := by
    intro n hn
    obtain ⟨hnI, hnEven, hnpos⟩ := Finset.mem_filter.mp hn
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hnpos
    rw [Finset.mem_filter] at hj
    exact Finset.mem_biUnion.mpr ⟨j, hj.1, Finset.mem_filter.mpr ⟨hnI, hnEven, hj.2⟩⟩
  calc S.card ≤ ((Finset.Icc 1 L).biUnion
        (fun j => (Finset.Ico X (2 * X)).filter (fun n => Even n ∧ rf (n - 2 ^ j) = 0))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.Icc 1 L,
          ((Finset.Ico X (2 * X)).filter (fun n => Even n ∧ rf (n - 2 ^ j) = 0)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ j ∈ Finset.Icc 1 L, E.card := Finset.sum_le_sum hT
    _ = (Finset.Icc 1 L).card * E.card := by rw [Finset.sum_const, smul_eq_mul]
    _ = L * E.card := by
        rw [Nat.card_Icc]
        have hLeq : L + 1 - 1 = L := by omega
        rw [hLeq]
