import Mathlib

namespace GoldbachDyadicExceptions
open Finset

private def reps (n : ℕ) :=
  (range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))

private def block (x : ℕ) :=
  ((Ico x (2*x)).filter (fun n => 4 ≤ n ∧ Even n)).filter (fun n => (reps n).card = 0)

private def below (x : ℕ) :=
  (range x).filter (fun n => 4 ≤ n ∧ Even n ∧ (reps n).card = 0)

private theorem split (x : ℕ) : (below (2*x)).card ≤ (below x).card + (block x).card := by
  apply le_trans (card_le_card (t := below x ∪ block x) ?_) (card_union_le _ _)
  intro n hn
  obtain ⟨hnx, h4, he, hz⟩ := mem_filter.mp hn
  have hn2 := mem_range.mp hnx
  by_cases h : n < x
  · exact mem_union_left _ (mem_filter.mpr ⟨mem_range.mpr h, h4, he, hz⟩)
  · exact mem_union_right _ (mem_filter.mpr ⟨mem_filter.mpr
      ⟨mem_Ico.mpr ⟨Nat.le_of_not_gt h, hn2⟩, h4, he⟩, hz⟩)

theorem transfer (K N : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : ∀ n : ℕ, 4 ≤ n → n < 2^K → Even n → (reps n).Nonempty)
    (hblocks : ∀ j : ℕ, K ≤ j → ((block (2^j)).card : ℝ) ≤ ε * ((2^j : ℕ) : ℝ)) :
    ((below (N+1)).card : ℝ) ≤ 2 * ε * (N : ℝ) := by
  have empty_before (x : ℕ) (hx : x ≤ 2^K) : below x = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro n hn
    obtain ⟨hm,h4,he,hz⟩ := mem_filter.mp hn
    exact (card_pos.mpr (hsmall n h4 ((mem_range.mp hm).trans_le hx) he)).ne' hz
  have hbase : 1 ≤ (2 : ℕ)^K := Nat.one_le_pow _ _ (by decide)
  have hpow (j : ℕ) : ((below (2^j)).card : ℝ) ≤ ε * ((2^j : ℕ) : ℝ) := by
    induction j with
    | zero =>
      rw [empty_before _ (by simpa using hbase)]
      simpa using hε
    | succ j ih =>
      by_cases hj : j < K
      · rw [empty_before _ (Nat.pow_le_pow_right (by decide) hj)]
        simp only [card_empty, Nat.cast_zero]
        positivity
      · have hsum := add_le_add ih (hblocks j (Nat.le_of_not_gt hj))
        have hs : ((below (2*(2^j))).card : ℝ) ≤
            ((below (2^j)).card : ℝ) + ((block (2^j)).card : ℝ) := by
          exact_mod_cast split (2^j)
        rw [pow_succ, Nat.mul_comm (2^j) 2]
        calc
          _ ≤ _ := hs.trans hsum
          _ = _ := by push_cast; ring
  by_cases hN : N = 0
  · subst N
    rw [empty_before _ hbase]
    simp
  let j := Nat.log 2 N
  have hlo : 2^j ≤ N := Nat.pow_log_le_self 2 hN
  have hhi : N < 2^(j+1) := Nat.lt_pow_succ_log_self (by decide : 1<2) N
  have hsub : below (N+1) ⊆ below (2^(j+1)) := by
    intro n hn
    obtain ⟨hm, hb⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hm).trans_le hhi), hb⟩
  have hup : 2^(j+1) ≤ 2*N := by rw [pow_succ]; omega
  calc
    _ ≤ ((below (2^(j+1))).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ ≤ _ := hpow (j+1)
    _ ≤ ε * ((2*N : ℕ) : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hup) hε
    _ = _ := by push_cast; ring

end GoldbachDyadicExceptions

theorem Conjectures.Goldbach.DyadicExceptionDensityTransfer :
    let reps (n : ℕ) := (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))
    let D (X : ℕ) := (Finset.Ico X (2 * X)).filter (fun n => 4 ≤ n ∧ Even n)
    let bad (X : ℕ) := (D X).filter (fun n => (reps n).card = 0)
    let exc (N : ℕ) := (Finset.range (N + 1)).filter (fun n => 4 ≤ n ∧ Even n ∧ (reps n).card = 0)
    ∀ (K N : ℕ) (ε : ℝ), 0 ≤ ε →
      (∀ n : ℕ, 4 ≤ n → n < 2 ^ K → Even n → (reps n).Nonempty) →
      (∀ j : ℕ, K ≤ j → ((bad (2 ^ j)).card : ℝ) ≤ ε * ((2 ^ j : ℕ) : ℝ)) →
      ((exc N).card : ℝ) ≤ 2 * ε * (N : ℝ) :=
  GoldbachDyadicExceptions.transfer
