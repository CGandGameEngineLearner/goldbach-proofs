import Mathlib.Data.Nat.BitIndices
import Mathlib.Algebra.BigOperators.Fin

private theorem split_pow_step :
    ∀ (L : List ℕ), L.length < (L.map (fun k => 2 ^ k)).sum →
      ∃ L' : List ℕ, L'.length = L.length + 1 ∧
        (L'.map (fun k => 2 ^ k)).sum = (L.map (fun k => 2 ^ k)).sum
  | [], h => by simp at h
  | 0 :: tl, h => by
    have htl : tl.length < (tl.map (fun k => 2 ^ k)).sum := by
      simp only [List.length_cons, List.map_cons, pow_zero, List.sum_cons] at h
      omega
    obtain ⟨tl', hlen, hsum⟩ := split_pow_step tl htl
    refine ⟨0 :: tl', ?_, ?_⟩
    · simp [hlen]
    · simp [hsum]
  | (k + 1) :: tl, _ => by
    refine ⟨k :: k :: tl, by simp, ?_⟩
    simp only [List.map_cons, List.sum_cons, pow_succ]
    omega

private theorem expand_pow_list :
    ∀ (d : ℕ) (L : List ℕ), L.length + d ≤ (L.map (fun k => 2 ^ k)).sum →
      ∃ L' : List ℕ, L'.length = L.length + d ∧
        (L'.map (fun k => 2 ^ k)).sum = (L.map (fun k => 2 ^ k)).sum
  | 0, L, _ => ⟨L, by simp, rfl⟩
  | d + 1, L, h => by
    obtain ⟨L₁, hlen₁, hsum₁⟩ := expand_pow_list d L (by omega)
    have hlt : L₁.length < (L₁.map (fun k => 2 ^ k)).sum := by omega
    obtain ⟨L₂, hlen₂, hsum₂⟩ := split_pow_step L₁ hlt
    exact ⟨L₂, by omega, hsum₂.trans hsum₁⟩

private theorem sum_fin_two_pow_eq_list_sum :
    ∀ {n : ℕ} (L : List ℕ), L.length = n →
      (∑ i : Fin n, 2 ^ L.getD i.1 0) = (L.map (fun k => 2 ^ k)).sum
  | _, [], h => by cases h; simp
  | _, a :: tl, h => by
    cases h
    change (∑ i : Fin (tl.length + 1), 2 ^ (a :: tl).getD i.1 0) = _
    rw [Fin.sum_univ_succ]
    simpa [List.getD] using congrArg (2 ^ a + ·) (sum_fin_two_pow_eq_list_sum tl rfl)

theorem Conjectures.Cuts.Taska126dd796add6b9dea852d9a : (∀ (x1 : ℕ), (13 : ℕ) ≤ x1 → x1.bitIndices.length ≤ (13 : ℕ) → ∃ (x4 : Fin (13 : ℕ) → ℕ), (2 : ℕ) * x1 = ∑ x5 : Fin (13 : ℕ), (2 : ℕ) ^ (x4 x5 + (1 : ℕ))) := by
  intro x1 hge hlen
  have hsum : (x1.bitIndices.map (fun k => 2 ^ k)).sum = x1 :=
    Nat.sum_map_two_pow_bitIndices x1
  have hle : x1.bitIndices.length + (13 - x1.bitIndices.length) ≤
      (x1.bitIndices.map (fun k => 2 ^ k)).sum := by
    omega
  obtain ⟨L', hL'_len, hL'_sum⟩ := expand_pow_list (13 - x1.bitIndices.length) x1.bitIndices hle
  have hlen13 : L'.length = 13 := by omega
  refine ⟨fun i => L'.getD i.1 0, ?_⟩
  have hrew : (∑ i : Fin 13, 2 ^ (L'.getD i.1 0 + 1)) =
      2 * ∑ i : Fin 13, 2 ^ L'.getD i.1 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ, mul_comm]
  rw [hrew, sum_fin_two_pow_eq_list_sum L' hlen13, hL'_sum, hsum]
