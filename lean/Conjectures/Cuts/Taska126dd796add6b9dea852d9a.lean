import Mathlib

/-!
Cut lemma of the exceptions route (adapted from the fleet's own scratch route; Mathlib only).

Statement: if `m ≥ 13` has at most thirteen set bits, then `2m` is a sum of exactly thirteen
positive powers of two, repetitions allowed.  Dividing by two, this is: `m` is a sum of exactly
thirteen powers of two.

Proof.  `Nat.sum_map_two_pow_bitIndices` gives the binary expansion
`m = ∑ i ∈ m.bitIndices, 2 ^ i`, i.e. a sum of `k = m.bitIndices.length ≤ 13` powers of two.
Splitting one term `2 ^ e = 2 ^ (e-1) + 2 ^ (e-1)` (available as soon as some exponent is
positive) raises the number of terms by one without changing the sum.  The padding lemma
`pad` iterates this from `k` up to `13`: with `n` terms summing to `m` and `n + 1 ≤ m` some
exponent must be positive (otherwise the sum would be `n`), so the split applies.  Finally
`2 * m = ∑ 2 * 2 ^ e = ∑ 2 ^ (e + 1)`.
-/

namespace Conjectures.Cuts.Taska126dd796add6b9dea852d9a_aux

/-- The binary expansion of `m` as a sum of `m.bitIndices.length` powers of two. -/
private lemma decompose (m : ℕ) :
    m = ∑ i : Fin m.bitIndices.length, 2 ^ m.bitIndices[(i : ℕ)] := by
  have h1 : (m.bitIndices.map (fun i => 2 ^ i)).sum = m := Nat.sum_map_two_pow_bitIndices m
  have h2 : (List.ofFn (fun i : Fin m.bitIndices.length => 2 ^ m.bitIndices[(i : ℕ)])).sum =
      (m.bitIndices.map (fun i => 2 ^ i)).sum := by
    rw [List.ofFn_getElem_eq_map]
  have h3 : (List.ofFn (fun i : Fin m.bitIndices.length => 2 ^ m.bitIndices[(i : ℕ)])).sum =
      ∑ i : Fin m.bitIndices.length, 2 ^ m.bitIndices[(i : ℕ)] := Fin.sum_ofFn _
  rw [← h3, h2, h1]

/-- If `k` powers of two sum to `m > k`, one of the exponents is positive. -/
private lemma exists_pos_exp {k : ℕ} {f : Fin k → ℕ} {m : ℕ}
    (hsum : m = ∑ i : Fin k, 2 ^ (f i)) (hlt : k < m) : ∃ i : Fin k, 1 ≤ f i := by
  by_contra h
  have h0 : ∀ i : Fin k, f i = 0 := fun i => by
    have hi : f i < 1 := Nat.lt_of_not_ge (fun hge => h ⟨i, hge⟩)
    omega
  have hk : (∑ i : Fin k, 2 ^ (f i)) = k := by
    simp [h0]
  omega

/-- Splitting one term of exponent `≥ 1` turns `k` terms into `k + 1` terms with the same sum. -/
private lemma split {k : ℕ} (f : Fin k → ℕ) (i : Fin k) (hi : 1 ≤ f i) :
    ∃ g : Fin (k + 1) → ℕ, ∑ j : Fin (k + 1), 2 ^ (g j) = ∑ j : Fin k, 2 ^ (f j) := by
  set h : Fin k → ℕ := fun j => if j = i then f i - 1 else f j
  refine ⟨Fin.cases (f i - 1) h, ?_⟩
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  have hsplit : (∑ j : Fin k, 2 ^ (h j)) = 2 ^ (f i - 1) + ∑ j ∈ Finset.univ.erase i, 2 ^ (f j) := by
    have key : (∑ j ∈ (Finset.univ : Finset (Fin k)), 2 ^ (h j)) =
        2 ^ (h i) + ∑ j ∈ Finset.univ.erase i, 2 ^ (h j) :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    rw [key]
    have hhi : h i = f i - 1 := by simp [h]
    have herase : ∑ j ∈ Finset.univ.erase i, 2 ^ (h j) = ∑ j ∈ Finset.univ.erase i, 2 ^ (f j) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hne : j ≠ i := Finset.ne_of_mem_erase hj
      simp [h, hne]
    rw [hhi, herase]
  rw [hsplit]
  have hpow : 2 ^ (f i - 1) + 2 ^ (f i - 1) = 2 ^ (f i) := by
    have hfi : f i - 1 + 1 = f i := Nat.sub_add_cancel hi
    calc 2 ^ (f i - 1) + 2 ^ (f i - 1) = 2 ^ (f i - 1) * 2 := by omega
      _ = 2 ^ (f i - 1 + 1) := (pow_succ 2 (f i - 1)).symm
      _ = 2 ^ (f i) := by rw [hfi]
  have herase2 : 2 ^ (f i) + ∑ j ∈ Finset.univ.erase i, 2 ^ (f j) = ∑ j : Fin k, 2 ^ (f j) :=
    Finset.add_sum_erase (Finset.univ : Finset (Fin k)) (fun j => 2 ^ (f j)) (Finset.mem_univ i)
  calc 2 ^ (f i - 1) + (2 ^ (f i - 1) + ∑ j ∈ Finset.univ.erase i, 2 ^ (f j))
      = 2 ^ (f i) + ∑ j ∈ Finset.univ.erase i, 2 ^ (f j) := by rw [← hpow]; omega
    _ = ∑ j : Fin k, 2 ^ (f j) := herase2

/-- Padding: `k ≤ n ≤ m` terms can be replaced by exactly `n` terms with the same sum. -/
private lemma pad : ∀ (n k : ℕ) (f : Fin k → ℕ) (m : ℕ),
    k ≤ n → n ≤ m → m = ∑ i : Fin k, 2 ^ (f i) → ∃ g : Fin n → ℕ, m = ∑ i : Fin n, 2 ^ (g i) := by
  intro n
  induction n with
  | zero =>
    intro k f m hk hnm hsum
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨f, hsum⟩
  | succ n ih =>
    intro k f m hk hnm hsum
    by_cases h : k = n + 1
    · subst h
      exact ⟨f, hsum⟩
    · have hkn : k ≤ n := by omega
      obtain ⟨g, hg⟩ := ih k f m hkn (by omega) hsum
      obtain ⟨i, hi⟩ := exists_pos_exp hg (by omega)
      obtain ⟨g', hg'⟩ := split g i hi
      exact ⟨g', by rw [hg', hg]⟩

end Conjectures.Cuts.Taska126dd796add6b9dea852d9a_aux

theorem Conjectures.Cuts.Taska126dd796add6b9dea852d9a :
    ∀ (x1 : ℕ), (13 : ℕ) ≤ x1 → x1.bitIndices.length ≤ (13 : ℕ) → ∃ (x4 : Fin (13 : ℕ) → ℕ), (2 : ℕ) * x1 = ∑ x5 : Fin (13 : ℕ), (2 : ℕ) ^ (x4 x5 + (1 : ℕ)) := by
  intro x1 h13 hpop
  have hd := Conjectures.Cuts.Taska126dd796add6b9dea852d9a_aux.decompose x1
  obtain ⟨g, hg⟩ := Conjectures.Cuts.Taska126dd796add6b9dea852d9a_aux.pad 13 x1.bitIndices.length
    (fun i => x1.bitIndices[(i : ℕ)]) x1 hpop h13 hd
  refine ⟨g, ?_⟩
  calc (2 : ℕ) * x1 = 2 * ∑ i : Fin 13, 2 ^ (g i) := by rw [← hg]
    _ = ∑ i : Fin 13, 2 * 2 ^ (g i) := by rw [Finset.mul_sum]
    _ = ∑ i : Fin 13, 2 ^ (g i + 1) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [pow_succ]; ring
