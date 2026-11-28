import Mathlib

open scoped BigOperators

-- child 1 zh: 已有 Goldbach 素数对但没有 X^(1/24)-粗糙素数对的 6 的倍数，例外预算为 X/4 除以任意固定对数幂。
-- child 1 en: Multiples of six with a Goldbach pair but no X^(1/24)-rough shifted product have budget X/4 divided by any fixed log power.
-- child 2 zh: 粗糙素数对的总对数惩罚超过每对 (3/2)log X 时，端点数服从同一个 X/4 对数节省预算。
-- child 2 en: Endpoints where the total log penalty of the rough pairs exceeds (3/2)log X per pair satisfy the same X/4 log-saving budget.
theorem Conjectures.Cuts.Cut77d5dcf781b3b62a523a97bf
    (hRough : ∀ A : ℕ, ∃ N : ℕ, ∀ X ≥ N,
      let P := fun n : ℕ => (Finset.range (n + 1)).filter (fun p => p.Prime ∧ (n - p).Prime)
      let Q := fun n p : ℕ => 2 * p * (n - p) + 1
      let R := fun n : ℕ => (P n).filter (fun p =>
        (Q n p).primeFactorsList.all (fun r : ℕ => decide (X ≤ r^24)) = true)
      (((Finset.Ioc (X / 2) X).filter (fun n => 6 ∣ n ∧ 0 < (P n).card ∧ (R n).card = 0)).card : ℝ) *
        Real.log (X : ℝ)^A ≤ (X : ℝ) / 4)
    (hPenalty : ∀ A : ℕ, ∃ N : ℕ, ∀ X ≥ N,
      let P := fun n : ℕ => (Finset.range (n + 1)).filter (fun p => p.Prime ∧ (n - p).Prime)
      let Q := fun n p : ℕ => 2 * p * (n - p) + 1
      let R := fun n : ℕ => (P n).filter (fun p =>
        (Q n p).primeFactorsList.all (fun r : ℕ => decide (X ≤ r^24)) = true)
      let W := fun m : ℕ => (m.primeFactorsList.map (fun r : ℕ =>
        max 0 (Real.log (X : ℝ) - 3 * Real.log (r : ℝ)))).sum
      (((Finset.Ioc (X / 2) X).filter (fun n => 6 ∣ n ∧
        3 * ((R n).card : ℝ) * Real.log (X : ℝ) / 2 < ∑ p ∈ R n, W (Q n p))).card : ℝ) *
          Real.log (X : ℝ)^A ≤ (X : ℝ) / 4) :
    (∀ (x1 : ℕ), ∃ (x2 : ℕ), ∀ (x3 : ℕ), x2 ≤ x3 → ↑{x5 ∈ Finset.Ioc (x3 / (2 : ℕ)) x3 | (6 : ℕ) ∣ x5 ∧ (0 : ℕ) < {x6 ∈ Finset.range (x5 + (1 : ℕ)) | Nat.Prime x6 ∧ Nat.Prime (x5 - x6)}.card ∧ {x6 ∈ Finset.range (x5 + (1 : ℕ)) | Nat.Prime x6 ∧ Nat.Prime (x5 - x6) ∧ ((2 : ℕ) * x6 * (x5 - x6) + (1 : ℕ)).primeFactorsList.length ≤ (7 : ℕ)}.card = (0 : ℕ)}.card * Real.log ↑x3 ^ x1 ≤ ↑x3 / (2 : ℝ)) := by
  intro A
  obtain ⟨N₁, h₁⟩ := hRough A
  obtain ⟨N₂, h₂⟩ := hPenalty A
  refine ⟨max 2 (max N₁ N₂), ?_⟩
  intro X hX
  have hTwo : 2 ≤ X := (le_max_left _ _).trans hX
  have hLarge : max N₁ N₂ ≤ X := (le_max_right _ _).trans hX
  have hLogX : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  let P := fun n : ℕ => (Finset.range (n + 1)).filter (fun p => p.Prime ∧ (n - p).Prime)
  let Q := fun n p : ℕ => 2 * p * (n - p) + 1
  let R := fun n : ℕ => (P n).filter (fun p =>
    (Q n p).primeFactorsList.all (fun r : ℕ => decide (X ≤ r^24)) = true)
  let W := fun m : ℕ => (m.primeFactorsList.map (fun r : ℕ =>
    max 0 (Real.log (X : ℝ) - 3 * Real.log (r : ℝ)))).sum

  -- Counting repeated factors makes their logarithms sum to log m exactly.
  have hWeight (m : ℕ) (hm : 0 < m) (hmX : m ≤ X^2) (hΩ : 8 ≤ m.primeFactorsList.length) :
      2 * Real.log (X : ℝ) ≤ W m := by
    have hLower (L : List ℕ) : (L.length : ℝ) * Real.log (X : ℝ) -
        3 * (L.map (fun r : ℕ => Real.log (r : ℝ))).sum ≤
        (L.map (fun r : ℕ => max 0 (Real.log (X : ℝ) - 3 * Real.log (r : ℝ)))).sum := by
      induction L with
      | nil => simp
      | cons p L ih =>
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons, List.sum_cons]
        linarith only [ih, le_max_right (0 : ℝ) (Real.log (X : ℝ) - 3 * Real.log (p : ℝ))]
    have hNe (x : ℝ) (hx : x ∈ m.primeFactorsList.map (fun r : ℕ => (r : ℝ))) : x ≠ 0 := by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
      exact_mod_cast (Nat.prime_of_mem_primeFactorsList hr).ne_zero
    have hProduct : (m.primeFactorsList.map (fun r : ℕ => Real.log (r : ℝ))).sum = Real.log (m : ℝ) := by
      simpa only [← Nat.cast_list_prod, Nat.prod_primeFactorsList hm.ne', List.map_map,
        Function.comp_def] using (Real.log_list_prod hNe).symm
    have hLogM : Real.log (m : ℝ) ≤ 2 * Real.log (X : ℝ) := by
      simpa [Real.log_pow] using Real.log_le_log (show (0 : ℝ) < (m : ℝ) by exact_mod_cast hm)
        (show (m : ℝ) ≤ (X : ℝ)^2 by exact_mod_cast hmX)
    have hCount := mul_le_mul_of_nonneg_right
      (show (8 : ℝ) ≤ (m.primeFactorsList.length : ℝ) by exact_mod_cast hΩ) hLogX.le
    have hCharged := hLower m.primeFactorsList
    rw [hProduct] at hCharged
    dsimp only [W]
    linarith only [hCharged, hLogM, hCount]

  let I := Finset.Ioc (X / 2) X
  let G := fun n : ℕ => (Finset.range (n + 1)).filter (fun p =>
    p.Prime ∧ (n - p).Prime ∧ (Q n p).primeFactorsList.length ≤ 7)
  let B := I.filter (fun n => 6 ∣ n ∧ 0 < (P n).card ∧ (G n).card = 0)
  let M := I.filter (fun n => 6 ∣ n ∧ 0 < (P n).card ∧ (R n).card = 0)
  let H := I.filter (fun n => 6 ∣ n ∧
    3 * ((R n).card : ℝ) * Real.log (X : ℝ) / 2 < ∑ p ∈ R n, W (Q n p))
  have hSubset : B ⊆ M ∪ H := by
    intro n hn
    obtain ⟨hnI, hnSix, hnPrime, hnBad⟩ := Finset.mem_filter.mp hn
    by_cases hEmpty : (R n).card = 0
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hnI, hnSix, hnPrime, hEmpty⟩))
    have hEach (p : ℕ) (hp : p ∈ R n) : 2 * Real.log (X : ℝ) ≤ W (Q n p) := by
      have hpP : p ∈ P n := (Finset.mem_filter.mp hp).1
      obtain ⟨hpRange, hpPrime, hqPrime⟩ := Finset.mem_filter.mp hpP
      have hpLe : p ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hpRange)
      have hSum : p + (n - p) = n := by omega
      have hNL : n ≤ X := (Finset.mem_Ioc.mp hnI).2
      have hBound : Q n p ≤ X^2 := by
        have hSquare := Nat.mul_le_mul hpPrime.two_le hpPrime.two_le
        calc
          Q n p ≤ 2 * p * (n - p) + (p * p + (n - p) * (n - p)) := by
            dsimp only [Q]
            omega
          _ = (p + (n - p))^2 := by ring
          _ ≤ X^2 := by rw [hSum]; exact Nat.pow_le_pow_left hNL 2
      apply hWeight _ (by dsimp only [Q]; omega) hBound
      by_contra! hSmall
      have hMem : p ∈ G n := Finset.mem_filter.mpr ⟨hpRange, hpPrime, hqPrime, by omega⟩
      simp [Finset.card_eq_zero.mp hnBad] at hMem
    have hSums : ((R n).card : ℝ) * (2 * Real.log (X : ℝ)) ≤ ∑ p ∈ R n, W (Q n p) := by
      calc
        _ = ∑ _p ∈ R n, 2 * Real.log (X : ℝ) := by simp
        _ ≤ _ := Finset.sum_le_sum hEach
    have hPos : 0 < ((R n).card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hEmpty)
    refine Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hnI, hnSix, ?_⟩))
    linarith only [hSums, mul_pos hPos hLogX]
  have hCard : (B.card : ℝ) ≤ (M.card : ℝ) + (H.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hSubset).trans (Finset.card_union_le M H)
  have hTotal := mul_le_mul_of_nonneg_right hCard (pow_nonneg hLogX.le A)
  rw [add_mul] at hTotal
  have hMass : (M.card : ℝ) * Real.log (X : ℝ)^A ≤ (X : ℝ) / 4 :=
    h₁ X ((le_max_left _ _).trans hLarge)
  have hPen : (H.card : ℝ) * Real.log (X : ℝ)^A ≤ (X : ℝ) / 4 :=
    h₂ X ((le_max_right _ _).trans hLarge)
  change (B.card : ℝ) * Real.log (X : ℝ)^A ≤ (X : ℝ) / 2
  linarith only [hTotal, hMass, hPen]
