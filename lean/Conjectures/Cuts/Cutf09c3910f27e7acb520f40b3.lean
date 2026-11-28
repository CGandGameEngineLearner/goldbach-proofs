import Mathlib

-- child 1 zh: 对充分大的 N=2^k，中央窗口内两端都是素数幂的有序对数，在 cN/(log N)^2 之上还留有两端高次素数幂的误差预算。
-- child 1 en: For large N = 2^k, the central prime-power pair count exceeds cN/(log N)^2 by a budget for proper prime powers at both endpoints.
-- child 2 zh: 对每个自然数 N，不超过 N 的非素数的素数幂至多有 (⌊√N⌋+1)(⌊log₂ N⌋+1) 个。
-- child 2 en: Up to any N, there are at most (floor(sqrt N)+1)(floor(log₂ N)+1) distinct proper prime powers.

theorem Conjectures.Cuts.Cutf09c3910f27e7acb520f40b3
    (mass : ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∀ k ≥ K,
      let N := 2 ^ k
      let W := (Finset.range (N + 1)).filter (fun p => N ≤ 3*p ∧ 3*p ≤ 2*N)
      let pairs := W.filter (fun p => IsPrimePow p ∧ IsPrimePow (N-p))
      c * (N : ℝ) / (Real.log N)^2 +
          ((2 * ((Nat.sqrt N + 1) * (Nat.log 2 N + 1)) : ℕ) : ℝ) ≤ pairs.card)
    (proper : ∀ N : ℕ,
      ((Finset.range (N+1)).filter (fun m => IsPrimePow m ∧ ¬ Nat.Prime m)).card ≤
        (Nat.sqrt N + 1) * (Nat.log 2 N + 1)) :
    (∃ (x1 : ℝ),   (0 : ℝ) < x1 ∧     ∃ (x2 : ℕ),       ∀ (x3 : ℕ),         x2 ≤ x3 →           have x5 : ℕ := (2 : ℕ) ^ x3;           have x6 : Finset ℕ := {x6 ∈ Finset.range (x5 + (1 : ℕ)) | x5 ≤ (3 : ℕ) * x6 ∧ (3 : ℕ) * x6 ≤ (2 : ℕ) * x5};           x1 * ↑x5 / Real.log ↑x5 ^ (2 : ℕ) ≤ ↑{x7 ∈ x6 | Nat.Prime x7 ∧ Nat.Prime (x5 - x7)}.card) := by
  classical
  obtain ⟨c, hc, K, hmass⟩ := mass
  refine ⟨c, hc, K, ?_⟩
  intro k hk
  let N : ℕ := 2^k
  let W := (Finset.range (N+1)).filter (fun p => N ≤ 3*p ∧ 3*p ≤ 2*N)
  let pairs := W.filter (fun p => IsPrimePow p ∧ IsPrimePow (N-p))
  let good := W.filter (fun p => Nat.Prime p ∧ Nat.Prime (N-p))
  let bad := (Finset.range (N+1)).filter (fun m => IsPrimePow m ∧ ¬ Nat.Prime m)
  let B := (Nat.sqrt N + 1) * (Nat.log 2 N + 1)
  change c * (N : ℝ) / (Real.log N)^2 ≤ (good.card : ℝ)
  have hsub : pairs ⊆ good ∪ (bad ∪ bad.image (fun m => N - m)) := by
    intro p hp
    obtain ⟨hpW, hpPow, hqPow⟩ := Finset.mem_filter.mp hp
    have hpR := (Finset.mem_filter.mp hpW).1
    have hpn : p ≤ N := by simpa using Finset.mem_range.mp hpR
    by_cases hprime : Nat.Prime p
    · by_cases hq : Nat.Prime (N-p)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpW, hprime, hq⟩)
      · have hb : N-p ∈ bad :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hqPow, hq⟩
        exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨N-p, hb, by omega⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hpR, hpPow, hprime⟩))
  have hbad : bad.card ≤ B := proper N
  have hinj : (bad.image (fun m => N-m)).card ≤ bad.card := Finset.card_image_le
  have hcard : pairs.card ≤ good.card + 2*B := calc
    pairs.card ≤ (good ∪ (bad ∪ bad.image (fun m => N-m))).card := Finset.card_le_card hsub
    _ ≤ good.card + (bad ∪ bad.image (fun m => N-m)).card := Finset.card_union_le _ _
    _ ≤ good.card + 2*B := by have := Finset.card_union_le bad (bad.image (fun m => N-m)); omega
  have hreal : (pairs.card : ℝ) ≤ (good.card : ℝ) + ((2*B : ℕ) : ℝ) := by exact_mod_cast hcard
  have hm : c*(N : ℝ)/(Real.log N)^2 + ((2*B : ℕ) : ℝ) ≤ (pairs.card : ℝ) := hmass k hk
  linarith