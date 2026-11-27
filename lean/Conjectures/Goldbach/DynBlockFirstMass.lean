import Mathlib
import Conjectures.Goldbach.DyadicCellShortPrimeFloor

/-!
# L-goldbach-dyn-block-first-mass (`Conjectures.Goldbach.DynBlockFirstMass`)

Pinned toolchain / library: `v4.36.0`, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

## Attribution
The zero-weight explicit-formula assembly (`GoldbachOC103.*`, `Vx`, `V7e`, `V86`, `V1e`, `V6i`)
and the Chebyshev `ψ`-window bridge (`GoldbachR11WindowBridge.norm_actual_principal_window_eq_abs_psi`)
are imported directly from the accepted community module `Conjectures.Goldbach.DyadicCellShortPrimeFloor`
(PR #3746, commit `ef8ddfa37003c69f326f69188c774106953d3969`, merged in `58074f8d`).

## Proof Outline
1. `actual_principal_window_half_of_zero_weights`:
   Re-assembles `GoldbachOC103.actual_principal_window_of_zero_weights` with the relaxed lower
   window hypothesis `X^(3/4) / 2 ≤ h`, giving `‖V42 h X‖ ≤ 5 * h / 16` (`h/16` low + `h/8` high
   + `h/8` residual).
2. `theta_window_lower_of_half`:
   Applies `GoldbachR11WindowBridge.norm_actual_principal_window_eq_abs_psi` and Mathlib's
   `Chebyshev.psi_sub_theta_le_mul_sqrt` to absorb prime powers into `h / 16`, yielding
   `θ(n + h) - θ(n) ≥ (5 / 8) * h` for all `n ≥ N₀` and `n^(3/4) / 2 ≤ h ≤ n`.
3. `dynBlock_window_three_fourths`:
   Using `r = ⌊⁴√X⌋ ≥ 64`, proves `h = W X - 2 * ⌊√X⌋` satisfies
   `(y - 1)^(3/4) / 2 ≤ h`, `h ≤ y - 1`, and `W X ≤ 2 * h` uniformly for `X ≤ y`, `y + W X ≤ 2 * X`.
4. `shortIntervalPrimeLowerBound_of_zero_weights`:
   Taking base point `y - 1` and `log p ≤ log (2X) ≤ 2 * log X`, deduces
   `((Q X y).card : ℝ) ≥ (5 / 32) * (W X / log X)`.
5. Combines with the verified shifted-window product counting lemma and dyadic small-prime
   lower bound to prove the unconditional frozen theorem `Conjectures.Goldbach.DynBlockFirstMass`.
-/

namespace Conjectures.Goldbach

/-! ### Part 1: Half-Window Explicit Formula Assembly (Reusing PR #3746) -/

section ExplicitFormulaHalf

open Finset
open scoped BigOperators Classical
open GoldbachOC103 Vx V7e V86 V1e V6i

/-- Half-window variant of `GoldbachOC103.actual_principal_window_of_zero_weights` (PR #3746):
relaxing `X^(3/4) ≤ h` to `X^(3/4) / 2 ≤ h` relaxes the high and residual budgets from `h / 16`
to `h / 8` each, giving total explicit-formula error `‖V42 h X‖ ≤ 5 * h / 16`. -/
private theorem actual_principal_window_half_of_zero_weights
    (hzero : ActualZeroWeightBounds) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ h : ℕ,
      X ^ (3 / 4 : ℝ) / 2 ≤ (h : ℝ) → (h : ℝ) ≤ X →
      ‖V42 h X‖ ≤ 5 * (h : ℝ) / 16 := by
  obtain ⟨C, hC, Xz, hz⟩ := hzero
  obtain ⟨D, hD, hpoint⟩ := V10s
  obtain ⟨Xb, hb⟩ := eventual_pointwise_budgets D C C hD.le
  refine ⟨max Xz Xb, ?_⟩
  intro X hX h hlower hupper
  have hbud := hb X ((le_max_right _ _).trans hX)
  have hX4 := hbud.scale_ge_four
  have hXpos : 0 < X := by linarith
  have hδ : 0 < X ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hV : 0 < X ^ (5 / 16 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  obtain ⟨hlo, hcount⟩ := hz X ((le_max_left _ _).trans hX) hX4
    hbud.log_ge_one hbud.split_ge_two hbud.split_le_scale
  let S := V3b X
  let A := S.filter (fun c => |c.val.1.im| ≤ X ^ (5 / 16 : ℝ))
  let R := S.filter (fun c => ¬ |c.val.1.im| ≤ X ^ (5 / 16 : ℝ))
  let K := C * (Real.log X) ^ 14 / (X ^ (5 / 16 : ℝ) * Real.sqrt (X ^ (5 / 16 : ℝ)))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hS : ∀ c ∈ S, |c.val.1.im| ≤ X := by
    intro c hc
    exact (V5l X c).mp hc
  have hlow : (∑ c ∈ A, X ^ (c.val.1.re - 1)) ≤ C / (Real.log X) ^ 4 :=
    hlo A (fun c hc => (mem_filter.mp hc).2)
  have hhigh : ∀ v : ℝ, X ^ (5 / 16 : ℝ) ≤ v →
      (∑ c ∈ R.filter (fun c => |c.val.1.im| ≤ v), X ^ (c.val.1.re - 1)) ≤
        K * v * Real.sqrt v := by
    intro v hv
    exact weight_count_clamp R X (X ^ (5 / 16 : ℝ)) K v hV hbud.split_le_scale hK hv
      (fun c hc => hS c (mem_filter.mp hc).1) hcount
  have hpacket := smoothed_packet_of_weight_bounds S (fun c => c.val.1)
    X X h (X ^ (2 / 3 : ℝ)) (X ^ (5 / 16 : ℝ)) (C / (Real.log X) ^ 4) K
    (by linarith) le_rfl (by linarith) hh hupper hδ hbud.smoothing_le_half hV hK
    (fun c _ => c.property.1.1) (fun c _ => c.property.1.2.1.le) hlow hhigh
  have hLowBudget : 2 * (h : ℝ) * (C / (Real.log X) ^ 4) ≤ (h : ℝ) / 16 := by
    calc
      _ = (h : ℝ) * (2 * C / (Real.log X) ^ 4) := by ring
      _ ≤ (h : ℝ) * (1 / 16) := mul_le_mul_of_nonneg_left hbud.low_budget hh
      _ = _ := by ring
  have hX34_step : X ^ (3 / 4 : ℝ) / 16 ≤ (h : ℝ) / 8 := by linarith
  have hHighBudget : 576 * X ^ 2 * K / (X ^ (2 / 3 : ℝ) * Real.sqrt (X ^ (5 / 16 : ℝ))) ≤
      (h : ℝ) / 8 := by
    dsimp only [K]
    rw [high_coefficient_normalization C X (X ^ (5 / 16 : ℝ)) (X ^ (2 / 3 : ℝ)) hV hδ]
    exact hbud.high_budget.trans hX34_step
  have hPacketBudget :
      ‖V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
        (X ^ (2 / 3 : ℝ)) X‖ ≤ 3 * (h : ℝ) / 16 := by
    linarith
  have hres := hpoint X X (X ^ (2 / 3 : ℝ)) X h hX4
    ⟨le_rfl, by linarith⟩ hupper hbud.smoothing_ge_one hbud.smoothing_le_half
    (by linarith)
  have hResidualBudget :
      ‖V42 h X +
        V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X ^ (2 / 3 : ℝ)) X‖ ≤ (h : ℝ) / 8 := by
    exact hres.trans (hbud.residual_budget.trans hX34_step)
  have hnorm : ‖V42 h X‖ ≤
      ‖V42 h X +
        V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X ^ (2 / 3 : ℝ)) X‖ +
      ‖V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X ^ (2 / 3 : ℝ)) X‖ := by
    simpa only [add_sub_cancel_right] using
      norm_sub_le (V42 h X +
        V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X ^ (2 / 3 : ℝ)) X)
        (V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X ^ (2 / 3 : ℝ)) X)
  linarith

/-- Uniform natural-number half-window `θ`-lower bound obtained by combining
`actual_principal_window_half_of_zero_weights`, `GoldbachR11WindowBridge.norm_actual_principal_window_eq_abs_psi`,
and Mathlib's `Chebyshev.psi_sub_theta_le_mul_sqrt`. -/
private theorem theta_window_lower_of_half
    (hzero : ActualZeroWeightBounds) :
    ∃ N₀ : ℕ, ∀ n h : ℕ, N₀ ≤ n →
      (n : ℝ) ^ (3 / 4 : ℝ) / 2 ≤ (h : ℝ) → h ≤ n →
      (5 / 8 : ℝ) * (h : ℝ) ≤
        Chebyshev.theta ((n + h : ℕ) : ℝ) - Chebyshev.theta (n : ℝ) := by
  obtain ⟨X₀, hX₀⟩ := actual_principal_window_half_of_zero_weights hzero
  obtain ⟨M₁, hM₁⟩ := exists_nat_ge X₀
  obtain ⟨C_pp, hC_pp⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let C' : ℝ := max C_pp 0
  let K₀ : ℕ := Nat.ceil (64 * C')
  refine ⟨max 4 (max M₁ (K₀ ^ 4)), ?_⟩
  intro n h hn hlower hupper
  have hn4 : 4 ≤ n := le_trans (le_max_left _ _) hn
  have hnM₁ : M₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnK : K₀ ^ 4 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hV42 : ‖V42 h (n : ℝ)‖ ≤ 5 * (h : ℝ) / 16 :=
    hX₀ (n : ℝ) (hM₁.trans (by exact_mod_cast hnM₁)) h hlower (by exact_mod_cast hupper)
  have hpsi_abs :
      |Chebyshev.psi ((n + h : ℕ) : ℝ) - Chebyshev.psi (n : ℝ) - (h : ℝ)| ≤ 5 * (h : ℝ) / 16 := by
    have hbridge := GoldbachR11WindowBridge.norm_actual_principal_window_eq_abs_psi n h
    simpa only [Nat.cast_add] using hbridge ▸ hV42
  have hpsi_lb : (11 / 16 : ℝ) * (h : ℝ) ≤
      Chebyshev.psi ((n + h : ℕ) : ℝ) - Chebyshev.psi (n : ℝ) := by
    have := (abs_le.mp hpsi_abs).1
    linarith
  have hC'_nonneg : 0 ≤ C' := le_max_right _ _
  have hC_le_C' : C_pp ≤ C' := le_max_left _ _
  have h64C' : 64 * C' ≤ (K₀ : ℝ) := Nat.le_ceil (64 * C')
  have hsqrt_pow4 : (64 * C' * Real.sqrt (n : ℝ)) ^ 4 ≤ ((n : ℝ) ^ (3 / 4 : ℝ)) ^ 4 := by
    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hK4 : (K₀ : ℝ) ^ 4 ≤ (n : ℝ) := by exact_mod_cast hnK
    have h64_4 : (64 * C') ^ 4 ≤ (n : ℝ) :=
      le_trans (pow_le_pow_left₀ (by positivity) h64C' 4) hK4
    have hlhs : (64 * C' * Real.sqrt (n : ℝ)) ^ 4 = (64 * C') ^ 4 * (n : ℝ) ^ 2 := by
      calc
        (64 * C' * Real.sqrt (n : ℝ)) ^ 4
            = (64 * C') ^ 4 * ((Real.sqrt (n : ℝ)) ^ 2) ^ 2 := by ring
        _ = (64 * C') ^ 4 * (n : ℝ) ^ 2 := by rw [Real.sq_sqrt hn_nonneg]
    have hrhs : ((n : ℝ) ^ (3 / 4 : ℝ)) ^ 4 = (n : ℝ) ^ 3 := by
      have h4eq : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
      have h3eq : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
      rw [← Real.rpow_natCast, ← h4eq, ← Real.rpow_mul hn_nonneg]
      have hexp : (3 / 4 : ℝ) * (4 : ℝ) = (3 : ℝ) := by norm_num
      rw [hexp, h3eq, Real.rpow_natCast]
    rw [hlhs, hrhs]
    calc
      (64 * C') ^ 4 * (n : ℝ) ^ 2 ≤ (n : ℝ) * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right h64_4 (sq_nonneg _)
      _ = (n : ℝ) ^ 3 := by ring
  have hsqrt_bound : 64 * C' * Real.sqrt (n : ℝ) ≤ (n : ℝ) ^ (3 / 4 : ℝ) :=
    le_of_pow_le_pow_left₀ (by norm_num : 4 ≠ 0) (Real.rpow_nonneg (Nat.cast_nonneg n) _) hsqrt_pow4
  have hsqrt_nh : Real.sqrt ((n + h : ℕ) : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    have hle : ((n + h : ℕ) : ℝ) ≤ 4 * (n : ℝ) := by exact_mod_cast (by omega : n + h ≤ 4 * n)
    calc
      Real.sqrt ((n + h : ℕ) : ℝ) ≤ Real.sqrt (4 * (n : ℝ)) := Real.sqrt_le_sqrt hle
      _ = Real.sqrt (2 ^ 2 * (n : ℝ)) := by norm_num
      _ = 2 * Real.sqrt (n : ℝ) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hpp_loss :
      Chebyshev.psi ((n + h : ℕ) : ℝ) - Chebyshev.theta ((n + h : ℕ) : ℝ) ≤ (h : ℝ) / 16 := by
    have h1 := hC_pp ((n + h : ℕ) : ℝ)
    have h2 : C_pp * Real.sqrt ((n + h : ℕ) : ℝ) ≤ C' * (2 * Real.sqrt (n : ℝ)) :=
      le_trans (mul_le_mul_of_nonneg_right hC_le_C' (Real.sqrt_nonneg _))
        (mul_le_mul_of_nonneg_left hsqrt_nh hC'_nonneg)
    linarith
  have htheta_le_psi : Chebyshev.theta (n : ℝ) ≤ Chebyshev.psi (n : ℝ) :=
    Chebyshev.theta_le_psi (n : ℝ)
  linarith

end ExplicitFormulaHalf

/-! ### Part 2: Frozen Definitions & Shifted-Window Product Counting Lemma -/

/-- Even integers in `[X, 2X]`. -/
def E (X : ℕ) : Finset ℕ :=
  (Finset.Icc X (2 * X)).filter (fun n => Even n)

/-- Small primes in `[⌊√X⌋, 2⌊√X⌋]`. -/
def P (X : ℕ) : Finset ℕ :=
  (Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime

/-- Number of representations `n = p + q` with `p ∈ P X` and `q` prime. -/
def H (X n : ℕ) : ℕ :=
  ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n - p))).card

/-- Dynamic block window width `W X = ⌊√X⌋ * ⌊⁴√X⌋ ≍ X^(3/4)`. -/
def W (X : ℕ) : ℕ :=
  Nat.sqrt X * Nat.sqrt (Nat.sqrt X)

/-- Dynamic block of even integers in `[y, y + W X)` inside `[X, 2X]`. -/
def B (X y : ℕ) : Finset ℕ :=
  (E X).filter (fun n => y ≤ n ∧ n < y + W X)

/-- Normalized first-mass scale `M X = √X / (log X)^2`. -/
noncomputable def M (X : ℕ) : ℝ :=
  Real.sqrt (X : ℝ) / (Real.log (X : ℝ)) ^ 2

/-- Shifted short-interval large-prime window `[y, y + W X - 2⌊√X⌋)`. -/
def Q (X y : ℕ) : Finset ℕ :=
  (Finset.Ico y (y + W X - 2 * Nat.sqrt X)).filter Nat.Prime

private lemma two_mul_sqrt_le_W {X : ℕ} (hX : 16 ≤ X) : 2 * Nat.sqrt X ≤ W X := by
  have hsqrt4 : 4 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by omega)
  have hqsqrt2 : 2 ≤ Nat.sqrt (Nat.sqrt X) := Nat.le_sqrt.mpr (by omega)
  calc
    2 * Nat.sqrt X = Nat.sqrt X * 2 := Nat.mul_comm 2 (Nat.sqrt X)
    _ ≤ Nat.sqrt X * Nat.sqrt (Nat.sqrt X) := Nat.mul_le_mul_left (Nat.sqrt X) hqsqrt2
    _ = W X := rfl

private lemma add_mem_B_of_mem_P_mem_Q {X y p q : ℕ}
    (hX : 16 ≤ X) (hXy : X ≤ y) (hyW : y + W X ≤ 2 * X)
    (hp : p ∈ P X) (hq : q ∈ Q X y) :
    p + q ∈ B X y := by
  have hsqrt4 : 4 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by omega)
  have hW : 2 * Nat.sqrt X ≤ W X := two_mul_sqrt_le_W hX
  simp only [P, Q, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico] at hp hq
  rcases hp with ⟨⟨hp_lo, hp_hi⟩, hp_prime⟩
  rcases hq with ⟨⟨hq_lo, hq_hi⟩, hq_prime⟩
  have hp_odd : Odd p := hp_prime.odd_of_ne_two (by omega)
  have hq_odd : Odd q := hq_prime.odd_of_ne_two (by omega)
  have h_even : Even (p + q) := hp_odd.add_odd hq_odd
  have h_lt : p + q < y + W X := by omega
  simp only [B, E, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨⟨by omega, by omega⟩, h_even⟩, by omega, h_lt⟩

/-- Natural-number shifted-window product counting lemma. -/
theorem shifted_window_product_count_nat {X y : ℕ}
    (hX : 16 ≤ X) (hXy : X ≤ y) (hyW : y + W X ≤ 2 * X) :
    (P X).card * (Q X y).card ≤ ∑ n ∈ B X y, H X n := by
  let S : Finset (ℕ × ℕ) :=
    (B X y ×ˢ P X).filter (fun np => np.2 ≤ np.1 ∧ Nat.Prime (np.1 - np.2))
  have hS_card : S.card = ∑ n ∈ B X y, H X n := by
    dsimp only [S]
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [H]
    rw [Finset.card_filter]
  rw [← hS_card, ← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun pq : ℕ × ℕ => (pq.1 + pq.2, pq.1)) ?_ ?_
  · intro pq hpq
    simp only [Finset.mem_coe, Finset.mem_product] at hpq
    rcases hpq with ⟨hp, hq⟩
    have hq_prime : Nat.Prime pq.2 := (Finset.mem_filter.mp hq).2
    have hmemB : pq.1 + pq.2 ∈ B X y := add_mem_B_of_mem_P_mem_Q hX hXy hyW hp hq
    simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hmemB, hp⟩, Nat.le_add_right pq.1 pq.2, ?_⟩
    simpa [Nat.add_sub_cancel_left] using hq_prime
  · intro pq₁ _ pq₂ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2 (by omega)

/-- Real-valued shifted-window product counting lemma. -/
theorem shifted_window_product_count {X y : ℕ}
    (hX : 16 ≤ X) (hXy : X ≤ y) (hyW : y + W X ≤ 2 * X) :
    ((P X).card : ℝ) * ((Q X y).card : ℝ) ≤ ∑ n ∈ B X y, (H X n : ℝ) := by
  have hnat := shifted_window_product_count_nat hX hXy hyW
  have hcast : (((P X).card * (Q X y).card : ℕ) : ℝ) ≤ ((∑ n ∈ B X y, H X n : ℕ) : ℝ) :=
    Nat.cast_le.mpr hnat
  simpa [Nat.cast_mul, Nat.cast_sum] using hcast

/-! ### Part 3: Unconditional Dyadic Small-Prime Band Lower Bound -/

private lemma primeCounting_sub_le_card_Icc_prime {N : ℕ} (hN : 1 ≤ N) :
    (Nat.primeCounting (2 * N) : ℝ) - (Nat.primeCounting N : ℝ) ≤
      (((Finset.Icc N (2 * N)).filter Nat.Prime).card : ℝ) := by
  have hdisj : Disjoint (Nat.primesLE (N - 1)) ((Finset.Icc N (2 * N)).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [Nat.mem_primesLE] at hp1
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp2
    omega
  have hunion :
      Nat.primesLE (N - 1) ∪ (Finset.Icc N (2 * N)).filter Nat.Prime = Nat.primesLE (2 * N) := by
    ext p
    simp only [Finset.mem_union, Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro (⟨hle, hp⟩ | ⟨⟨_, hle⟩, hp⟩)
      · exact ⟨by omega, hp⟩
      · exact ⟨hle, hp⟩
    · rintro ⟨hle, hp⟩
      by_cases h : p ≤ N - 1
      · exact Or.inl ⟨h, hp⟩
      · exact Or.inr ⟨⟨by omega, hle⟩, hp⟩
  have hcard :
      Nat.primeCounting (N - 1) + ((Finset.Icc N (2 * N)).filter Nat.Prime).card =
        Nat.primeCounting (2 * N) := by
    rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting,
      ← Finset.card_union_of_disjoint hdisj, hunion]
  have hmono : Nat.primeCounting (N - 1) ≤ Nat.primeCounting N :=
    Nat.monotone_primeCounting (Nat.sub_le N 1)
  have hcardR :
      (Nat.primeCounting (N - 1) : ℝ) + (((Finset.Icc N (2 * N)).filter Nat.Prime).card : ℝ) =
        (Nat.primeCounting (2 * N) : ℝ) := by
    exact_mod_cast hcard
  have hmonoR : (Nat.primeCounting (N - 1) : ℝ) ≤ (Nat.primeCounting N : ℝ) :=
    Nat.cast_le.mpr hmono
  linarith

/-- Unconditional lower bound on the dyadic small-prime band `P X` from Mathlib's `WeakPNT`. -/
theorem small_prime_band_lower_bound :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ X₁ : ℕ, ∀ X ≥ X₁,
      c₁ * (Real.sqrt (X : ℝ) / Real.log (X : ℝ)) ≤ ((P X).card : ℝ) := by
  have hpi : Filter.Tendsto
      (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x))
      Filter.atTop (nhds 1) := by
    have h := (Asymptotics.isEquivalent_iff_tendsto_one (by
      filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
      exact div_ne_zero (by linarith) (Real.log_pos hx).ne')).mp Nat.isEquivalent_primeCounting
    exact h.congr (fun _ => rfl)
  have hlo : ∀ᶠ x : ℝ in Filter.atTop,
      (7 / 8 : ℝ) < (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x) :=
    (tendsto_order.mp hpi).1 (7 / 8) (by norm_num)
  have hhi : ∀ᶠ x : ℝ in Filter.atTop,
      (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x) < (9 / 8 : ℝ) :=
    (tendsto_order.mp hpi).2 (9 / 8) (by norm_num)
  obtain ⟨A₁, hA₁⟩ := Filter.eventually_atTop.1 hlo
  obtain ⟨A₂, hA₂⟩ := Filter.eventually_atTop.1 hhi
  let N₀ : ℕ := max 256 (max (Nat.ceil A₁) (Nat.ceil A₂))
  refine ⟨31 / 72, by norm_num, max (N₀ * N₀) 16, ?_⟩
  intro X hX
  let N : ℕ := Nat.sqrt X
  have hN_ge : N₀ ≤ N := Nat.le_sqrt.mpr (le_trans (le_max_left _ _) hX)
  have hN256 : 256 ≤ N := le_trans (le_max_left _ _) hN_ge
  have hN_A1 : A₁ ≤ ((2 * N : ℕ) : ℝ) := by
    have h1 : A₁ ≤ (Nat.ceil A₁ : ℝ) := Nat.le_ceil A₁
    have h2 : Nat.ceil A₁ ≤ N :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN_ge
    have h3 : (Nat.ceil A₁ : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr h2
    have h4 : (N : ℝ) ≤ ((2 * N : ℕ) : ℝ) := Nat.cast_le.mpr (by omega)
    linarith
  have hN_A2 : A₂ ≤ (N : ℝ) := by
    have h1 : A₂ ≤ (Nat.ceil A₂ : ℝ) := Nat.le_ceil A₂
    have h2 : Nat.ceil A₂ ≤ N :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN_ge
    exact le_trans h1 (Nat.cast_le.mpr h2)
  have hlogN_pos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlog2N_pos : 0 < Real.log ((2 * N : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * N))
  have hlog2N_le : Real.log ((2 * N : ℕ) : ℝ) ≤ (9 / 8 : ℝ) * Real.log (N : ℝ) := by
    have h256 : (2 : ℝ) ^ (8 : ℕ) ≤ (N : ℝ) := by
      have : (256 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN256
      norm_num at this ⊢
      exact this
    have hlog2 : 8 * Real.log 2 ≤ Real.log (N : ℝ) := by
      have h := Real.log_le_log (by positivity) h256
      rwa [Real.log_pow, Nat.cast_ofNat] at h
    have hmul : Real.log ((2 * N : ℕ) : ℝ) = Real.log 2 + Real.log (N : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) (by positivity)]
    linarith
  have hpi2N : (14 / 9 : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) ≤ (Nat.primeCounting (2 * N) : ℝ) := by
    have h1 := hA₁ ((2 * N : ℕ) : ℝ) hN_A1
    rw [Nat.floor_natCast] at h1
    have hden_pos : 0 < ((2 * N : ℕ) : ℝ) / Real.log ((2 * N : ℕ) : ℝ) :=
      div_pos (by positivity) hlog2N_pos
    have h2 : (7 / 8 : ℝ) * (((2 * N : ℕ) : ℝ) / Real.log ((2 * N : ℕ) : ℝ)) ≤
        (Nat.primeCounting (2 * N) : ℝ) :=
      le_of_lt ((lt_div_iff₀ hden_pos).mp h1)
    have h3 : ((2 * N : ℕ) : ℝ) / ((9 / 8 : ℝ) * Real.log (N : ℝ)) ≤
        ((2 * N : ℕ) : ℝ) / Real.log ((2 * N : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hlog2N_pos hlog2N_le
    have h4 : (7 / 8 : ℝ) * (((2 * N : ℕ) : ℝ) / ((9 / 8 : ℝ) * Real.log (N : ℝ))) =
        (14 / 9 : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) := by
      rw [Nat.cast_mul, Nat.cast_ofNat]
      ring
    linarith [mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 7 / 8)]
  have hpiN : (Nat.primeCounting N : ℝ) ≤ (9 / 8 : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) := by
    have h1 := hA₂ (N : ℝ) hN_A2
    rw [Nat.floor_natCast] at h1
    have hden_pos : 0 < (N : ℝ) / Real.log (N : ℝ) := div_pos (by positivity) hlogN_pos
    exact le_of_lt ((div_lt_iff₀ hden_pos).mp h1)
  have hband : (31 / 72 : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) ≤ ((P X).card : ℝ) := by
    have hsub := primeCounting_sub_le_card_Icc_prime (N := N) (by omega)
    change (Nat.primeCounting (2 * N) : ℝ) - (Nat.primeCounting N : ℝ) ≤ ((P X).card : ℝ) at hsub
    linarith
  have hN_le_sqrt : (N : ℝ) ≤ Real.sqrt (X : ℝ) := by
    refine Real.le_sqrt_of_sq_le ?_
    have hsq : N * N ≤ X := Nat.sqrt_le X
    have hsq' : (N : ℝ) * (N : ℝ) ≤ (X : ℝ) := by exact_mod_cast hsq
    simpa [sq] using hsq'
  have hsqrt_le_twoN : Real.sqrt (X : ℝ) ≤ 2 * (N : ℝ) := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have hlt : X < (N + 1) * (N + 1) := Nat.lt_succ_sqrt X
    have hle : X ≤ (2 * N) * (2 * N) := by nlinarith
    have hle' : (X : ℝ) ≤ (2 * (N : ℝ)) * (2 * (N : ℝ)) := by exact_mod_cast hle
    simpa [sq] using hle'
  have hlogN_le_half : Real.log (N : ℝ) ≤ Real.log (X : ℝ) / 2 := by
    calc
      Real.log (N : ℝ) ≤ Real.log (Real.sqrt (X : ℝ)) :=
        Real.log_le_log (by positivity) hN_le_sqrt
      _ = Real.log (X : ℝ) / 2 := Real.log_sqrt (by positivity)
  have hlogX_pos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hratio : Real.sqrt (X : ℝ) / Real.log (X : ℝ) ≤ (N : ℝ) / Real.log (N : ℝ) := by
    rw [div_le_div_iff₀ hlogX_pos hlogN_pos]
    calc
      Real.sqrt (X : ℝ) * Real.log (N : ℝ)
          ≤ (2 * (N : ℝ)) * Real.log (N : ℝ) :=
            mul_le_mul_of_nonneg_right hsqrt_le_twoN hlogN_pos.le
      _ ≤ (2 * (N : ℝ)) * (Real.log (X : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left hlogN_le_half (by positivity)
      _ = (N : ℝ) * Real.log (X : ℝ) := by ring
  exact le_trans (mul_le_mul_of_nonneg_left hratio (by norm_num)) hband

/-! ### Part 4: Dynamic Window `3/4`-Scale Geometry & Short-Interval Prime Lower Bound -/

private lemma rpow_three_fourths_le_of_cube_le_pow_four {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpoly : a ^ 3 ≤ b ^ 4) :
    a ^ (3 / 4 : ℝ) ≤ b := by
  have h1 : (a ^ (3 / 4 : ℝ)) ^ (4 : ℝ) ≤ b ^ (4 : ℝ) := by
    rw [← Real.rpow_mul ha]
    have hexp : (3 / 4 : ℝ) * (4 : ℝ) = (3 : ℝ) := by norm_num
    rw [hexp]
    have h3eq : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
    have h4eq : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
    rw [h3eq, h4eq, Real.rpow_natCast, Real.rpow_natCast]
    exact hpoly
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg (Real.rpow_nonneg ha _) _) h1
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  rw [← Real.rpow_mul (Real.rpow_nonneg ha _), ← Real.rpow_mul hb] at h2
  have hexp4 : (4 : ℝ) * (1 / 4 : ℝ) = 1 := by norm_num
  rw [hexp4, Real.rpow_one, Real.rpow_one] at h2
  exact h2

/-- For `X ≥ 64^4` (`4096 * 4096`), `X ≤ y`, `y + W X ≤ 2 * X`, the shifted window
`h = W X - 2 * ⌊√X⌋` satisfies `(y - 1)^(3/4) / 2 ≤ h`, `h ≤ y - 1`, `W X ≤ 2 * h`, and
`2 * ⌊√X⌋ ≤ W X`. -/
private lemma dynBlock_window_three_fourths {X y : ℕ}
    (hX : 4096 * 4096 ≤ X) (hXy : X ≤ y) (hyW : y + W X ≤ 2 * X) :
    let h := W X - 2 * Nat.sqrt X
    ((y - 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ) / 2 ≤ (h : ℝ) ∧
      h ≤ y - 1 ∧ W X ≤ 2 * h ∧ 2 * Nat.sqrt X ≤ W X := by
  intro h
  let s : ℕ := Nat.sqrt X
  let r : ℕ := Nat.sqrt s
  have hs : 4096 ≤ s := Nat.le_sqrt.mpr hX
  have hr : 64 ≤ r := Nat.le_sqrt.mpr hs
  have hr2_le_s : r ^ 2 ≤ s := by simpa [sq] using Nat.sqrt_le s
  have hs_lt : s < (r + 1) ^ 2 := by simpa [sq] using Nat.lt_succ_sqrt s
  have hX_lt : X < (r + 1) ^ 4 := by
    have h1 : X < (s + 1) * (s + 1) := Nat.lt_succ_sqrt X
    have h2 : s + 1 ≤ (r + 1) ^ 2 := by omega
    calc
      X < (s + 1) * (s + 1) := h1
      _ ≤ (r + 1) ^ 2 * (r + 1) ^ 2 := Nat.mul_le_mul h2 h2
      _ = (r + 1) ^ 4 := by ring
  have hW_eq : W X = s * r := rfl
  have h2s_le : 2 * s ≤ s * r := by nlinarith
  have hh_add : h + 2 * s = s * r := Nat.sub_add_cancel h2s_le
  have hW_le_2h : W X ≤ 2 * h := by nlinarith
  have hh_le_ym1 : h ≤ y - 1 := by omega
  have hr2_sub_le_h : r ^ 2 * (r - 2) ≤ h := by
    have hmul : s * (r - 2) = h := by
      have h1 : s * (r - 2) + 2 * s = s * r := by
        calc
          s * (r - 2) + 2 * s = s * ((r - 2) + 2) := by ring
          _ = s * r := by congr 1; omega
      omega
    rw [← hmul]
    exact Nat.mul_le_mul_right (r - 2) hr2_le_s
  have h7_le_8h : 7 * (r + 1) ^ 3 ≤ 8 * h := by
    have hpoly : 7 * (r + 1) ^ 3 ≤ 8 * (r ^ 2 * (r - 2)) := by
      have hr_sub : r - 2 + 2 = r := by omega
      nlinarith
    exact le_trans hpoly (Nat.mul_le_mul_left 8 hr2_sub_le_h)
  have hym1_le : y - 1 ≤ 2 * (r + 1) ^ 4 := by omega
  have hcube_le_pow4 : (y - 1) ^ 3 ≤ (2 * h) ^ 4 := by
    have h1 : (y - 1) ^ 3 ≤ (2 * (r + 1) ^ 4) ^ 3 := Nat.pow_le_pow_left hym1_le 3
    have h2 : (7 * (r + 1) ^ 3) ^ 4 ≤ (8 * h) ^ 4 := Nat.pow_le_pow_left h7_le_8h 4
    have h1' : (y - 1) ^ 3 ≤ 8 * (r + 1) ^ 12 := by
      calc
        (y - 1) ^ 3 ≤ (2 * (r + 1) ^ 4) ^ 3 := h1
        _ = 8 * (r + 1) ^ 12 := by ring
    have h2' : 2401 * (r + 1) ^ 12 ≤ 4096 * h ^ 4 := by
      calc
        2401 * (r + 1) ^ 12 = (7 * (r + 1) ^ 3) ^ 4 := by ring
        _ ≤ (8 * h) ^ 4 := h2
        _ = 4096 * h ^ 4 := by ring
    have h3 : 2401 * (y - 1) ^ 3 ≤ 32768 * h ^ 4 := by
      calc
        2401 * (y - 1) ^ 3 ≤ 2401 * (8 * (r + 1) ^ 12) := Nat.mul_le_mul_left 2401 h1'
        _ = 8 * (2401 * (r + 1) ^ 12) := by ring
        _ ≤ 8 * (4096 * h ^ 4) := Nat.mul_le_mul_left 8 h2'
        _ = 32768 * h ^ 4 := by ring
    have h4 : (2 * h) ^ 4 = 16 * h ^ 4 := by ring
    omega
  have hpow : ((y - 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ) ≤ 2 * (h : ℝ) := by
    have hcast : (((y - 1 : ℕ) : ℝ)) ^ 3 ≤ (2 * (h : ℝ)) ^ 4 := by exact_mod_cast hcube_le_pow4
    exact rpow_three_fourths_le_of_cube_le_pow_four (by positivity) (by positivity) hcast
  exact ⟨by linarith, hh_le_ym1, hW_le_2h, h2s_le⟩

private lemma theta_sub_eq_sum_Ico_prime {y h : ℕ} (hy : 1 ≤ y) (hh : 1 ≤ h) :
    Chebyshev.theta ((y - 1 + h : ℕ) : ℝ) - Chebyshev.theta ((y - 1 : ℕ) : ℝ) =
      ∑ p ∈ (Finset.Ico y (y + h)).filter Nat.Prime, Real.log (p : ℝ) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
  have hdisj : Disjoint (Nat.primesLE (y - 1)) ((Finset.Ico y (y + h)).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [Nat.mem_primesLE] at hp1
    simp only [Finset.mem_filter, Finset.mem_Ico] at hp2
    omega
  have hunion :
      Nat.primesLE (y - 1) ∪ (Finset.Ico y (y + h)).filter Nat.Prime =
        Nat.primesLE (y - 1 + h) := by
    ext p
    simp only [Finset.mem_union, Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro (⟨hle, hp⟩ | ⟨⟨_, hlt⟩, hp⟩)
      · exact ⟨by omega, hp⟩
      · exact ⟨by omega, hp⟩
    · rintro ⟨hle, hp⟩
      by_cases hpy : p ≤ y - 1
      · exact Or.inl ⟨hpy, hp⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, hp⟩
  rw [← hunion, Finset.sum_union hdisj, add_sub_cancel_left]

/-- Unconditional short-interval prime lower bound on `Q X y` (explicit `c₂ = 5 / 32`),
derived from PR #3746's `ActualZeroWeightBounds`. -/
private theorem shortIntervalPrimeLowerBound_of_zero_weights
    (hzero : GoldbachOC103.ActualZeroWeightBounds) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₂ : ℕ, ∀ X ≥ X₂, ∀ y : ℕ,
      X ≤ y → y + W X ≤ 2 * X →
      c₂ * ((W X : ℝ) / Real.log (X : ℝ)) ≤ ((Q X y).card : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := theta_window_lower_of_half hzero
  refine ⟨5 / 32, by norm_num, max (4096 * 4096) (N₀ + 1), ?_⟩
  intro X hX y hXy hyW
  have hX_big : 4096 * 4096 ≤ X := le_trans (le_max_left _ _) hX
  have hN₀_le : N₀ ≤ y - 1 := by
    have : N₀ + 1 ≤ X := le_trans (le_max_right _ _) hX
    omega
  have hadm := dynBlock_window_three_fourths hX_big hXy hyW
  dsimp only at hadm
  rcases hadm with ⟨hpow, hh_le_ym1, hW_le_2h, h2s_le⟩
  let h : ℕ := W X - 2 * Nat.sqrt X
  have hs_pos : 4096 ≤ Nat.sqrt X := Nat.le_sqrt.mpr hX_big
  have hW_pos : 2 ≤ W X := by omega
  have hh_pos : 1 ≤ h := by omega
  have htheta := hN₀ (y - 1) h hN₀_le hpow hh_le_ym1
  have hQ_eq : Q X y = (Finset.Ico y (y + h)).filter Nat.Prime := by
    simp only [Q, h, Nat.add_sub_assoc h2s_le]
  have hsum_eq :
      Chebyshev.theta ((y - 1 + h : ℕ) : ℝ) - Chebyshev.theta ((y - 1 : ℕ) : ℝ) =
        ∑ p ∈ Q X y, Real.log (p : ℝ) := by
    rw [hQ_eq]
    exact theta_sub_eq_sum_Ico_prime (by omega) hh_pos
  have hlogX_pos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hlog2X_le : Real.log ((2 * X : ℕ) : ℝ) ≤ 2 * Real.log (X : ℝ) := by
    have h2X_le : 2 * X ≤ X * X := by nlinarith
    have h1 : Real.log ((2 * X : ℕ) : ℝ) ≤ Real.log ((X : ℝ) * (X : ℝ)) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < 2 * X)) (by exact_mod_cast h2X_le)
    rw [Real.log_mul (by positivity) (by positivity)] at h1
    linarith
  have hsum_ub : ∑ p ∈ Q X y, Real.log (p : ℝ) ≤ ((Q X y).card : ℝ) * (2 * Real.log (X : ℝ)) := by
    calc
      ∑ p ∈ Q X y, Real.log (p : ℝ)
          ≤ ∑ _p ∈ Q X y, (2 * Real.log (X : ℝ)) := by
            refine Finset.sum_le_sum fun p hp => ?_
            rw [hQ_eq, Finset.mem_filter, Finset.mem_Ico] at hp
            have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.2.pos
            have hp_le : p ≤ 2 * X := by omega
            exact le_trans (Real.log_le_log hp_pos (by exact_mod_cast hp_le)) hlog2X_le
      _ = ((Q X y).card : ℝ) * (2 * Real.log (X : ℝ)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
  have hW_le_2hR : (W X : ℝ) ≤ 2 * (h : ℝ) := by exact_mod_cast hW_le_2h
  have hcomb : (5 / 16 : ℝ) * (W X : ℝ) ≤ ((Q X y).card : ℝ) * (2 * Real.log (X : ℝ)) := by
    linarith [htheta, hsum_eq, hsum_ub]
  have hdiv := (div_le_iff₀ (by positivity : 0 < 2 * Real.log (X : ℝ))).mpr hcomb
  have hlhs : (5 / 32 : ℝ) * ((W X : ℝ) / Real.log (X : ℝ)) =
      (5 / 16 : ℝ) * (W X : ℝ) / (2 * Real.log (X : ℝ)) := by
    ring
  rw [hlhs]
  exact hdiv

/-! ### Part 5: Unconditional Frozen Theorem `Conjectures.Goldbach.DynBlockFirstMass` -/

/-- Complete unconditional proof of the frozen theorem `Conjectures.Goldbach.DynBlockFirstMass`
(`L-goldbach-dyn-block-first-mass`). -/
theorem DynBlockFirstMass :
    let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n);
    let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime;
    let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card;
    let W := fun X : ℕ => Nat.sqrt X * Nat.sqrt (Nat.sqrt X);
    let B := fun (X y : ℕ) => (E X).filter (fun n => y ≤ n ∧ n < y + W X);
    let M := fun X : ℕ => Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2;
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ,
      X ≤ y → y + W X ≤ 2*X → c*(W X:ℝ)*M X ≤ ∑ n ∈ B X y, (H X n:ℝ) := by
  obtain ⟨c₁, hc₁, X₁, hP⟩ := small_prime_band_lower_bound
  obtain ⟨c₂, hc₂, X₂, hQ⟩ :=
    shortIntervalPrimeLowerBound_of_zero_weights GoldbachOC103.actual_zero_weight_bounds
  refine ⟨c₁ * c₂, mul_pos hc₁ hc₂, max 16 (max X₁ X₂), ?_⟩
  intro X hX y hXy hyW
  have h16 : 16 ≤ X := le_trans (le_max_left _ _) hX
  have hX1 : X₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hX2 : X₂ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hlogX_pos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hP_bound : c₁ * (Real.sqrt (X : ℝ) / Real.log (X : ℝ)) ≤ ((P X).card : ℝ) :=
    hP X hX1
  have hQ_bound : c₂ * ((W X : ℝ) / Real.log (X : ℝ)) ≤ ((Q X y).card : ℝ) :=
    hQ X hX2 y hXy hyW
  have hprod : ((P X).card : ℝ) * ((Q X y).card : ℝ) ≤ ∑ n ∈ B X y, (H X n : ℝ) :=
    shifted_window_product_count h16 hXy hyW
  have hP_nonneg : 0 ≤ c₁ * (Real.sqrt (X : ℝ) / Real.log (X : ℝ)) := by positivity
  have hQ_nonneg : 0 ≤ c₂ * ((W X : ℝ) / Real.log (X : ℝ)) := by positivity
  have hmul :
      (c₁ * (Real.sqrt (X : ℝ) / Real.log (X : ℝ))) *
          (c₂ * ((W X : ℝ) / Real.log (X : ℝ))) ≤
        ((P X).card : ℝ) * ((Q X y).card : ℝ) :=
    mul_le_mul hP_bound hQ_bound hQ_nonneg (le_trans hP_nonneg hP_bound)
  have halg :
      c₁ * c₂ * (W X : ℝ) * (Real.sqrt (X : ℝ) / (Real.log (X : ℝ)) ^ 2) =
        (c₁ * (Real.sqrt (X : ℝ) / Real.log (X : ℝ))) *
          (c₂ * ((W X : ℝ) / Real.log (X : ℝ))) := by
    ring
  change c₁ * c₂ * (W X : ℝ) * (Real.sqrt (X : ℝ) / (Real.log (X : ℝ)) ^ 2) ≤
      ∑ n ∈ B X y, (H X n : ℝ)
  exact halg.trans_le (hmul.trans hprod)

end Conjectures.Goldbach
