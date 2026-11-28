import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Average the reflected prime correlation in the first-summand strip [n/2,5n/8)
over H consecutive offsets. Subtract the loss from evaluating at offset zero
before removing the prime logarithms and absorbing the proper-power margin.
-/

open Finset Filter
open scoped Topology

-- child 1 zh: 设 n=2^k、H=2^⌈7k/12⌉。对所有充分大的 k，在首项从 n/2 到 5n/8（不含上端）的区间上，对 0≤d<H 的反射素数对数权相关求和，至少为 Hn/32。
-- child 1 en: For all large k, put n=2^k and H=2^ceil(7k/12). Summing the reflected prime log-weight correlations at shifts 0 through H-1 over first summands in [n/2,5n/8) gives at least Hn/32.
-- child 2 zh: 在同一区间与偏移范围，对所有充分大的 k，反射相关在所有偏移上的和减去零偏移相关的 H 倍，至多为 Hn/64。
-- child 2 en: For all large k, on the same strip and shift range, the sum of reflected correlations minus H times the correlation at offset zero is at most Hn/64.

theorem Conjectures.Cuts.Cut3bad1b9dc881b44bf03d0e26
    (h₁ : ∃ K : ℕ, ∀ k ≥ K, let n : ℕ := 2^k
      let u := n/8
      let H : ℕ := 2^((7*k+11)/12)
      let w : ℕ → ℝ := fun p => if Nat.Prime p then Real.log p else 0
      let s : ℕ → ℝ := fun d => ∑ i ∈ Finset.range u, w (4*u+i)*w (4*u-i+d)
      (H:ℝ)*n/32 ≤ ∑ d ∈ Finset.range H, s d)
    (h₂ : ∃ J : ℕ, ∀ k ≥ J, let n : ℕ := 2^k
      let u := n/8
      let H : ℕ := 2^((7*k+11)/12)
      let w : ℕ → ℝ := fun p => if Nat.Prime p then Real.log p else 0
      let s : ℕ → ℝ := fun d => ∑ i ∈ Finset.range u, w (4*u+i)*w (4*u-i+d)
      (∑ d ∈ Finset.range H, s d) - (H:ℝ)*s 0 ≤ (H:ℝ)*n/64) : (∃ (x1 : ℝ),   (0 : ℝ) < x1 ∧     ∃ (x2 : ℕ),       ∀ x3 ≥ x2,         have x5 : ℕ := (2 : ℕ) ^ x3;         have x6 : Finset ℕ := {x6 ∈ Finset.range (x5 + (1 : ℕ)) | x5 ≤ (3 : ℕ) * x6 ∧ (3 : ℕ) * x6 ≤ (2 : ℕ) * x5};         have x7 : Finset ℕ := {x7 ∈ x6 | IsPrimePow x7 ∧ IsPrimePow (x5 - x7)};         x1 * ↑x5 / Real.log ↑x5 ^ (2 : ℕ) + ↑((2 : ℕ) * ((x5.sqrt + (1 : ℕ)) * (Nat.log (2 : ℕ) x5 + (1 : ℕ)))) ≤ ↑x7.card) := by
  let Registered : Prop := (∃ (x1 : ℝ),   (0 : ℝ) < x1 ∧     ∃ (x2 : ℕ),       ∀ x3 ≥ x2,         have x5 : ℕ := (2 : ℕ) ^ x3;         have x6 : Finset ℕ := {x6 ∈ Finset.range (x5 + (1 : ℕ)) | x5 ≤ (3 : ℕ) * x6 ∧ (3 : ℕ) * x6 ≤ (2 : ℕ) * x5};         have x7 : Finset ℕ := {x7 ∈ x6 | IsPrimePow x7 ∧ IsPrimePow (x5 - x7)};         x1 * ↑x5 / Real.log ↑x5 ^ (2 : ℕ) + ↑((2 : ℕ) * ((x5.sqrt + (1 : ℕ)) * (Nat.log (2 : ℕ) x5 + (1 : ℕ)))) ≤ ↑x7.card)

  let window (n : ℕ) : Finset ℕ :=
    (Finset.range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n)

  let pairs (n : ℕ) : Finset ℕ :=
    (window n).filter (fun p => IsPrimePow p ∧ IsPrimePow (n-p))

  let budget (n : ℕ) : ℕ :=
    2 * ((n.sqrt + 1) * (Nat.log 2 n + 1))


  have budget_eventually (δ : ℝ) (hδ : 0 < δ) :
      ∀ᶠ n : ℕ in atTop, (budget n : ℝ) * (Real.log n)^2 ≤ δ * n := by
    have hnat := tendsto_natCast_atTop_atTop (R := ℝ)
    have hlog := Real.tendsto_log_atTop.comp hnat
    have hsmall := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) (show 0 < (1/2 : ℝ) by norm_num)).bound
      (show 0 < δ/12 by positivity)
    filter_upwards [hnat.eventually hsmall, hlog.eventually_ge_atTop 1,
      eventually_ge_atTop (1 : ℕ)] with n hs hl hn
    change 1 ≤ Real.log (n : ℝ) at hl
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hsqrt : (1 : ℝ) ≤ Real.sqrt n := (Real.one_le_sqrt).2 hn1
    have hnatLog := Real.natLog_le_logb n 2
    simp only [Real.logb, Nat.cast_ofNat] at hnatLog
    have hl2 := Real.log_two_gt_d9
    have hlogbound : (Nat.log 2 n : ℝ) ≤ 2 * Real.log n :=
      hnatLog.trans ((div_le_iff₀ (by linarith : 0 < Real.log 2)).2
        (by nlinarith only [mul_nonneg (show 0 ≤ Real.log n by linarith) (show 0 ≤ 2 * Real.log 2 - 1 by linarith)]))
    have ha : (n.sqrt : ℝ) + 1 ≤ 2 * Real.sqrt n := by linarith [Real.nat_sqrt_le_real_sqrt (a := n)]
    have hb : (Nat.log 2 n : ℝ) + 1 ≤ 3 * Real.log n := by linarith
    have hbudget : (budget n : ℝ) ≤ 12 * Real.sqrt n * Real.log n := by
      unfold budget
      push_cast
      nlinarith only [mul_le_mul ha hb (by positivity) (by positivity)]
    have hcub : (Real.log n)^3 ≤ (δ/12) * Real.sqrt n := by
      simpa only [Real.norm_eq_abs, ← Real.sqrt_eq_rpow, Real.rpow_ofNat,
        abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ Real.log n) 3),
        abs_of_nonneg (Real.sqrt_nonneg _)] using hs
    calc
      _ ≤ (12 * Real.sqrt n * Real.log n) * (Real.log n)^2 :=
        mul_le_mul_of_nonneg_right hbudget (sq_nonneg _)
      _ = (12 * Real.sqrt n) * (Real.log n)^3 := by ring
      _ ≤ (12 * Real.sqrt n) * ((δ/12) * Real.sqrt n) :=
        mul_le_mul_of_nonneg_left hcub (by positivity)
      _ = δ * (Real.sqrt n)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg n)]


  have add_budget
      (h : ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∀ k ≥ K,
        c * (2^k : ℕ) / (Real.log (2^k : ℕ))^2 ≤ ((pairs (2^k)).card : ℝ)) :
      Registered := by
    obtain ⟨c,hc,K,h⟩ := h
    obtain ⟨T,hT⟩ := eventually_atTop.mp (budget_eventually (c/2) (by positivity))
    refine ⟨c/2, by positivity, max (max K T) 1, ?_⟩
    intro k hk
    let n : ℕ := 2^k
    have hkK : K ≤ k := by omega
    have hkT : T ≤ k := by omega
    have hk1 : 1 ≤ k := by omega
    have hkn : k < n := by simpa [n] using (Nat.lt_pow_self (a := 2) (n := k) (by decide))
    have hn : 1 < n := by omega
    have hlog : 0 < (Real.log n)^2 := by
      have := Real.log_pos (show (1 : ℝ) < n by exact_mod_cast hn)
      positivity
    change (c/2) * (n : ℝ) / (Real.log n)^2 + (budget n : ℝ) ≤ ((pairs n).card : ℝ)
    have hb := (le_div_iff₀ hlog).2 (hT n (by omega))
    calc
      _ ≤ (c/2) * (n : ℝ) / (Real.log n)^2 + (c/2) * n / (Real.log n)^2 := by linarith
      _ = c * (n : ℝ) / (Real.log n)^2 := by ring
      _ ≤ _ := h k hkK

  let weight (p : ℕ) : ℝ :=
    if p.Prime then Real.log p else 0


  let central (m : ℕ) : Finset ℕ :=
    (range (m + 1)).filter (fun p =>
      m ≤ 3*p ∧ 3*p ≤ 2*m ∧ p.Prime ∧ (m-p).Prime)


  let score (u d : ℕ) : ℝ :=
    ∑ i ∈ range u, weight (4*u+i) * weight (4*u-i+d)


  have score_le_count {u d : ℕ} (hu : 0 < u) (hd : d ≤ u) :
      score u d ≤ ((central (8*u+d)).card : ℝ) * (Real.log ((8*u : ℕ) : ℝ))^2 := by
    classical
    let S := (range u).filter (fun i => (4*u+i).Prime ∧ (4*u-i+d).Prime)
    let L := Real.log ((8*u : ℕ) : ℝ)
    have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 8*u by omega))
    have hsub : S.image (fun i => 4*u+i) ⊆ central (8*u+d) := by
      intro p hp
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
      obtain ⟨hir,hp',hq⟩ := mem_filter.mp hi
      have hlt := mem_range.mp hir
      apply mem_filter.mpr
      exact ⟨mem_range.mpr (by omega), by omega, by omega, hp',
        (show 8*u+d-(4*u+i) = 4*u-i+d by omega) ▸ hq⟩
    have hcard : S.card ≤ (central (8*u+d)).card := calc
      _ = (S.image (fun i => 4*u+i)).card :=
        (card_image_of_injective _ (by intro a b hab; exact Nat.add_left_cancel hab)).symm
      _ ≤ _ := card_le_card hsub
    have restrict : score u d = ∑ i ∈ S, weight (4*u+i) * weight (4*u-i+d) := by
      unfold score S
      rw [sum_filter]
      apply sum_congr rfl
      intro i _
      by_cases hp : (4*u+i).Prime <;> by_cases hq : (4*u-i+d).Prime <;> simp [weight,hp,hq]
    rw [restrict]
    calc
      _ ≤ ∑ _i ∈ S, L^2 := by
        apply sum_le_sum
        intro i hi
        obtain ⟨hir,hp,hq⟩ := mem_filter.mp hi
        have hiu := mem_range.mp hir
        have hb (m : ℕ) (hm : m.Prime) (hle : m ≤ 8*u) : Real.log (m:ℝ) ≤ L :=
          Real.log_le_log (by exact_mod_cast hm.pos) (by exact_mod_cast hle)
        simpa only [weight, ite_eq_left hp, ite_eq_left hq, pow_two] using
          (mul_le_mul (hb _ hp (by omega)) (hb _ hq (by omega))
            (Real.log_nonneg (by exact_mod_cast hq.one_le)) hL)
      _ = (S.card:ℝ) * L^2 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (sq_nonneg _)

  have central_le_prime_powers (m : ℕ) :
      (central m).card ≤ (pairs m).card := by
    apply card_le_card
    intro p hp
    obtain ⟨hpR,hlo,hhi,hp',hq'⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hpR,hlo,hhi⟩,hp'.isPrimePow,hq'.isPrimePow⟩

  obtain ⟨J,hJ⟩ := h₂
  obtain ⟨K,hK⟩ := h₁
  apply add_budget
  refine ⟨1/64, by norm_num, max (max K J) 4, ?_⟩
  intro k hk
  let n : ℕ := 2^k
  let H : ℕ := 2^((7*k+11)/12)
  have hdvd : 8 ∣ n := by
    change (2:ℕ)^3 ∣ 2^k
    exact pow_dvd_pow 2 (by omega)
  have hn : 8*(n/8) = n := Nat.mul_div_cancel' hdvd
  have hn16 : 16 ≤ n := (show (2:ℕ)^4 ≤ 2^k from Nat.pow_le_pow_right (by decide) (by omega))
  have avg : (H:ℝ)*n/32 ≤ ∑ d ∈ range H, score (n/8) d := hK k (by omega)
  have err : (∑ d ∈ range H, score (n/8) d) - (H:ℝ)*score (n/8) 0 ≤ (H:ℝ)*n/64 := hJ k (by omega)
  have hzero : (1/64 : ℝ)*n ≤ score (n/8) 0 := by
    have hpos : 0 < (H:ℝ) := by dsimp [H]; positivity
    apply (mul_le_mul_iff_right₀ hpos).mp
    nlinarith only [avg,err]
  have cap := score_le_count (show 0 < n/8 by omega) (show 0 ≤ n/8 by omega)
  rw [hn, Nat.add_zero] at cap
  have hlog := sq_pos_of_pos (Real.log_pos (show (1 : ℝ) < (n:ℝ) by exact_mod_cast (show 1 < n by omega)))
  apply (div_le_iff₀ hlog).mpr
  exact hzero.trans (cap.trans (mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (central_le_prime_powers n)) hlog.le))
