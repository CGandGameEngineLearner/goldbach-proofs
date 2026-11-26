import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith

/-!
Finite orthogonal projection proof of the Liouville dilation variance bound.

The self-contained divisor-counting/covariance and multiplicative reindexing
proofs below adapt the accepted supporting proofs in upstream PR #2706
(snomiao) and PR #2722 (Tim Tan), respectively. No other project module is imported.
The Bessel step is a finite Cauchy--Schwarz argument. The final variance and
coefficient identities retain the zero endpoint L(0)=0.
-/


theorem dvd_indicator_sum_mul (N d : ℕ) (hd : 0 < d) (hdN : d ∣ N) :
    (d : ℝ) * (∑ t ∈ Finset.range N, (if d ∣ t then (1 : ℝ) else 0)) = N := by
  rcases hdN with ⟨m, rfl⟩
  have himg : (Finset.range (d * m)).filter (fun t => d ∣ t)
      = (Finset.range m).image (fun k => d * k) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨ht, k, rfl⟩
      exact ⟨k, lt_of_mul_lt_mul_left ht (Nat.zero_le d), rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨Nat.mul_lt_mul_of_pos_left hk hd, dvd_mul_right _ _⟩
  rw [← Finset.sum_filter, himg, Finset.sum_const,
    Finset.card_image_of_injective _ (mul_right_injective₀ hd.ne'), Finset.card_range]
  simp

theorem mean_zero (N p : ℕ) (_hN : 0 < N) (hp : Nat.Prime p) (hpN : p ∣ N) :
    ∑ t ∈ Finset.range N,
        ((p : ℝ) * (if p ∣ t then 1 else 0) - 1) = 0 := by
  calc
    ∑ t ∈ Finset.range N,
        ((p : ℝ) * (if p ∣ t then 1 else 0) - 1)
        = (p : ℝ) *
            (∑ t ∈ Finset.range N, (if p ∣ t then (1 : ℝ) else 0)) -
          ∑ t ∈ Finset.range N, (1 : ℝ) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = (p : ℝ) *
            (∑ t ∈ Finset.range N, (if p ∣ t then (1 : ℝ) else 0)) - N := by
      simp
    _ = 0 := by
      rw [dvd_indicator_sum_mul N p hp.pos hpN, sub_self]

theorem PEqualNP.Outside.L_goldbach_divisor_indicator_covariance :
    let X := fun (p t : ℕ) => (p : ℝ) * (if p ∣ t then 1 else 0) - 1
    ∀ (N p q : ℕ), 0 < N → Nat.Prime p → Nat.Prime q → p ∣ N → q ∣ N →
      (∑ t ∈ Finset.range N, X p t * X q t) / (N : ℝ) =
        if p = q then (p : ℝ) - 1 else 0 := by
  intro X N p q hN hp hq hpN hqN
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have expand : ∑ t ∈ Finset.range N, X p t * X q t
      = (p : ℝ) * q *
          (∑ t ∈ Finset.range N, (if p ∣ t ∧ q ∣ t then (1 : ℝ) else 0))
        - (p : ℝ) *
          (∑ t ∈ Finset.range N, (if p ∣ t then (1 : ℝ) else 0))
        - (q : ℝ) *
          (∑ t ∈ Finset.range N, (if q ∣ t then (1 : ℝ) else 0))
        + ∑ t ∈ Finset.range N, (1 : ℝ) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    simp only [X]
    by_cases h1 : p ∣ t <;> by_cases h2 : q ∣ t <;> simp [h1, h2] <;> ring
  have hone : ∑ t ∈ Finset.range N, (1 : ℝ) = N := by simp
  rw [expand, hone]
  have hcp := dvd_indicator_sum_mul N p hp.pos hpN
  have hcq := dvd_indicator_sum_mul N q hq.pos hqN
  by_cases hpq : p = q
  · subst hpq
    simp only [and_self, ite_true]
    rw [div_eq_iff hN']
    linear_combination ((p : ℝ) - 2) * hcp
  · simp only [hpq, ite_false]
    have hco : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
    have hiff : ∀ t : ℕ, (p ∣ t ∧ q ∣ t) ↔ p * q ∣ t := fun t =>
      ⟨fun h => hco.mul_dvd_of_dvd_of_dvd h.1 h.2,
       fun h => ⟨(dvd_mul_right p q).trans h, (dvd_mul_left q p).trans h⟩⟩
    simp only [hiff]
    have hcpq := dvd_indicator_sum_mul N (p * q) (Nat.mul_pos hp.pos hq.pos)
      (hco.mul_dvd_of_dvd_of_dvd hpN hqN)
    push_cast at hcpq
    rw [div_eq_zero_iff]
    left
    linear_combination hcpq - hcp - hcq

theorem PEqualNP.Outside.L_goldbach_liouville_multiple_average :
    let L := fun n : ℕ => if n = 0 then (0 : ℝ) else (-1 : ℝ) ^ n.primeFactorsList.length
    let C := fun n : ℕ => (∑ t ∈ Finset.range n, L t * L (n - t)) / (n : ℝ)
    ∀ (N p : ℕ), 0 < N → Nat.Prime p → p ∣ N →
      (∑ t ∈ (Finset.range N).filter (fun t => p ∣ t), L t * L (N - t)) /
          ((N / p : ℕ) : ℝ) = C (N / p) := by
  intro L C N p hN hp hpN
  have hp0 : 0 < p := hp.pos
  have hpne : p ≠ 0 := hp.pos.ne'
  set M : ℕ := N / p with hM
  have hNp : N = p * M := by
    rw [hM, mul_comm]
    exact (Nat.div_mul_cancel hpN).symm
  have hL0 : L 0 = 0 := by
    dsimp only [L]
    simp
  have hLp : ∀ s : ℕ, s ≠ 0 → L (p * s) = -L s := by
    intro s hs
    dsimp only [L]
    rw [ite_eq_right (by positivity : ¬p * s = 0), ite_eq_right hs]
    have hperm := Nat.perm_primeFactorsList_mul (a := p) (b := s) hpne hs
    rw [Nat.primeFactorsList_prime hp] at hperm
    have hlen : (p * s).primeFactorsList.length = s.primeFactorsList.length + 1 := by
      have h1 : ([p] ++ s.primeFactorsList).length = s.primeFactorsList.length + 1 := by
        simp
      rw [← h1]
      exact hperm.length_eq
    rw [hlen, pow_succ]
    ring
  have hreindex : (∑ t ∈ (Finset.range N).filter (fun t => p ∣ t), L t * L (N - t))
      = ∑ s ∈ Finset.range M, L (p * s) * L (N - p * s) := by
    refine Finset.sum_bij' (fun t _ => t / p) (fun s _ => p * s) ?_ ?_ ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht
      obtain ⟨htN, hpt⟩ := ht
      obtain ⟨s, rfl⟩ := hpt
      have hdiv : p * s / p = s := by
        rw [mul_comm p s]
        exact Nat.mul_div_left s hp0
      rw [hdiv]
      rw [hNp] at htN
      exact Finset.mem_range.mpr ((Nat.mul_lt_mul_left hp0).mp htN)
    · intro s hs
      have hsM : s < M := Finset.mem_range.mp hs
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ⟨s, rfl⟩⟩
      rw [hNp]
      exact Nat.mul_lt_mul_of_pos_left hsM hp0
    · intro t ht
      simp only [Finset.mem_filter] at ht
      exact Nat.mul_div_cancel' ht.2
    · intro s hs
      show p * s / p = s
      rw [mul_comm p s]
      exact Nat.mul_div_left s hp0
    · intro t ht
      simp only [Finset.mem_filter] at ht
      rw [Nat.mul_div_cancel' ht.2]
  have hterm : ∀ s ∈ Finset.range M,
      L (p * s) * L (N - p * s) = L s * L (M - s) := by
    intro s hs
    have hsM : s < M := Finset.mem_range.mp hs
    by_cases hs0 : s = 0
    · subst hs0
      simp only [mul_zero, Nat.sub_zero]
      rw [hL0]
      ring
    · have hMs : M - s ≠ 0 := (Nat.sub_pos_of_lt hsM).ne'
      have h1 := hLp s hs0
      have hsub : N - p * s = p * (M - s) := by
        rw [hNp]
        exact (Nat.mul_sub_left_distrib p M s).symm
      have h2 : L (N - p * s) = -L (M - s) := by
        rw [hsub]
        exact hLp (M - s) hMs
      rw [h1, h2]
      ring
  have hS : (∑ s ∈ Finset.range M, L (p * s) * L (N - p * s))
      = ∑ s ∈ Finset.range M, L s * L (M - s) := Finset.sum_congr rfl hterm
  rw [hreindex, hS]


/-!
# A weighted finite Bessel inequality in real Euclidean space

This file isolates the finite-dimensional orthogonality estimate used by the
Liouville mean-square argument.  The hypotheses permit arbitrary finite index
sets; the statement is specialized to `ℕ` for direct use in the parent proof.
-/

noncomputable section

open scoped BigOperators

namespace GoldbachResearch

/-- Finite weighted Bessel inequality for real finite sums.

This is proved directly from the finite Cauchy--Schwarz inequality and the
weighted orthogonality hypothesis.  The coefficient `g p / (W * d p)` gives a
projection whose square norm is `W` times the asserted Bessel energy. -/
theorem finite_real_bessel_weighted
    (s T : Finset ℕ) (W : ℝ) (x : ℕ → ℕ → ℝ)
    (f : ℕ → ℝ) (d : ℕ → ℝ) (hW : 0 < W)
    (hd : ∀ p ∈ s, 0 < d p)
    (hGram : ∀ p ∈ s, ∀ q ∈ s,
      (∑ t ∈ T, x p t * x q t) / W = if p = q then d p else 0) :
    (∑ p ∈ s, ((∑ t ∈ T, f t * x p t) / W) ^ 2 / d p) ≤
      (∑ t ∈ T, f t ^ 2) / W := by
  classical
  let g : ℕ → ℝ := fun p => ∑ t ∈ T, f t * x p t
  let c : ℕ → ℝ := fun p => g p / (W * d p)
  let B : ℝ := ∑ p ∈ s, (g p / W) ^ 2 / d p
  let K : ℝ := ∑ p ∈ s, c p * g p
  let Q : ℝ := ∑ p ∈ s, c p ^ 2 * (W * d p)
  let E : ℝ := ∑ t ∈ T, f t ^ 2
  have hdne : ∀ p ∈ s, d p ≠ 0 := fun p hp => (hd p hp).ne'
  have hWne : W ≠ 0 := hW.ne'

  have hc_mul (p : ℕ) (hp : p ∈ s) :
      c p * g p = W * ((g p / W) ^ 2 / d p) := by
    dsimp [c]
    field_simp [hWne, hdne p hp]
  have hc_sq (p : ℕ) (hp : p ∈ s) :
      c p ^ 2 * (W * d p) = W * ((g p / W) ^ 2 / d p) := by
    dsimp [c]
    field_simp [hWne, hdne p hp]
  have hK : K = W * B := by
    calc
      K = ∑ p ∈ s, W * ((g p / W) ^ 2 / d p) :=
        Finset.sum_congr rfl fun p hp => hc_mul p hp
      _ = W * B := by rw [Finset.mul_sum]
  have hQ : Q = W * B := by
    calc
      Q = ∑ p ∈ s, W * ((g p / W) ^ 2 / d p) :=
        Finset.sum_congr rfl fun p hp => hc_sq p hp
      _ = W * B := by rw [Finset.mul_sum]

  have hdot (p q : ℕ) (hp : p ∈ s) (hq : q ∈ s) :
      (∑ t ∈ T, x p t * x q t) = W * (if p = q then d p else 0) := by
    rw [← hGram p hp q hq]
    field_simp [hWne]

  have hquad :
      (∑ t ∈ T, (∑ p ∈ s, c p * x p t) ^ 2) =
        W * ∑ p ∈ s, c p ^ 2 * d p := by
    calc
      (∑ t ∈ T, (∑ p ∈ s, c p * x p t) ^ 2) =
          ∑ t ∈ T, ∑ p ∈ s, ∑ q ∈ s,
            (c p * x p t) * (c q * x q t) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [sq, Finset.sum_mul_sum]
      _ = ∑ p ∈ s, ∑ q ∈ s, ∑ t ∈ T,
            (c p * x p t) * (c q * x q t) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.sum_comm]
      _ = ∑ p ∈ s, ∑ q ∈ s,
            c p * c q * (∑ t ∈ T, x p t * x q t) := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        calc
          (∑ t ∈ T, (c p * x p t) * (c q * x q t)) =
              ∑ t ∈ T, (c p * c q) * (x p t * x q t) := by
            apply Finset.sum_congr rfl
            intro t ht
            ring
          _ = c p * c q * (∑ t ∈ T, x p t * x q t) := by
            rw [Finset.mul_sum]
      _ = ∑ p ∈ s, ∑ q ∈ s,
            c p * c q * (W * (if p = q then d p else 0)) := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        rw [hdot p q hp hq]
      _ = ∑ p ∈ s, c p ^ 2 * (W * d p) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.sum_eq_single p]
        · simp [pow_two]
        · intro q hq hqp
          simp [show p ≠ q from fun h => hqp h.symm]
        · intro hpnot
          exact (hpnot hp).elim
      _ = W * ∑ p ∈ s, c p ^ 2 * d p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring

  have hquadQ :
      (∑ t ∈ T, (∑ p ∈ s, c p * x p t) ^ 2) = Q := by
    rw [hquad]
    dsimp [Q]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring

  have hleft :
      (∑ t ∈ T, (∑ p ∈ s, c p * x p t) * f t) = K := by
    calc
      (∑ t ∈ T, (∑ p ∈ s, c p * x p t) * f t) =
          ∑ t ∈ T, ∑ p ∈ s, (c p * x p t) * f t := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.sum_mul]
      _ = ∑ p ∈ s, ∑ t ∈ T, (c p * x p t) * f t := by
        rw [Finset.sum_comm]
      _ = ∑ p ∈ s, c p * g p := by
        apply Finset.sum_congr rfl
        intro p hp
        calc
          (∑ t ∈ T, (c p * x p t) * f t) =
              ∑ t ∈ T, c p * (x p t * f t) := by
            apply Finset.sum_congr rfl
            intro t ht
            ring
          _ = c p * (∑ t ∈ T, x p t * f t) := by
            rw [Finset.mul_sum]
          _ = c p * g p := by
            congr 1
            apply Finset.sum_congr rfl
            intro t ht
            ring
      _ = K := rfl

  have hcs := Finset.sum_mul_sq_le_sq_mul_sq T
    (fun t => ∑ p ∈ s, c p * x p t) f
  have hbase : (W * B) ^ 2 ≤ (W * B) * E := by
    simpa [hleft, hquadQ, hK, hQ] using hcs
  have hB_nonneg : 0 ≤ B := by
    apply Finset.sum_nonneg
    intro p hp
    exact div_nonneg (sq_nonneg _) (hd p hp).le
  have hE_nonneg : 0 ≤ E := by
    apply Finset.sum_nonneg
    intro t ht
    exact sq_nonneg _
  have hB : B ≤ E / W := by
    by_cases hB0 : B = 0
    · rw [hB0]
      exact div_nonneg hE_nonneg hW.le
    · have hBpos : 0 < B := lt_of_le_of_ne hB_nonneg (Ne.symm hB0)
      have hWBpos : 0 < W * B := mul_pos hW hBpos
      have hWBle : W * B ≤ E := by
        exact le_of_mul_le_mul_left (by simpa [pow_two] using hbase) hWBpos
      exact (le_div_iff₀ hW).2 (by simpa [mul_comm] using hWBle)
  simpa [B, g, E] using hB

end GoldbachResearch


open scoped BigOperators

namespace DilationProof

def L (n : ℕ) : ℝ := if n = 0 then 0 else (-1 : ℝ) ^ n.primeFactorsList.length
def f (N t : ℕ) : ℝ := L t * L (N-t)
noncomputable def C (N : ℕ) : ℝ := (∑ t ∈ Finset.range N, f N t) / N
def X (p t : ℕ) : ℝ := (p : ℝ) * (if p ∣ t then 1 else 0) - 1

theorem L_sq (k : ℕ) (hk : k ≠ 0) : (L k)^2 = 1 := by
  dsimp [L]
  rw [ite_eq_right hk, ← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

theorem f_square_sum (N : ℕ) (hN : 0 < N) :
    (∑ t ∈ Finset.range N, (f N t)^2) = ((N-1 : ℕ) : ℝ) := by
  have ht : ∀ t ∈ Finset.range N, (f N t)^2 =
      (1 : ℝ) - (if t = 0 then 1 else 0) := by
    intro t ht
    by_cases h0 : t = 0
    · subst t; norm_num [f, L]
    · rw [ite_eq_right h0, sub_zero]
      dsimp [f]
      rw [mul_pow, L_sq t h0, L_sq (N-t) (by have := Finset.mem_range.mp ht; omega)]
      norm_num
  rw [Finset.sum_congr rfl ht, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_range, hN, ite_true]
  exact (Nat.cast_sub (by omega : 1 ≤ N)).symm

theorem centered_variance (N : ℕ) (hN : 0 < N) :
    (∑ t ∈ Finset.range N, (f N t - C N)^2) / (N : ℝ) =
      ((N-1 : ℕ) : ℝ) / N - (C N)^2 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hm : (∑ t ∈ Finset.range N, f N t) = (C N) * N := by
    exact (div_eq_iff hn).mp rfl
  have hexp : (∑ t ∈ Finset.range N, (f N t-C N)^2) =
      (∑ t ∈ Finset.range N, (f N t)^2) -
        2 * C N * (∑ t ∈ Finset.range N, f N t) + (N : ℝ) * (C N)^2 := by
    calc
      _ = ∑ t ∈ Finset.range N, ((f N t)^2 - 2*C N*f N t+(C N)^2) := by
        apply Finset.sum_congr rfl; intro t _; ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum]; simp
  rw [hexp, f_square_sum N hN, hm]
  field_simp
  ring

theorem centered_inner (N p : ℕ) (hN : 0 < N) (hp : p.Prime) (hpN : p ∣ N)
    (hz : (∑ t ∈ Finset.range N, X p t) = 0)
    (ha : (∑ t ∈ (Finset.range N).filter (fun t => p ∣ t), f N t) /
      ((N/p : ℕ) : ℝ) = C (N/p)) :
    (∑ t ∈ Finset.range N, (f N t-C N)*X p t) / (N : ℝ) =
      C (N/p)-C N := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hm : ((N/p : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.div_pos (Nat.le_of_dvd hN hpN) hp.pos).ne'
  have hav := (div_eq_iff hm).mp ha
  have hf : (∑ t ∈ Finset.range N, f N t) = C N * N :=
    (div_eq_iff hn).mp rfl
  have hprod : (p : ℝ) * ((N/p : ℕ) : ℝ) = N := by
    exact_mod_cast Nat.mul_div_cancel' hpN
  have he : (∑ t ∈ Finset.range N, f N t*X p t) =
      (p : ℝ)*(∑ t ∈ (Finset.range N).filter (fun t => p ∣ t), f N t) -
        ∑ t ∈ Finset.range N, f N t := by
    simp only [X, mul_sub, mul_one, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    by_cases ht : p ∣ t
    · simp [ht]; ring
    · simp [ht]
  have he' : (∑ t ∈ Finset.range N, (f N t-C N)*X p t) =
      ∑ t ∈ Finset.range N, f N t*X p t := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hz, mul_zero, sub_zero]
  apply (div_eq_iff hn).mpr
  rw [he', he, hav, hf]
  calc
    _ = C (N/p) * ((p : ℝ)*((N/p : ℕ) : ℝ)) - C N * N := by ring
    _ = _ := by rw [hprod]; ring

end DilationProof

theorem PEqualNP.Outside.L_goldbach_liouville_dilation_bessel :
    let L := fun n : ℕ => if n=0 then (0:ℝ) else (-1:ℝ)^n.primeFactorsList.length; let C := fun n : ℕ => (∑ t ∈ Finset.range n, L t * L (n-t))/(n:ℝ); ∀ N : ℕ, 0 < N → (∑ p ∈ N.divisors.filter Nat.Prime, (C (N/p)-C N)^2/((p:ℝ)-1)) ≤ ((N-1:ℕ):ℝ)/(N:ℝ)-(C N)^2 := by
  intro L C N hN
  change (∑ p ∈ N.divisors.filter Nat.Prime,
    (DilationProof.C (N/p)-DilationProof.C N)^2 / ((p : ℝ)-1)) ≤
      ((N-1 : ℕ) : ℝ)/(N : ℝ) - (DilationProof.C N)^2
  have hW : (0 : ℝ) < N := by exact_mod_cast hN
  have hprime : ∀ p ∈ N.divisors.filter Nat.Prime, p.Prime ∧ p ∣ N := by
    intro p hp
    exact ⟨(Finset.mem_filter.mp hp).2, (Nat.mem_divisors.mp (Finset.mem_filter.mp hp).1).1⟩
  have hd : ∀ p ∈ N.divisors.filter Nat.Prime, (0 : ℝ) < (p : ℝ)-1 := by
    intro p hp
    have := (hprime p hp).1.two_le
    have : (2 : ℝ) ≤ p := by exact_mod_cast this
    linarith only [this]
  have hg : ∀ p ∈ N.divisors.filter Nat.Prime, ∀ q ∈ N.divisors.filter Nat.Prime,
      (∑ t ∈ Finset.range N, DilationProof.X p t * DilationProof.X q t) / (N : ℝ) =
        if p=q then (p : ℝ)-1 else 0 := by
    intro p hp q hq
    exact PEqualNP.Outside.L_goldbach_divisor_indicator_covariance N p q hN
      (hprime p hp).1 (hprime q hq).1 (hprime p hp).2 (hprime q hq).2
  have hi : ∀ p ∈ N.divisors.filter Nat.Prime,
      (∑ t ∈ Finset.range N, (DilationProof.f N t-DilationProof.C N)*DilationProof.X p t) /
        (N : ℝ) = DilationProof.C (N/p)-DilationProof.C N := by
    intro p hp
    exact DilationProof.centered_inner N p hN (hprime p hp).1 (hprime p hp).2
      (mean_zero N p hN (hprime p hp).1 (hprime p hp).2)
      (PEqualNP.Outside.L_goldbach_liouville_multiple_average N p hN
        (hprime p hp).1 (hprime p hp).2)
  calc
    _ = ∑ p ∈ N.divisors.filter Nat.Prime,
        ((∑ t ∈ Finset.range N,
          (DilationProof.f N t-DilationProof.C N)*DilationProof.X p t)/(N : ℝ))^2 /
            ((p : ℝ)-1) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hi p hp]
    _ ≤ (∑ t ∈ Finset.range N, (DilationProof.f N t-DilationProof.C N)^2)/(N : ℝ) :=
      GoldbachResearch.finite_real_bessel_weighted (N.divisors.filter Nat.Prime)
        (Finset.range N) (N : ℝ) DilationProof.X
        (fun t => DilationProof.f N t-DilationProof.C N) (fun p => (p : ℝ)-1) hW hd hg
    _ = _ := DilationProof.centered_variance N hN
