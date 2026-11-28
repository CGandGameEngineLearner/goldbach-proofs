import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

open Finset
open scoped BigOperators

namespace PrimeSquareFourier

private noncomputable def turn : ℂ := 2 * (Real.pi : ℂ) * Complex.I

private noncomputable def phase (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * turn)

private theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  simp only [phase, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem phase_nat_mul (k : ℕ) (t : ℝ) : phase (k * t) = phase t ^ k := by
  rw [phase, phase, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

private theorem phase_int (k : ℤ) : phase (k : ℝ) = 1 := by
  simpa only [phase, turn, Complex.ofReal_intCast] using Complex.exp_int_mul_two_pi_mul_I k

private theorem phase_norm (t : ℝ) : ‖phase t‖ = 1 := by
  simp [phase, turn, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

private theorem frozen_phase (r s : ℝ) :
    Complex.exp (↑(2 * Real.pi * r * s) * Complex.I) = phase (r * s) := by
  unfold phase turn
  congr 1
  push_cast
  ring

private theorem row_root (p : ℕ) (hp : Nat.Prime p) (a : ℤ)
    (ha : a.natAbs.Coprime (p ^ 2)) :
    ∑ v ∈ range p, (phase ((a : ℝ) / p)) ^ v = 0 := by
  let ζ := phase ((a : ℝ) / p)
  have pR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have pC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have root : ζ ^ p = 1 := by
    rw [show ζ = phase ((a : ℝ) / p) from rfl, ← phase_nat_mul]
    rw [show (p : ℝ) * ((a : ℝ) / p) = a by field_simp]
    exact phase_int a
  have root_ne : ζ ≠ 1 := by
    intro h
    change Complex.exp (↑((a : ℝ) / p) * turn) = 1 at h
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
    have hc : turn ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_pos.ne')) Complex.I_ne_zero
    change ↑((a : ℝ) / p) * turn = (k : ℂ) * turn at hk
    have he : (a : ℂ) / (p : ℂ) = (k : ℂ) := by
      exact_mod_cast mul_right_cancel₀ hc hk
    have ia : a = k * (p : ℤ) := by exact_mod_cast (div_eq_iff pC).mp he
    have hd : p ∣ a.natAbs := by
      rw [ia, Int.natAbs_mul, Int.natAbs_natCast]
      exact dvd_mul_left _ _
    have hd' : p ∣ p ^ 2 := by exact dvd_pow_self _ (by decide)
    have hOne : p ∣ 1 := by simpa only [ha.gcd_eq_one] using Nat.dvd_gcd hd hd'
    exact hp.not_dvd_one hOne
  have hsum := geom_sum_mul_neg ζ p
  rw [root, sub_self] at hsum
  exact (mul_eq_zero.mp hsum).resolve_right (sub_ne_zero.mpr root_ne.symm)

end PrimeSquareFourier

open PrimeSquareFourier

theorem Conjectures.Cuts.Taska315e3c3ebb6e113f5a86bc3 :
have x1 : (ℕ → ℝ) → ℕ → ℝ → ℂ := fun (x1 : ℕ → ℝ) (x2 : ℕ) (x3 : ℝ) => ∑ x4 ∈ Finset.range x2, ↑(x1 x4) * Complex.exp (↑((2 : ℝ) * Real.pi * ↑x4 * x3) * Complex.I); have x2 : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun (x2 : ℕ → ℝ) (x3 x4 : ℕ) =>   have x5 : ℕ → ℕ → ℝ := fun (x5 x6 : ℕ) => ∑ x7 ∈ Finset.range x3 with x7 % x4 ^ (2 : ℕ) = x5 + x4 * x6, x2 x7;   ∑ x6 ∈ Finset.range x4, ∑ x7 ∈ Finset.range x4, (x5 x6 x7 - (∑ x8 ∈ Finset.range x4, x5 x6 x8) / ↑x4) ^ (2 : ℕ); ∀ (x3 : ℕ → ℝ) (x4 x5 : ℕ) (x6 : ℤ), Nat.Prime x5 → x6.natAbs.Coprime (x5 ^ (2 : ℕ)) → ‖x1 x3 x4 (↑x6 / ↑(x5 ^ (2 : ℕ)))‖ ≤ ↑x5 * √(x2 x3 x4 x5) := by
  dsimp only
  intro w N p a hp ha
  classical
  let q := p ^ 2
  let α : ℝ := (a : ℝ) / q
  let P (n : ℕ) := phase ((n : ℝ) * α)
  let B (u v : ℕ) := ∑ n ∈ range N with n % q = u + p * v, w n
  let mean (u : ℕ) := (∑ v ∈ range p, B u v) / (p : ℝ)
  let D (i : ℕ × ℕ) := B i.1 i.2 - mean i.1
  let idx := range p ×ˢ range p
  have pR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have qpos : 0 < q := pow_pos hp.pos _
  have qR : (q : ℝ) ≠ 0 := by exact_mod_cast qpos.ne'
  have periodic (n : ℕ) : P n = P (n % q) := by
    let k : ℕ := n / q
    have decomp : (n : ℝ) = (↑(n % q) : ℝ) + (q : ℝ) * (k : ℝ) := by
      exact_mod_cast (Nat.mod_add_div n q).symm
    have hfreq : (n : ℝ) * α = (↑(n % q) : ℝ) * α + (↑(a * (k : ℤ)) : ℝ) := by
      conv_lhs => rw [decomp]
      dsimp only [α]
      rw [Int.cast_mul, Int.cast_natCast]
      field_simp [qR] <;> ring
    dsimp only [P]
    rw [hfreq, phase_add, phase_int, mul_one]
  have row_phase (u v : ℕ) : P (u + p * v) = P u * (phase ((a : ℝ) / p)) ^ v := by
    rw [← phase_nat_mul]
    dsimp only [P]
    rw [← phase_add]
    congr 1
    dsimp [α, q]
    push_cast
    field_simp [pR] <;> ring
  have row_cancel (u : ℕ) : ∑ v ∈ range p, P (u + p * v) = 0 := by
    simp_rw [row_phase, ← mul_sum, row_root p hp a ha, mul_zero]
  let digits (n : ℕ) : ℕ × ℕ := (n % q % p, n % q / p)
  have maps_to (n : ℕ) (_ : n ∈ range N) : digits n ∈ idx := by
    refine mem_product.mpr ⟨mem_range.mpr (Nat.mod_lt _ hp.pos), mem_range.mpr ?_⟩
    exact (Nat.div_lt_iff_lt_mul hp.pos).mpr (by simpa [q, pow_two] using Nat.mod_lt n qpos)
  have digit_eq (n u v : ℕ) (hu : u < p) :
      digits n = (u, v) ↔ n % q = u + p * v := by
    constructor
    · intro h
      have h₁ : n % q % p = u := congrArg Prod.fst h
      have h₂ : n % q / p = v := congrArg Prod.snd h
      rw [← h₁, ← h₂, Nat.mod_add_div]
    · intro h
      dsimp [digits]
      rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu, Nat.add_mul_div_left _ _ hp.pos,
        Nat.div_eq_of_lt hu, zero_add]
  have grouped :
      (∑ n ∈ range N, (w n : ℂ) * P n) =
        ∑ i ∈ idx, (B i.1 i.2 : ℂ) * P (i.1 + p * i.2) := by
    rw [← sum_fiberwise_of_maps_to maps_to (fun n => (w n : ℂ) * P n)]
    refine sum_congr rfl ?_
    rintro ⟨u, v⟩ hi
    have hu := mem_range.mp (mem_product.mp hi).1
    have hfilter : (range N).filter (fun n => digits n = (u, v)) =
        (range N).filter (fun n => n % q = u + p * v) := by
      ext n
      simp only [mem_filter, digit_eq n u v hu]
    rw [hfilter]
    calc
      _ = ∑ n ∈ range N with n % q = u + p * v, (w n : ℂ) * P (u + p * v) := by
        refine sum_congr rfl fun n hn => ?_
        rw [periodic n, (mem_filter.mp hn).2]
      _ = _ := by simp [B, sum_mul]
  have centered :
      (∑ i ∈ idx, (B i.1 i.2 : ℂ) * P (i.1 + p * i.2)) =
        ∑ i ∈ idx, (D i : ℂ) * P (i.1 + p * i.2) := by
    simp only [idx, sum_product]
    refine sum_congr rfl fun u _ => ?_
    simp only [D, Complex.ofReal_sub, sub_mul, sum_sub_distrib, ← mul_sum, row_cancel,
      mul_zero, sub_zero]
  simp_rw [frozen_phase]
  change ‖∑ n ∈ range N, (w n : ℂ) * P n‖ ≤
    (p : ℝ) * Real.sqrt (∑ u ∈ range p, ∑ v ∈ range p, D (u, v) ^ 2)
  rw [grouped, centered]
  have cs := sq_sum_le_card_mul_sum_sq (s := idx) (f := fun i => |D i|)
  have cs' : (∑ i ∈ idx, |D i|) ^ 2 ≤ (p : ℝ)^2 * ∑ i ∈ idx, D i ^ 2 := by
    simp_rw [sq_abs] at cs
    simpa only [idx, card_product, card_range, Nat.cast_mul, pow_two] using cs
  calc
    _ ≤ ∑ i ∈ idx, ‖(D i : ℂ) * P (i.1 + p*i.2)‖ := norm_sum_le _ _
    _ = ∑ i ∈ idx, |D i| := by simp [P, phase_norm, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ Real.sqrt ((p : ℝ)^2 * ∑ i ∈ idx, D i ^ 2) := Real.le_sqrt_of_sq_le cs'
    _ = _ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg _)]
      simp only [idx, sum_product]
