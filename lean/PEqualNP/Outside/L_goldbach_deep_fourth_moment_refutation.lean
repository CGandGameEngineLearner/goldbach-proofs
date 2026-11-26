import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push

/-!
# The fourth moment outside the published Goldbach wide arcs

For prime denominators just above the cube-root cutoff, additive-character
orthogonality and the positive prime mass around frequency zero force a fourth
moment that exceeds n^(2+1/6). The final theorem negates the exact catalogue
statement at goldbach-proofs commit 998680d8a74fbfe1becc177ce656a88294a58e1e.
-/

open scoped BigOperators

namespace GBFour.Moment

/-- Fourth-power Jensen bound for a finite family of complex numbers. -/
theorem norm_sum_pow_four {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    ‖∑ a ∈ s, z a‖ ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ a ∈ s, ‖z a‖ ^ 4 := by
  calc
    ‖∑ a ∈ s, z a‖ ^ 4 ≤ (∑ a ∈ s, ‖z a‖) ^ 4 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _
    _ ≤ _ := pow_sum_le_card_mul_sum_pow (s := s) (f := fun a => ‖z a‖)
      (fun a _ => norm_nonneg _) 3

/-- Near frequency zero the real part retains at least half of the nonnegative mass. -/
theorem half_mass_le_re (n : ℕ) (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (δ : ℝ) (hδ : 0 ≤ δ) (hsmall : 32 * (n : ℝ) * δ ≤ 1) :
    (∑ k ∈ Finset.range (n + 1), w k) / 2 ≤
    (∑ k ∈ Finset.range (n + 1), (w k : ℂ) *
      Complex.exp (((2 * Real.pi * ((k : ℝ) * δ) : ℝ) : ℂ) * Complex.I)).re := by
  rw [Complex.re_sum, Finset.sum_div]
  apply Finset.sum_le_sum
  intro k hk
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hmul := mul_le_mul_of_nonneg_right hkn hδ
  have hbound : 2 * ((k : ℝ) * δ) ≤ 1 / 3 := by
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ n) hδ]
  have hangle : 2 * Real.pi * ((k : ℝ) * δ) ≤ Real.pi / 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hbound Real.pi_pos.le]
  have hcos : (1 : ℝ) / 2 ≤ Real.cos (2 * Real.pi * ((k : ℝ) * δ)) := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos]) hangle
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.exp_ofReal_mul_I_re]
  nlinarith [mul_le_mul_of_nonneg_left hcos (hw k)]

/-- Common one-sided neighbourhood used for the disjoint rational intervals. -/
theorem half_mass_le_re_on_interval (n : ℕ) (hn : 0 < n) (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (δ : ℝ) (hδ : 0 ≤ δ) (hsmall : δ ≤ 1 / (100 * (n : ℝ))) :
    (∑ k ∈ Finset.range (n + 1), w k) / 2 ≤
    (∑ k ∈ Finset.range (n + 1), (w k : ℂ) *
      Complex.exp (((2 * Real.pi * ((k : ℝ) * δ) : ℝ) : ℂ) * Complex.I)).re := by
  apply half_mass_le_re n w hw δ hδ
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hm := (le_div_iff₀ (by positivity : 0 < 100 * (n : ℝ))).mp hsmall
  nlinarith [mul_nonneg hn'.le hδ]

end GBFour.Moment

noncomputable section
open Finset Filter Topology

namespace GoldbachFourth

def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
def primeWeight (k : ℕ) : ℝ := if k.Prime then Real.log (k : ℝ) else 0
def S (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n+1), (primeWeight k : ℂ) * phase ((k : ℝ)*t)

theorem primeWeight_nonneg (k : ℕ) : 0 ≤ primeWeight k := by
  unfold primeWeight
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_le)
  · exact le_rfl

theorem mass_eq_theta (n : ℕ) :
    ∑ k ∈ Finset.range (n+1), primeWeight k = Chebyshev.theta n := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, Finset.sum_filter]
  rw [Nat.range_succ_eq_Icc_zero] <;> rfl

theorem phase_add (x y : ℝ) : phase (x+y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_grid (k a q : ℕ) :
    phase ((k : ℝ) * ((a : ℝ)/q)) =
      Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ)/q)) ^ a := by
  unfold phase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem prime_orthogonality {k q : ℕ} (hk : k.Prime) (hq : q.Prime) :
    (∑ a ∈ Finset.range q, phase ((k : ℝ) * ((a : ℝ)/q))) =
      (if q = k then (q : ℂ) else 0) := by
  simp only [phase_grid]
  by_cases h : q = k
  · subst k
    have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
    simp [hqc, Complex.exp_two_pi_mul_I]
  · have hcop : k.Coprime q := (hq.coprime_iff_not_dvd.mpr
        (fun hd => h ((Nat.prime_dvd_prime_iff_eq hq hk).mp hd))).symm
    rw [if_neg h]
    exact (Complex.isPrimitiveRoot_exp_of_coprime k q hq.ne_zero hcop).geom_sum_eq_zero hq.one_lt

theorem full_prime_orbit (n q : ℕ) (hq : q.Prime) (hqn : q ≤ n) (δ : ℝ) :
    (∑ a ∈ Finset.range q, S n ((a : ℝ) / q + δ)) =
      (q : ℂ) * (Real.log (q : ℝ) : ℂ) * phase ((q : ℝ)*δ) := by
  unfold S
  rw [Finset.sum_comm]
  calc
    _ = ∑ k ∈ Finset.range (n+1), (if q = k then
        (q : ℂ) * (Real.log (q : ℝ) : ℂ) * phase ((q : ℝ)*δ) else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k.Prime
      · simp_rw [mul_add, phase_add]
        calc
          _ = ((primeWeight k : ℂ) * phase ((k : ℝ)*δ)) *
              ∑ a ∈ Finset.range q, phase ((k : ℝ)*((a : ℝ)/q)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (by intros; ring)
          _ = _ := by
            rw [prime_orthogonality hk hq]
            by_cases h : q=k
            · subst k; simp [primeWeight, hq] <;> ring
            · simp [h]
      · have hne : q ≠ k := by rintro rfl; exact hk hq
        simp [primeWeight, hk, hne]
    _ = _ := by simp [Nat.lt_succ_iff.mpr hqn]

theorem prime_orbit (n q : ℕ) (hq : q.Prime) (hqn : q ≤ n) (δ : ℝ) :
    (∑ a ∈ Finset.Ioc 0 (q-1), S n ((a : ℝ) / q + δ)) =
      (q : ℂ) * (Real.log (q : ℝ) : ℂ) * phase ((q : ℝ)*δ) - S n δ := by
  have h := full_prime_orbit n q hq hqn δ
  rw [Nat.range_eq_Icc_zero_sub_one q hq.ne_zero,
      ← Finset.add_sum_Ioc_eq_sum_Icc (by omega : 0 ≤ q-1)] at h
  simp only [Nat.cast_zero, zero_div, zero_add] at h
  linear_combination h

theorem norm_phase (t : ℝ) : ‖phase t‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

theorem prime_norm_sum_lower (n q : ℕ) (hq : q.Prime) (hqn : q ≤ n) (δ : ℝ)
    (hshift : Chebyshev.theta n / 2 ≤ (S n δ).re) :
    Chebyshev.theta n / 2 - (q : ℝ) * Real.log q ≤
      ‖∑ a ∈ Finset.Ioc 0 (q-1), S n ((a : ℝ) / q + δ)‖ := by
  rw [prime_orbit n q hq hqn δ]
  let z := (q : ℂ) * (Real.log (q : ℝ) : ℂ) * phase ((q : ℝ)*δ)
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq.one_le)
  have hz : ‖z‖ = (q : ℝ) * Real.log q := by
    simp only [z, norm_mul, Complex.norm_natCast, Complex.norm_real,
      Real.norm_of_nonneg hlog, norm_phase, mul_one]
  have tri : ‖S n δ‖ ≤ ‖z‖ + ‖z - S n δ‖ := by
    simpa [sub_sub_cancel] using norm_sub_le z (z - S n δ)
  have hreal := Complex.re_le_norm (S n δ)
  change _ ≤ ‖z - S n δ‖
  linarith


theorem prime_orbit_fourth (n q : ℕ) (hq : q.Prime) (hqn : q ≤ n) (δ : ℝ)
    (hδ : 0 ≤ δ) (hsmall : δ ≤ 1 / (100 * (n : ℝ)))
    (hθ : (n : ℝ) / 4 ≤ Chebyshev.theta n)
    (hcost : (q : ℝ) * Real.log q ≤ (n : ℝ) / 16) :
    (n : ℝ)^4 / (65536 * (q : ℝ)^3) ≤
      ∑ a ∈ Finset.Ioc 0 (q-1), ‖S n ((a : ℝ) / q + δ)‖^4 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hn : 0 < n := lt_of_lt_of_le hq.pos hqn
  have hshift := GBFour.Moment.half_mass_le_re_on_interval n hn primeWeight
    primeWeight_nonneg δ hδ hsmall
  rw [mass_eq_theta] at hshift
  change Chebyshev.theta n / 2 ≤ (S n δ).re at hshift
  have hlow := prime_norm_sum_lower n q hq hqn δ hshift
  let a := Finset.Ioc 0 (q-1)
  let z := fun m : ℕ => S n ((m : ℝ)/q + δ)
  have hlow' : (n : ℝ)/16 ≤ ‖∑ m ∈ a, z m‖ := by
    dsimp [a,z]
    linarith
  have h4 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ)/16) hlow' 4
  have hj := GBFour.Moment.norm_sum_pow_four a z
  have hcard : (a.card : ℝ) ≤ q := by
    exact_mod_cast (show a.card ≤ q by simp [a])
  have hnns : 0 ≤ ∑ m ∈ a, ‖z m‖^4 := by positivity
  have hc := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Nat.cast_nonneg a.card) hcard 3) hnns
  change (n : ℝ)^4 / (65536 * (q : ℝ)^3) ≤ ∑ m ∈ a, ‖z m‖^4
  rw [div_le_iff₀ (by positivity)]
  nlinarith only [h4.trans (hj.trans hc)]


end GoldbachFourth

namespace FareyFourth

noncomputable section

def wide (n B H : ℕ) : Set ℝ := {t | ∃ m b : ℕ, 1 ≤ m ∧ m ≤ B ∧ b ≤ m ∧
  Nat.Coprime b m ∧ |t - (b : ℝ) / m| ≤ (H : ℝ) / ((m : ℝ) * n)}

def radius (n : ℕ) : ℝ := 1 / (32 * (n : ℝ))

def arc (n q a : ℕ) : Set ℝ :=
  Set.Icc ((a : ℝ) / q - radius n) ((a : ℝ) / q + radius n)

theorem mem_arc {n q a : ℕ} {t : ℝ} :
    t ∈ arc n q a ↔ |t - (a : ℝ) / q| ≤ radius n := by
  change _ ∧ _ ↔ _
  rw [abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Separation by a nonzero integer determinant, as in goldbach-proofs PR #2468
(CornerFour.centerSep, Apache-2.0). -/
theorem centerSep {a b q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (h : a*r ≠ b*q) : 1/((q:ℝ)*r) ≤ |(a:ℝ)/q-b/r| := by
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
  rw [show (a:ℝ)/q-b/r = (a*r-b*q)/(q*r) by field_simp, abs_div,
    abs_of_pos (mul_pos hq' hr')]
  apply (div_le_div_iff_of_pos_right (mul_pos hq' hr')).mpr
  rcases lt_or_gt_of_ne h with hab | hba
  · have hgap : (a:ℝ)*r+1 ≤ b*q := by exact_mod_cast Nat.succ_le_of_lt hab
    linarith [neg_le_abs ((a:ℝ)*r-b*q)]
  · have hgap : (b:ℝ)*q+1 ≤ a*r := by exact_mod_cast Nat.succ_le_of_lt hba
    linarith [le_abs_self ((a:ℝ)*r-b*q)]

theorem arc_subset_deep {n B H q a : ℕ} (hn : 0 < n) (hq : B < q)
    (ha : a.Coprime q) (hsize : q*(B + 32*H) < 32*n) :
    arc n q a ⊆ (wide n B H)ᶜ := by
  intro t ht hwide
  obtain ⟨m,b,hm,hmB,_,_,hbt⟩ := hwide
  have hq0 : 0 < q := Nat.zero_lt_of_lt hq
  have hdet : a * m ≠ b * q := by
    intro heq
    have hd : q ∣ a * m := heq ▸ Nat.dvd_mul_left q b
    have hqm := Nat.le_of_dvd hm (ha.symm.dvd_of_dvd_mul_left hd)
    omega
  have hsep := centerSep hq0 hm hdet
  have hdist := abs_sub_le ((a : ℝ)/q) t ((b : ℝ)/m)
  rw [abs_sub_comm ((a : ℝ)/q) t] at hdist
  have h := hsep.trans (hdist.trans (add_le_add (mem_arc.mp ht) hbt))
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq0
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hsize' : (q : ℝ)*(m + 32*H) < 32*n := by
    exact_mod_cast lt_of_le_of_lt (Nat.mul_le_mul_left q (Nat.add_le_add_right hmB _)) hsize
  unfold radius at h
  field_simp at h
  nlinarith

theorem prime_arc_subset_deep {n B H q a : ℕ} (hn : 0 < n) (hlarge : B < q)
    (hq : q.Prime) (ha : 0 < a) (haq : a < q) (hsize : q*(B + 32*H) < 32*n) :
    arc n q a ⊆ (wide n B H)ᶜ :=
  arc_subset_deep hn hlarge ((hq.coprime_iff_not_dvd.mpr
    (fun hd => (Nat.le_of_dvd ha hd).not_gt haq)).symm) hsize

theorem arc_disjoint_of_det {n q r a b : ℕ} (hn : 0 < n) (hq : 0 < q) (hr : 0 < r)
    (hdet : a*r ≠ b*q) (hsize : q*r < 16*n) :
    Disjoint (arc n q a) (arc n r b) := by
  rw [Set.disjoint_left]
  intro t ht hu
  have hs := centerSep hq hr hdet
  have hd := abs_sub_le ((a : ℝ)/q) t ((b : ℝ)/r)
  rw [abs_sub_comm ((a : ℝ)/q) t] at hd
  have h := hs.trans (hd.trans (add_le_add (mem_arc.mp ht) (mem_arc.mp hu)))
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  have hs' : (q : ℝ)*r < 16*n := by exact_mod_cast hsize
  unfold radius at h
  field_simp at h
  nlinarith

theorem distinct_det {q r a b : ℕ} (hq : 0 < q) (ha : a.Coprime q)
    (hb : b.Coprime r) (hne : (q,a) ≠ (r,b)) : a*r ≠ b*q := by
  intro heq
  have h₁ : q ∣ a*r := heq ▸ Nat.dvd_mul_left q b
  have h₂ : r ∣ b*q := heq.symm ▸ Nat.dvd_mul_left r a
  have hqr := Nat.dvd_antisymm (ha.symm.dvd_of_dvd_mul_left h₁) (hb.symm.dvd_of_dvd_mul_left h₂)
  subst r
  have hab := Nat.eq_of_mul_eq_mul_right hq heq
  exact hne (by rw [hab])

theorem arc_disjoint {n q r a b : ℕ} (hn : 0 < n) (hq : 0 < q) (hr : 0 < r)
    (ha : a.Coprime q) (hb : b.Coprime r) (hne : (q,a) ≠ (r,b))
    (hsize : q*r < 16*n) : Disjoint (arc n q a) (arc n r b) := by
  exact arc_disjoint_of_det hn hq hr (distinct_det hq ha hb hne) hsize

theorem arc_subset_unit {n q a : ℕ} (hn : 0 < n) (ha : 0 < a) (haq : a < q)
    (hsize : q < 32*n) : arc n q a ⊆ Set.Ioo 0 1 := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast ha.trans haq
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : (q : ℝ) < 32*n := by exact_mod_cast hsize
  have hr : radius n < 1 / (q : ℝ) := by
    unfold radius
    exact one_div_lt_one_div_of_lt hq hs
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have haq' : (a : ℝ) + 1 ≤ q := by exact_mod_cast Nat.succ_le_of_lt haq
  have hl := div_le_div_of_nonneg_right ha' hq.le
  have hu : (a : ℝ)/q + 1/q ≤ 1 := by rw [← add_div, div_le_one hq]; exact haq'
  intro t ht
  change _ ∧ _ at ht ⊢
  constructor <;> linarith [ht.1, ht.2]

theorem prime_center_separated {n M q r a b : ℕ} (hn : 0 < n) (hq : q.Prime) (hr : r.Prime)
    (ha : 0 < a) (haq : a < q) (hb : 0 < b) (hbr : b < r) (hqM : q ≤ M) (hrM : r ≤ M)
    (hM : M^2 ≤ n) (hne : q ≠ r ∨ a ≠ b) :
    radius n ≤ |(a : ℝ) / q - b / r| := by
  have cp {x p : ℕ} (hp : p.Prime) (hx : 0 < x) (hxp : x < p) : x.Coprime p :=
    (hp.coprime_iff_not_dvd.mpr (fun h => (Nat.le_of_dvd hx h).not_gt hxp)).symm
  have hpair : (q,a) ≠ (r,b) := by
    intro h
    rcases Prod.mk.inj h with ⟨rfl,rfl⟩
    simp at hne
  have hsep := centerSep hq.pos hr.pos (distinct_det hq.pos (cp hq ha haq) (cp hr hb hbr) hpair)
  apply le_trans _ hsep
  have hprod : q*r ≤ n := (Nat.mul_le_mul hqM hrM).trans (by simpa [pow_two] using hM)
  have hprod' : (q : ℝ)*r ≤ n := by exact_mod_cast hprod
  apply one_div_le_one_div_of_le (mul_pos (by exact_mod_cast hq.pos) (by exact_mod_cast hr.pos))
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem prime_shift_in_deep {n B H M q a : ℕ} (hn : 0 < n) (hq : q.Prime)
    (hB : B < q) (hqM : q ≤ M) (ha : 0 < a) (haq : a < q)
    (hbgt : 2*M*(H+1) ≤ n) (hM : M^2 ≤ n) {δ : ℝ}
    (hδ : δ ∈ Set.Ioc 0 (radius n)) :
    (a : ℝ)/q + δ ∈ Set.Ioc (0:ℝ) 1 ∩ (wide n B H)ᶜ := by
  have qB : q*B ≤ n := (Nat.mul_le_mul hqM (hB.le.trans hqM)).trans (by simpa [pow_two] using hM)
  have qH : q*H ≤ M*H := Nat.mul_le_mul_right H hqM
  have small : q*(B+32*H) < 32*n := by nlinarith
  have small' : q < 32*n := by nlinarith
  have hmem : (a : ℝ)/q + δ ∈ arc n q a := by
    rw [mem_arc, add_sub_cancel_left, abs_of_nonneg hδ.1.le]
    exact hδ.2
  have hunit := arc_subset_unit hn ha haq small' hmem
  exact ⟨⟨hunit.1,hunit.2.le⟩, prime_arc_subset_deep hn hB hq ha haq small hmem⟩


end
end FareyFourth

open Filter
namespace FourthMomentGrowth

noncomputable def denom (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
noncomputable def radiusNumerator (n : ℕ) : ℕ := 256 * denom n * (Nat.log 2 (n + 2)) ^ 2

/- The elementary logarithm comparison follows the Apache-2.0 proof in
   goldbach-proofs #2489, which credits #2468. -/
private theorem log2_le_four_log (n : ℕ) (hn : 2 ≤ n) :
    (Nat.log 2 (n + 2) : ℝ) ≤ 4 * Real.log n := by
  have hb := Real.natLog_le_logb (n + 2) 2
  rw [Real.logb] at hb
  push_cast at hb
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hx : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have square : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith) (show 0 ≤ (n : ℝ) + 1 by positivity)]
  have logarithm := Real.log_le_log (by positivity : 0 < (n : ℝ) + 2) square
  rw [Real.log_pow] at logarithm
  norm_num at logarithm
  have divided := (le_div_iff₀ (by linarith : 0 < Real.log 2)).mp hb
  have multiplied := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (Nat.log 2 (n + 2)) : (0 : ℝ) ≤ _)
  linarith only [logarithm, divided, multiplied]

private theorem eventually_root_control (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, K ≤ (n : ℝ)^(1/48:ℝ) ∧ Real.log n ≤ (n : ℝ)^(1/48:ℝ) := by
  have hroot := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/48)).comp
     (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/48)).tendsto_div_nhds_zero.comp
     (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hroot.eventually_ge_atTop K,
      hlog.eventually_lt_const (show (0:ℝ)<1 by norm_num), eventually_ge_atTop 1] with n hn hl hn'
  refine ⟨hn,?_⟩
  change Real.log n / (n:ℝ) ^ (1/48:ℝ) < 1 at hl
  have np : (0:ℝ)<n := by exact_mod_cast hn'
  simpa only [one_mul] using ((div_lt_iff₀ (Real.rpow_pos_of_pos np _)).mp hl).le

private theorem exp_step (n k : ℕ) :
    ((n : ℝ) ^ (1/48:ℝ)) ^ k = (n : ℝ) ^ ((k:ℝ)/48) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  ring

/-- The four bounds control wide-arc separation, disjointness, the exceptional
prime term, and the logarithmic loss in prime supply, respectively. -/
theorem eventual_budgets (C : ℕ) (hC : 0 < C) (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ n : ℕ in atTop,
      2 * (C * denom n) * (radiusNumerator n + 1) ≤ n ∧
      (C * denom n) ^ 2 ≤ n ∧
      (32 : ℝ) * (C * denom n : ℕ) * Real.log (C * denom n : ℕ) ≤ (n : ℝ) ∧
      K * (n:ℝ) ^ (1/6:ℝ) * Real.log (C * denom n : ℕ) < (denom n : ℝ) := by
  have cpos : (1:ℝ) ≤ C := by exact_mod_cast hC
  filter_upwards [eventually_root_control (max (max (8194 * (C:ℝ)) (2*K+2)) 2),
      eventually_ge_atTop 2] with n h hn
  set t := (n : ℝ) ^ (1/48:ℝ)
  change _ ≤ t ∧ Real.log n ≤ t at h
  have ht : 2 ≤ t := (le_max_right _ _).trans h.1
  have hcu : 8194 * (C : ℝ) ≤ t := (le_max_left _ _).trans ((le_max_left _ _).trans h.1)
  have hku : 2*K+2 ≤ t := (le_max_right _ _).trans ((le_max_left _ _).trans h.1)
  have h1 : 1 ≤ t := by linarith
  have tpos : 0 < t := by linarith
  have castN : t^48 = (n:ℝ) := by rw [show t^48 = _ from exp_step n 48]; norm_num
  have castQ : t^16 = (n:ℝ)^(1/3:ℝ) := by rw [show t^16 = _ from exp_step n 16]; norm_num
  have castSmall : t^8 = (n:ℝ)^(1/6:ℝ) := by rw [show t^8 = _ from exp_step n 8]; norm_num
  have qU : (denom n:ℝ) ≤ t^16 := by rw [castQ]; apply Nat.floor_le; positivity
  have qL : t^16 < (denom n:ℝ) + 1 := by rw [castQ]; exact Nat.lt_floor_add_one _
  have mon : ∀ {a b:ℕ}, a ≤ b → t^a ≤ t^b := fun h => pow_le_pow_right₀ h1 h
  have t16 : (2:ℝ) ≤ t^16 := ht.trans (by simpa using (mon (by decide : 1 ≤ 16)))
  have tq : 0 < (denom n:ℝ) := by linarith only [qL,t16]
  have tQ : (↑(C * denom n) : ℝ) ≤ t^17 := by
    push_cast
    calc _ ≤ t * t^16 := by gcongr <;> linarith only [hcu,cpos]
         _ = _ := by ring
  have ctq : (0:ℝ) < ↑(C*denom n) := by push_cast; positivity
  have tLog : Real.log (C * denom n : ℕ) ≤ t :=
    (Real.log_le_log ctq ((tQ.trans (mon (by decide : 17 ≤ 48))).trans_eq castN)).trans h.2
  have hln := (log2_le_four_log n hn).trans (mul_le_mul_of_nonneg_left h.2 (by norm_num))
  have s1 : (1:ℝ) ≤ t^18 := one_le_pow₀ h1
  have cut : (radiusNumerator n : ℝ) + 1 ≤ 4097 * t^18 := by
    unfold radiusNumerator
    push_cast
    calc
      _ ≤ 256 * t^16 * (4*t)^2 + 1 := by gcongr
      _ ≤ _ := by nlinarith only [s1]
  constructor
  · have realBound : (2:ℝ) * (↑(C * denom n):ℝ) * ((radiusNumerator n:ℝ)+1) ≤ n := by
      calc
        _ ≤ 2 * t^17 * (4097 * t^18) := by gcongr
        _ = 8194 * t^35 := by ring
        _ ≤ t * t^35 := by gcongr <;> linarith only [hcu,cpos]
        _ = t^36 := by ring
        _ ≤ t^48 := mon (by decide)
        _ = _ := castN
    exact_mod_cast realBound
  constructor
  · have realBound : (↑(C * denom n):ℝ)^2 ≤ n := by
      calc _ ≤ (t^17)^2 := by gcongr
           _ = t^34 := by ring
           _ ≤ t^48 := mon (by decide)
           _ = _ := castN
    exact_mod_cast realBound
  constructor
  · calc
      _ ≤ 32 * t^17 * t := by gcongr
      _ ≤ t * t^17 * t := by gcongr <;> linarith only [hcu,cpos]
      _ = t^19 := by ring
      _ ≤ t^48 := mon (by decide)
      _ = _ := castN
  · rw [← castSmall]
    have t10 : t^10 ≤ t^16 := mon (by decide)
    have halfQ : t^16 / 2 < (denom n:ℝ) := by linarith only [qL,t16]
    calc
      _ ≤ K * t^8 * t := by gcongr
      _ ≤ (t / 2) * t^8 * t := by gcongr <;> linarith only [hku]
      _ = t^10 / 2 := by ring
      _ ≤ t^16 / 2 := by linarith only [t10]
      _ < _ := halfQ

theorem tendsto_denom : Tendsto denom atTop atTop :=
  (tendsto_nat_floor_atTop (α := ℝ)).comp
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3)).comp (tendsto_natCast_atTop_atTop (R:=ℝ)))

theorem denom_cube_le (n : ℕ) : (denom n)^3 ≤ n := by
  have h : (denom n:ℝ) ≤ (n:ℝ)^(1/3:ℝ) := Nat.floor_le (by positivity)
  have hc := pow_le_pow_left₀ (Nat.cast_nonneg _) h 3
  rw [← Real.rpow_natCast ((n:ℝ)^(1/3:ℝ)), ← Real.rpow_mul (Nat.cast_nonneg _)] at hc
  norm_num at hc
  exact_mod_cast hc

theorem band_geometry {n q r : ℕ} (hn : 0 < n)
    (hwide : 2*(16*denom n)*(radiusNumerator n+1) ≤ n)
    (hsq : (16*denom n)^2 ≤ n) (hq : q ≤ 16*denom n) (hr : r ≤ 16*denom n) :
    q*(denom n+32*radiusNumerator n) < 32*n ∧ q*r < 16*n := by
  have hpair : q*r ≤ n := by
    rw [pow_two] at hsq
    exact (Nat.mul_le_mul hq hr).trans hsq
  have hqQ : q * denom n ≤ n := by
    rw [pow_two] at hsq
    exact (Nat.mul_le_mul hq (by omega : denom n ≤ 16*denom n)).trans hsq
  have hw : 2*q*(radiusNumerator n+1) ≤ n :=
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hq)).trans hwide
  have hqH : 2*(q*radiusNumerator n) ≤ n := by
    calc
      _ ≤ 2*q*(radiusNumerator n+1) := by ring_nf; omega
      _ ≤ _ := hw
  rw [Nat.mul_add, show q*(32*radiusNumerator n) = 32*(q*radiusNumerator n) by ring]
  omega

/-- Bounds used uniformly for every prime denominator in the band. -/
theorem prime_parameter_bounds {n q : ℕ} (hq0 : 1 ≤ q) (hq : q ≤ 16*denom n)
    (hlarge : (32 : ℝ) * (16 * denom n : ℕ) * Real.log (16 * denom n : ℕ) ≤ n) :
    (q:ℝ) * Real.log q ≤ (n:ℝ)/32 ∧ (q:ℝ)^3 ≤ 4096*(n:ℝ) := by
  have qpos : (0:ℝ)<q := by exact_mod_cast hq0
  have qlarge : (q:ℝ) ≤ (↑(16 * denom n):ℝ) := by exact_mod_cast hq
  have hl := Real.log_le_log qpos qlarge
  have hqlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq0)
  have h0 : (0:ℝ) ≤ ↑(16 * denom n) := by positivity
  have hpl := mul_le_mul qlarge hl hqlog h0
  have hcube : (denom n:ℝ)^3 ≤ n := by exact_mod_cast denom_cube_le n
  have hq3 := pow_le_pow_left₀ (Nat.cast_nonneg _) qlarge 3
  push_cast at hq3
  constructor
  · nlinarith only [hlarge,hpl]
  · nlinarith only [hq3,hcube]

theorem eventual_prime_supply_budget (K : ℝ) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop, (n:ℝ)^(1/6:ℝ) < denom n / (K * Real.log (denom n)) := by
  filter_upwards [eventual_budgets 16 (by decide) K hK.le, tendsto_denom.eventually_ge_atTop 2]
    with n hb hQ
  have qpos : (0:ℝ) < denom n := by exact_mod_cast (by omega : 0 < denom n)
  have qgt : (1:ℝ) < denom n := by exact_mod_cast hQ
  have hl : 0 < Real.log (denom n) := Real.log_pos qgt
  have hl' : Real.log (denom n) ≤ Real.log (16*denom n:ℕ) :=
    Real.log_le_log qpos (by exact_mod_cast (by omega : denom n ≤ 16*denom n))
  apply (lt_div_iff₀ (mul_pos hK hl)).mpr
  calc
    _ = K * (n:ℝ)^(1/6:ℝ) * Real.log (denom n) := by ring
    _ ≤ K * (n:ℝ)^(1/6:ℝ) * Real.log (16*denom n:ℕ) := by gcongr
    _ < _ := hb.2.2.2

end FourthMomentGrowth

open Finset

namespace GoldbachFourthMoment

/-- An elementary explicit lower bound for the Chebyshev theta function. -/
theorem theta_lower (n : ℕ) (hn : 10^16 ≤ n) : (n : ℝ) / 4 ≤ Chebyshev.theta n := by
  have hx : (10 : ℝ)^16 ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) ≤ n := by positivity
  have hs0 := Real.sqrt_nonneg (n : ℝ)
  have hs2 := Real.sq_sqrt hx0
  have hu2 := Real.sq_sqrt hs0
  have hs : (10 : ℝ)^8 ≤ Real.sqrt n := by
    rw [Real.le_sqrt (by positivity) hx0]
    norm_num at hx ⊢
    exact hx
  have hu : (1600 : ℝ) ≤ Real.sqrt (Real.sqrt n) := by
    rw [Real.le_sqrt (by positivity) hs0]
    norm_num at hs ⊢
    linarith
  have hulog := Real.log_le_sub_one_of_pos (by linarith : 0 < Real.sqrt (Real.sqrt n))
  rw [Real.log_sqrt hs0, Real.log_sqrt hx0] at hulog
  have hscale := mul_le_mul_of_nonneg_right hu (Real.sqrt_nonneg (Real.sqrt n))
  have hbudget : 400 * Real.log n ≤ Real.sqrt n := by nlinarith
  have herror := Chebyshev.psi_sub_theta_le (by linarith : (1 : ℝ) ≤ n)
  have hmul := mul_le_mul_of_nonneg_left hbudget hs0
  have hl : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hmain := (mul_le_mul_of_nonneg_left hl hx0).trans
    (Chebyshev.psi_ge_of_seven_le (by omega : 7 ≤ n))
  nlinarith

/-- The sum of the weights appearing in the Goldbach exponential sum. -/
theorem primeWeight_sum_eq_theta (n : ℕ) :
    (∑ k ∈ range (n+1), if k.Prime then Real.log k else 0) = Chebyshev.theta n := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, sum_filter]
  have hr : range (n+1) = Icc 0 n := by ext k; simp
  rw [hr]

/-- A quantitative supply of prime denominators in a fixed multiplicative interval. -/
theorem prime_band_weighted (x : ℕ) (hx : 10^16 ≤ x) :
    (x : ℝ) ≤ (((Ioc x (16*x)).filter Nat.Prime).card : ℝ) * Real.log (16*(x:ℝ)) := by
  let s := (Ioc 0 x).filter Nat.Prime
  let t := (Ioc x (16*x)).filter Nat.Prime
  have hdis : Disjoint s t := by
    rw [Finset.disjoint_left]
    intro k hks hkt
    have ha := (mem_Ioc.mp (mem_filter.mp hks).1).2
    have hb := (mem_Ioc.mp (mem_filter.mp hkt).1).1
    omega
  have hun : (Ioc 0 (16*x)).filter Nat.Prime = s ∪ t := by
    ext k
    simp only [s,t,mem_union,mem_filter,mem_Ioc]
    constructor
    · rintro ⟨⟨hk, hk16⟩, hprime⟩
      by_cases hv : k ≤ x
      · exact Or.inl ⟨⟨hk, hv⟩, hprime⟩
      · exact Or.inr ⟨⟨by omega, hk16⟩, hprime⟩
    · rintro (⟨⟨hk, hkx⟩, hprime⟩ | ⟨⟨hxk, hk⟩, hprime⟩)
      · exact ⟨⟨hk, by omega⟩, hprime⟩
      · exact ⟨⟨by omega, hk⟩, hprime⟩
  have heq : Chebyshev.theta (16*x : ℕ) = Chebyshev.theta x + ∑ p ∈ t, Real.log p := by
    simp only [Chebyshev.theta, Nat.floor_natCast]
    rw [hun, sum_union hdis]
  have hlo := theta_lower (16*x) (by omega)
  have hhi := Chebyshev.theta_le_log4_mul_x (by positivity : (0 : ℝ) ≤ x)
  have hlog4 := Real.log_le_sub_one_of_pos (by norm_num : 0 < (4 : ℝ))
  have hx0 : (0:ℝ) ≤ x := by positivity
  have hhi' : Chebyshev.theta x ≤ 3*x := by
    refine hhi.trans (mul_le_mul_of_nonneg_right ?_ hx0)
    linarith
  rw [heq] at hlo
  push_cast at hlo
  have hsum : (x : ℝ) ≤ ∑ p ∈ t, Real.log p := by linarith
  have hsum' : (∑ p ∈ t, Real.log p) ≤ t.card * Real.log (16*(x:ℝ)) := by
    calc
      _ ≤ ∑ _p ∈ t, Real.log (16*(x:ℝ)) := by
        apply sum_le_sum
        intro p hp
        have hp' := mem_filter.mp hp
        apply Real.log_le_log (by exact_mod_cast hp'.2.pos)
        exact_mod_cast (mem_Ioc.mp hp'.1).2
      _ = _ := by simp
  exact hsum.trans hsum'

theorem prime_band_count (x : ℕ) (hx : 10^16 ≤ x) :
    (x : ℝ) / (2 * Real.log x) ≤ (((Ioc x (16*x)).filter Nat.Prime).card : ℝ) := by
  have hx16 : (16 : ℝ) ≤ x := by exact_mod_cast (by omega : 16 ≤ x)
  have hlogprod : Real.log (16*(x:ℝ)) ≤ 2 * Real.log x := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    linarith [Real.log_le_log (by norm_num : (0:ℝ) < 16) hx16]
  apply (div_le_iff₀ (mul_pos (by norm_num) (Real.log_pos (by linarith)))).2
  exact (prime_band_weighted x hx).trans (mul_le_mul_of_nonneg_left hlogprod (by positivity))

/-- A convenient polynomial lower bound for the same prime count. -/
theorem prime_band_count_sqrt (x : ℕ) (hx : 10^16 ≤ x) :
    Real.sqrt x / 4 ≤ (((Ioc x (16*x)).filter Nat.Prime).card : ℝ) := by
  have hp : (1:ℝ) < x := by exact_mod_cast (by omega : 1 < x)
  have hnonneg : (0:ℝ) ≤ x := by positivity
  have hs := Real.sqrt_nonneg (x : ℝ)
  have hsq := Real.sq_sqrt hnonneg
  have hl := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (by linarith : 0 < (x:ℝ)))
  rw [Real.log_sqrt hnonneg] at hl
  have hlog : Real.log x ≤ 2 * Real.sqrt x := by linarith
  apply le_trans _ (prime_band_count x hx)
  apply (le_div_iff₀ (mul_pos (by norm_num) (Real.log_pos hp))).2
  nlinarith [mul_le_mul_of_nonneg_left hlog hs]

end GoldbachFourthMoment

/-! Integrate a common translate parameter over disjoint windows in a measurable set. -/
open MeasureTheory Set

namespace GoldbachFourier

theorem integrate_windows {ι : Type*} (T : Finset ι) (z : ι → ℝ)
    {F : ℝ → ℝ} (hF : Continuous F) (hpos : ∀ t, 0 ≤ F t)
    {D : Set ℝ} (hD : MeasurableSet D) {w M : ℝ} (hw : 0 ≤ w)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → w ≤ |z i - z j|)
    (hwin : ∀ i ∈ T, ∀ δ ∈ Ioc (0:ℝ) w, z i + δ ∈ Ioc (0:ℝ) 1 ∩ D)
    (hM : ∀ δ ∈ Icc (0:ℝ) w, M ≤ ∑ i ∈ T, F (z i + δ)) :
    w * M ≤ ∫ t in (0:ℝ)..1, D.indicator F t := by
  classical
  let J (i : ι) := Ioc (z i) (z i+w)
  have hmJ (i : ι) : MeasurableSet (J i) := measurableSet_Ioc
  have hpair : (T : Set ι).Pairwise (fun i j => Disjoint (J i) (J j)) := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hsep' := hsep i hi j hj hij
    rcases le_abs.mp hsep' with he | he
    · change z i < x ∧ x ≤ z i+w at hx
      change z j < x ∧ x ≤ z j+w at hy
      linarith [hx.1, hy.2]
    · change z i < x ∧ x ≤ z i+w at hx
      change z j < x ∧ x ≤ z j+w at hy
      linarith [hy.1, hx.2]
  have hU : (⋃ i ∈ T, J i) ⊆ Ioc (0:ℝ) 1 ∩ D := by
    intro x hx
    obtain ⟨i, hi, (hx : z i < x ∧ x ≤ z i+w)⟩ := Set.mem_iUnion₂.mp hx
    simpa only [add_sub_cancel] using
      hwin i hi (x - z i) ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hshift (i : ι) : (∫ t in (0:ℝ)..w, F (z i+t)) = ∫ x in J i, F x := by
    rw [intervalIntegral.integral_comp_add_left]
    simpa only [add_zero] using
      (intervalIntegral.integral_of_le (μ := volume) (f := F)
        (show z i + 0 ≤ z i + w by linarith))
  have hfamily (i : ι) : Continuous (fun t => F (z i+t)) :=
    hF.comp (continuous_const.add continuous_id)
  calc
    w * M = ∫ _t in (0:ℝ)..w, M := by
      simp [intervalIntegral.integral_const]
    _ ≤ ∫ δ in (0:ℝ)..w, ∑ i ∈ T, F (z i+δ) :=
      intervalIntegral.integral_mono_on hw intervalIntegrable_const
        ((continuous_finsetSum T (fun i _ => hfamily i)).intervalIntegrable ..) hM
    _ = ∑ i ∈ T, ∫ x in J i, F x := by
      rw [intervalIntegral.integral_finsetSum (fun i _ => (hfamily i).intervalIntegrable ..)]
      exact Finset.sum_congr rfl fun i _ => hshift i
    _ = ∫ x in ⋃ i ∈ T, J i, F x :=
      (MeasureTheory.integral_biUnion_finset T (fun i _ => hmJ i) hpair
        (fun i _ => hF.integrableOn_Ioc)).symm
    _ ≤ ∫ x in Ioc (0:ℝ) 1 ∩ D, F x :=
      MeasureTheory.setIntegral_mono_set
        (hF.integrableOn_Ioc.mono_set inter_subset_left)
        (Filter.Eventually.of_forall hpos) hU.eventuallySubset
    _ = ∫ t in (0:ℝ)..1, D.indicator F t := by
      rw [intervalIntegral.integral_of_le (by norm_num), MeasureTheory.setIntegral_indicator hD]

/-- Group windows by modulus, and then by numerator within each modulus. -/
theorem integrate_orbits (Q : Finset ℕ) (A : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ)
    {F : ℝ → ℝ} (hF : Continuous F) (hpos : ∀ t, 0 ≤ F t)
    {D : Set ℝ} (hD : MeasurableSet D) {w : ℝ} (hw : 0 ≤ w) (M : ℕ → ℝ)
    (hsep : ∀ q ∈ Q, ∀ a ∈ A q, ∀ r ∈ Q, ∀ b ∈ A r,
      q ≠ r ∨ a ≠ b → w ≤ |c q a - c r b|)
    (hwin : ∀ q ∈ Q, ∀ a ∈ A q, ∀ δ ∈ Ioc (0:ℝ) w,
      c q a + δ ∈ Ioc (0:ℝ) 1 ∩ D)
    (hM : ∀ q ∈ Q, ∀ δ ∈ Icc (0:ℝ) w, M q ≤ ∑ a ∈ A q, F (c q a+δ)) :
    w * ∑ q ∈ Q, M q ≤ ∫ t in (0:ℝ)..1, D.indicator F t := by
  apply integrate_windows (Q.sigma A) (fun i => c i.1 i.2) hF hpos hD hw
  · rintro ⟨q,a⟩ hqa ⟨r,b⟩ hrb hne
    obtain ⟨hq,ha⟩ := Finset.mem_sigma.mp hqa
    obtain ⟨hr,hb⟩ := Finset.mem_sigma.mp hrb
    apply hsep q hq a ha r hr b hb
    by_cases hqr : q = r
    · right
      rintro rfl
      exact hne (by cases hqr; rfl)
    · exact Or.inl hqr
  · rintro ⟨q,a⟩ hqa δ hδ
    obtain ⟨hq,ha⟩ := Finset.mem_sigma.mp hqa
    exact hwin q hq a ha δ hδ
  · intro δ hδ
    rw [Finset.sum_sigma]
    exact Finset.sum_le_sum fun q hq => hM q hq δ hδ

end GoldbachFourier

namespace GoldbachFourthBounds

theorem uniform_orbit_lower (n q B : ℕ) (hn : 0 < n) (hq : 0 < q) (hqB : q ≤ 16*B)
    (hc : B^3 ≤ n) :
    (n:ℝ)^3 / 268435456 ≤ (n:ℝ)^4 / (65536 * (q:ℝ)^3) := by
  have hq' : (q:ℝ) ≤ 16*(B:ℝ) := by exact_mod_cast hqB
  have hc' : (B:ℝ)^3 ≤ n := by exact_mod_cast hc
  have hqpow : (q:ℝ)^3 ≤ (16*(B:ℝ))^3 := by gcongr
  have hbound : (q:ℝ)^3 ≤ 4096*(n:ℝ) := by linarith
  have qpos : (0:ℝ) < q := by exact_mod_cast hq
  apply (le_div_iff₀ (by positivity)).mpr
  have h := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ (n:ℝ)^3)
  linarith only [h]

theorem scaled_area (n : ℕ) (hn : 0 < n) (k : ℝ) :
    (1 / (100*(n:ℝ))) * (k * ((n:ℝ)^3 / 268435456)) =
       k * (n:ℝ)^2 / 26843545600 := by
  have h : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  <;> ring

theorem violates_bound (n : ℕ) (hn : 0 < n) (k : ℝ)
    (hk : 26843545600 * (n:ℝ)^(1/6:ℝ) < k) :
    (n:ℝ)^(2+(1/6:ℝ)) < k * (n:ℝ)^2 / 26843545600 := by
  have h : (0:ℝ)<n := by exact_mod_cast hn
  rw [Real.rpow_add h]
  norm_num
  have hh := mul_lt_mul_of_pos_right hk (by positivity : 0 < (n:ℝ)^2)
  linarith only [hh]

end GoldbachFourthBounds

namespace GoldbachFourthCertificate
open MeasureTheory Finset Filter
open FourthMomentGrowth

noncomputable section

def band (B : ℕ) := (Finset.Ioc B (16*B)).filter Nat.Prime
def nums (q : ℕ) := Finset.Ioc 0 (q-1)
def center (q a : ℕ) : ℝ := (a:ℝ)/q
def width (n : ℕ) : ℝ := 1/(100*(n:ℝ))
def D (n : ℕ) := (FareyFourth.wide n (denom n) (radiusNumerator n))ᶜ
def moment (n : ℕ) : ℝ :=
  intervalIntegral (fun t => (D n).indicator (fun u => ‖GoldbachFourth.S n u‖^4) t) 0 1 volume

theorem width_le_radius (n : ℕ) (hn : 0 < n) : width n ≤ FareyFourth.radius n := by
  have h : (0:ℝ) < n := by exact_mod_cast hn
  unfold width FareyFourth.radius
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem numerator_info {q a : ℕ} (hq : q.Prime) (ha : a ∈ nums q) :
    0 < a ∧ a < q ∧ a.Coprime q := by
  obtain ⟨hp, hu⟩ := Finset.mem_Ioc.mp ha
  have hq0 := hq.pos
  have haq : a < q := by omega
  exact ⟨hp,haq,(hq.coprime_iff_not_dvd.mpr (fun h => (Nat.le_of_dvd hp h).not_gt haq)).symm⟩

theorem orbit_separation {n B : ℕ} (hn : 0 < n) (hsize : (16*B)^2 ≤ n)
    (q : ℕ) (hq : q ∈ band B) (a : ℕ) (ha : a ∈ nums q)
    (r : ℕ) (hr : r ∈ band B) (b : ℕ) (hb : b ∈ nums r)
    (hne : q ≠ r ∨ a ≠ b) :
    width n ≤ |center q a - center r b| := by
  obtain ⟨hqI,hqp⟩ := Finset.mem_filter.mp hq
  obtain ⟨hrI,hrp⟩ := Finset.mem_filter.mp hr
  have hqr : q*r < 16*n := by
    have hu := Nat.mul_le_mul (Finset.mem_Ioc.mp hqI).2 (Finset.mem_Ioc.mp hrI).2
    rw [← sq] at hu
    omega
  have hd := FareyFourth.arc_disjoint hn hqp.pos hrp.pos
    (numerator_info hqp ha).2.2 (numerator_info hrp hb).2.2
    (show (q,a) ≠ (r,b) by intro e; simp_all) hqr
  by_contra! h
  have h1 : center r b ∈ FareyFourth.arc n q a := by
    apply FareyFourth.mem_arc.mpr
    change |center r b - center q a| ≤ _
    rw [abs_sub_comm]
    exact h.le.trans (width_le_radius n hn)
  have h2 : center r b ∈ FareyFourth.arc n r b := by
    apply FareyFourth.mem_arc.mpr
    simp [center,FareyFourth.radius]
  exact (Set.disjoint_left.mp hd) h1 h2

theorem orbit_window {n : ℕ} (hn : 0 < n)
    (hs : ∀ q ≤ 16*denom n, q*(denom n + 32*radiusNumerator n) < 32*n)
    (hsq : (16*denom n)^2 ≤ n)
    (q : ℕ) (hq : q ∈ band (denom n)) (a : ℕ) (ha : a ∈ nums q)
    (δ : ℝ) (hδ : δ ∈ Set.Ioc 0 (width n)) :
    center q a + δ ∈ Set.Ioc 0 1 ∩ D n := by
  obtain ⟨hi,hp⟩ := Finset.mem_filter.mp hq
  obtain ⟨hlo,hhi⟩ := Finset.mem_Ioc.mp hi
  obtain ⟨hapos,haq,_⟩ := numerator_info hp ha
  have small : q < 32*n := by
    have h := (Nat.le_self_pow (by decide : 2 ≠ 0) (16*denom n)).trans hsq
    omega
  have harc : center q a + δ ∈ FareyFourth.arc n q a := by
    apply FareyFourth.mem_arc.mpr
    change |center q a + δ - center q a| ≤ _
    simpa only [add_sub_cancel_left, abs_of_pos hδ.1] using hδ.2.trans (width_le_radius n hn)
  have unit := FareyFourth.arc_subset_unit hn hapos haq small harc
  exact ⟨⟨unit.1,unit.2.le⟩,FareyFourth.prime_arc_subset_deep hn hlo hp hapos haq (hs q hhi) harc⟩

theorem measurable_D (n : ℕ) : MeasurableSet (D n) := by
  apply MeasurableSet.compl
  unfold FareyFourth.wide
  simp only [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  by_cases hb : 1 ≤ q ∧ q ≤ denom n ∧ a ≤ q ∧ a.Coprime q
  · obtain ⟨h1,h2,h3,h4⟩ := hb
    simp only [h1,h2,h3,true_and]
    have he : {t : ℝ | a.Coprime q ∧ |t-(a:ℝ)/q| ≤ (radiusNumerator n:ℝ)/((q:ℝ)*n)} =
        {t : ℝ | |t-(a:ℝ)/q| ≤ (radiusNumerator n:ℝ)/((q:ℝ)*n)} := by
      ext t
      exact ⟨And.right, And.intro h4⟩
    rw [he]
    exact measurableSet_le (f := fun t : ℝ => |t - (a:ℝ)/q|)
      (g := fun _ : ℝ => (radiusNumerator n:ℝ) / ((q:ℝ)*n)) (by fun_prop) measurable_const
  · convert MeasurableSet.empty (α := ℝ) using 1
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    tauto

theorem nonnegative_moment_density (n : ℕ) : Continuous (fun t => ‖GoldbachFourth.S n t‖ ^ 4) := by
  unfold GoldbachFourth.S GoldbachFourth.phase
  fun_prop

/-- Each prime denominator contributes at least n²/26843545600 to the deep fourth moment. -/
theorem band_moment (n : ℕ) (hn : 10^16 ≤ n)
    (hw : 2*(16*denom n)*(radiusNumerator n+1) ≤ n)
    (hsq : (16*denom n)^2 ≤ n)
    (hlog : 32*(16*denom n:ℕ)*Real.log (16*denom n:ℕ) ≤ (n:ℝ)) :
    ((band (denom n)).card:ℝ) * (n:ℝ)^2 / 26843545600 ≤ moment n := by
  classical
  have hn' : 0 < n := by omega
  have qmax : 16*denom n ≤ n :=
    (Nat.le_self_pow (by decide : 2 ≠ 0) _).trans hsq
  have h0 : 0 ≤ width n := by unfold width; positivity
  have h := GoldbachFourier.integrate_orbits (band (denom n)) nums center
    (nonnegative_moment_density n) (fun _ => by positivity)
    (measurable_D n) h0 (fun _ => (n:ℝ)^3 / 268435456)
    (orbit_separation hn' hsq)
    (orbit_window hn' (fun q hq => (band_geometry hn' hw hsq hq hq).1) hsq) ?_
  · change _ ≤ moment n at h
    simp only [Finset.sum_const, nsmul_eq_mul] at h
    unfold width at h
    rw [GoldbachFourthBounds.scaled_area n hn'] at h
    exact h
  · intro q hq δ hδ
    obtain ⟨hi,hp⟩ := Finset.mem_filter.mp hq
    have hqu := (Finset.mem_Ioc.mp hi).2
    have hupper : (q:ℝ) ≤ (↑(16*denom n):ℝ) := by exact_mod_cast hqu
    have hlog' := Real.log_le_log (show (0:ℝ)<q by exact_mod_cast hp.pos) hupper
    have hprod : (q:ℝ)*Real.log q ≤ (↑(16*denom n):ℝ)*Real.log (16*denom n:ℕ) :=
      mul_le_mul hupper hlog' (Real.log_nonneg (by exact_mod_cast hp.one_le)) (by positivity)
    apply (GoldbachFourthBounds.uniform_orbit_lower n q (denom n) hn' hp.pos hqu (denom_cube_le n)).trans
    exact GoldbachFourth.prime_orbit_fourth n q hp (hqu.trans qmax) δ hδ.1 hδ.2
      (GoldbachFourthMoment.theta_lower n hn) (by linarith only [hprod,hlog])

theorem large_moment :
    ∀ᶠ n : ℕ in atTop, (n:ℝ)^(2+1/6:ℝ) < moment n := by
  filter_upwards [eventual_budgets 16 (by decide) 53687091200 (by norm_num),
    tendsto_denom.eventually_ge_atTop (10^16), eventually_ge_atTop (10^16:ℕ)] with n h hB hn
  obtain ⟨hw,hsq,hlog,hgrowth⟩ := h
  have hn0 : 0 < n := by omega
  have supply := GoldbachFourthMoment.prime_band_count (denom n) hB
  change (denom n:ℝ) / (2*Real.log (denom n)) ≤ ((band (denom n)).card:ℝ) at supply
  have B1 : (1:ℝ) < denom n := by exact_mod_cast (by omega : 1 < denom n)
  have lp := Real.log_pos B1
  have ll : Real.log (denom n:ℝ) ≤ Real.log (16*denom n:ℕ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast (by omega : denom n ≤ 16*denom n))
  have lsmall := mul_le_mul_of_nonneg_left ll (by positivity : 0 ≤ 53687091200 * (n:ℝ)^(1/6:ℝ))
  have count : 26843545600 * (n:ℝ)^(1/6:ℝ) < ((band (denom n)).card:ℝ) := by
    apply lt_of_lt_of_le _ supply
    apply (lt_div_iff₀ (by positivity)).mpr
    linarith only [lt_of_le_of_lt lsmall hgrowth]
  exact (GoldbachFourthBounds.violates_bound n hn0 _ count).trans_le (band_moment n hn hw hsq hlog)
end
end GoldbachFourthCertificate

namespace PEqualNP.Outside

/-- The exact negation of the frozen deep-minor fourth-moment upper bound. -/
theorem L_goldbach_deep_fourth_moment_refutation :
    ¬ (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun u => ‖S n w u‖ ^ 4) t) (0 : ℝ) 1 MeasureTheory.volume ≤ (n : ℝ) ^ (2 + η)) := by
  intro upper
  obtain ⟨N,hN⟩ := upper (1/6) (by norm_num)
  obtain ⟨n,hn,hcounter⟩ := (Filter.eventually_ge_atTop N |>.and GoldbachFourthCertificate.large_moment).exists
  exact (hcounter.not_ge (hN n hn))

end PEqualNP.Outside
