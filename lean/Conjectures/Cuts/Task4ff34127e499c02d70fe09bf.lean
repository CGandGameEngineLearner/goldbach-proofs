import Mathlib.NumberTheory.LSeries.WeakPNT
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PEqualNP.Outside.L_goldbach_frontier_skirt_polylog_moduli

/-!
At modulus one, the verified short-progression mean bounds the total
discrepancy of length-H prime windows over integer starts in [n/4,n/2).
Reflection takes distinct prime-strip indices into that block. Each
discrepancy is weighted by at most log n, which the mean estimate absorbs.
-/

namespace DyadicShortAverage

open Finset

private noncomputable def weight (p : ℕ) : ℝ :=
  if p.Prime then Real.log p else 0

private theorem weight_nonneg (p : ℕ) : 0 ≤ weight p := by
  by_cases hp : p.Prime <;> simp [weight,hp,Real.log_natCast_nonneg]

private noncomputable def score (u d : ℕ) : ℝ :=
  ∑ i ∈ range u, weight (4*u+i) * weight (4*u-i+d)

private theorem theta_prefix {m : ℕ} (hm : 0 < m) :
    Chebyshev.theta ((m-1 : ℕ):ℝ) = ∑ i ∈ range m, weight i := by
  have hs : Icc 0 (m-1) = range m := by
    ext i; simp only [mem_Icc, mem_range, Nat.zero_le, true_and]; omega
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, hs, sum_filter]
  rfl

/-- The prime number theorem supplies half the length in logarithmic prime
mass on this fixed-proportion strip, for all sufficiently large strip sizes. -/
private theorem eventual_strip_weight :
    ∃ U : ℕ, ∀ u ≥ U, (u:ℝ)/2 ≤ ∑ i ∈ range u, weight (4*u+i) := by
  have hlo := Chebyshev.tendsto_theta_div_atTop.eventually_const_lt
    (by norm_num : (31/32 : ℝ) < 1)
  have hhi := Chebyshev.tendsto_theta_div_atTop.eventually_lt_const
    (by norm_num : (1 : ℝ) < 33/32)
  obtain ⟨a,ha⟩ := Filter.eventually_atTop.mp (hlo.and hhi)
  obtain ⟨U,hU⟩ := exists_nat_ge a
  refine ⟨max U 2, ?_⟩
  intro u hu
  have hpos (m : ℕ) (hm : u ≤ m) : 0 < (m:ℝ) := by exact_mod_cast (show 0<m by omega)
  have hthr (m : ℕ) (hm : u ≤ m) : a ≤ (m:ℝ) :=
    hU.trans (Nat.cast_le.mpr (by omega))
  have hu4 : u ≤ 4*u-1 := by omega
  have hu5 : u ≤ 5*u-1 := by omega
  have h1 := (lt_div_iff₀ (hpos _ hu5)).mp (ha _ (hthr _ hu5)).1
  have h2 := (div_lt_iff₀ (hpos _ hu4)).mp (ha _ (hthr _ hu4)).2
  have h4 : 0 < 4*u := by omega
  have h5 : 0 < 5*u := by omega
  rw [theta_prefix h5, show 5*u=4*u+u by omega, sum_range_add] at h1
  rw [theta_prefix h4] at h2
  push_cast [Nat.cast_sub (by omega : 1 ≤ 4*u), Nat.cast_sub (by omega : 1 ≤ 4*u+u)] at h1 h2
  linarith

/-- For modulus one, the verified error dominates the deficit at this start. -/
private theorem row_lower (y H : ℕ) :
    (H:ℝ) ≤ (∑ d ∈ range H, weight (y+1+d)) + V2h.V4z 1 H (y:ℝ) := by
  classical
  let I := V2h.V9a H (y:ℝ)
  have hI : I = Ioc y (y+H) := by simp [I,V2h.V9a]
  have hs : (∑ d ∈ range H, weight (y+1+d)) = ∑ z ∈ I, weight z := by
    rw [hI]
    apply sum_bij (fun d _ => y+1+d)
    · intro d hd; have := mem_range.mp hd; exact mem_Ioc.mpr ⟨by omega, by omega⟩
    · intro d _ t _ h; exact Nat.add_left_cancel h
    · intro z hz
      obtain ⟨hz₁,hz₂⟩ := mem_Ioc.mp hz
      exact ⟨z-(y+1), mem_range.mpr (by omega), by omega⟩
    · intro _ _; rfl
  have hf : I.filter (fun z : ℕ => (z : ZMod 1) = 1) = I :=
    filter_true_of_mem (fun _ _ => Subsingleton.elim _ _)
  have hcap := V3z.V114 I (1 : ZMod 1) isUnit_one
  change ‖(∑ z ∈ I.filter (fun z : ℕ => (z : ZMod 1) = 1), (weight z : ℂ)) -
    (I.card:ℂ) / ((Nat.totient 1:ℕ):ℂ)‖ ≤ V2h.V4z 1 H (y:ℝ) at hcap
  rw [hf, show I.card = H from V2h.V20b _ _, Nat.totient_one, Nat.cast_one,
    div_one, ← Complex.ofReal_sum] at hcap
  have ha : |(∑ z ∈ I, weight z) - (H:ℝ)| ≤ V2h.V4z 1 H (y:ℝ) := by
    simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] using hcap
  rw [hs]
  linarith [(abs_le.mp ha).1]

private theorem strip_lower (u H : ℕ) (hu : 0 < u)
    (hstrip : (u:ℝ)/2 ≤ ∑ i ∈ range u, weight (4*u+i))
    (herror : Real.log (8*u:ℕ) * (∑ y ∈ Ico (2*u) (4*u), V2h.V4z 1 H (y:ℝ)) ≤
      (H:ℝ)*u/4) :
    (H:ℝ)*u/4 ≤ ∑ d ∈ range H, score u d := by
  classical
  let y := fun i : ℕ => 4*u-i-1
  let E := fun z : ℕ => V2h.V4z 1 H (z:ℝ)
  let L := Real.log (8*u:ℕ)
  have hL : 0 ≤ L := Real.log_natCast_nonneg _
  have hinj : Set.InjOn y (↑(range u) : Set ℕ) := by
    intro i hi t ht he
    have hai := mem_range.mp hi
    have hat := mem_range.mp ht
    dsimp [y] at he
    omega
  have hsub : (range u).image y ⊆ Ico (2*u) (4*u) := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
    have := mem_range.mp hi
    dsimp [y]
    exact mem_Ico.mpr ⟨by omega, by omega⟩
  have hsE : (∑ i ∈ range u, E (y i)) ≤ ∑ z ∈ Ico (2*u) (4*u), E z := calc
    _ = ∑ z ∈ (range u).image y, E z := (sum_image hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => V2h.Vj2 1 H z)
  have hw (i : ℕ) (hi : i ∈ range u) : weight (4*u+i) ≤ L := by
    have hiu := mem_range.mp hi
    by_cases hp : (4*u+i).Prime
    · simpa only [weight, ite_eq_left hp] using Real.log_le_log
        (show (0:ℝ)<(4*u+i:ℕ) by exact_mod_cast hp.pos)
        (show ((4*u+i:ℕ):ℝ)≤((8*u:ℕ):ℝ) by exact_mod_cast (show 4*u+i≤8*u by omega))
    · simpa [weight,hp] using hL
  have herr : (∑ i ∈ range u, weight (4*u+i)*E (y i)) ≤ (H:ℝ)*u/4 := calc
    _ ≤ ∑ i ∈ range u, L*E (y i) :=
      sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hw i hi) (V2h.Vj2 1 H _)
    _ = L * ∑ i ∈ range u, E (y i) := (mul_sum ..).symm
    _ ≤ L * ∑ z ∈ Ico (2*u) (4*u), E z := mul_le_mul_of_nonneg_left hsE hL
    _ ≤ _ := herror
  have htotal : (∑ i ∈ range u, weight (4*u+i)) * (H:ℝ) ≤
      (∑ d ∈ range H, score u d) + ∑ i ∈ range u, weight (4*u+i) * E (y i) := calc
    _ = ∑ i ∈ range u, weight (4*u+i)*(H:ℝ) := sum_mul _ _ _
    _ ≤ ∑ i ∈ range u, weight (4*u+i)*((∑ d ∈ range H, weight (4*u-i+d)) + E (y i)) := by
      apply sum_le_sum
      intro i hi
      have hiu := mem_range.mp hi
      apply mul_le_mul_of_nonneg_left _ (weight_nonneg _)
      have hz : y i+1 = 4*u-i := by dsimp [y]; omega
      simpa only [hz] using row_lower (y i) H
    _ = _ := by simp only [mul_add, sum_add_distrib, mul_sum, score]; rw [sum_comm (s := range u) (t := range H)]
  nlinarith only [mul_le_mul_of_nonneg_right hstrip (Nat.cast_nonneg (α := ℝ) H), htotal, herr]

end DyadicShortAverage

open Finset DyadicShortAverage

theorem Conjectures.Cuts.Task4ff34127e499c02d70fe09bf : (∃ (x1 : ℕ),   ∀ x2 ≥ x1,     have x4 : ℕ := (2 : ℕ) ^ x2;     have x5 : ℕ := x4 / (8 : ℕ);     have x6 : ℕ := (2 : ℕ) ^ (((7 : ℕ) * x2 + (11 : ℕ)) / (12 : ℕ));     have x7 : ℕ → ℝ := fun (x7 : ℕ) => if Nat.Prime x7 then Real.log ↑x7 else (0 : ℝ);     have x8 : ℕ → ℝ := fun (x8 : ℕ) => ∑ x9 ∈ Finset.range x5, x7 ((4 : ℕ) * x5 + x9) * x7 ((4 : ℕ) * x5 - x9 + x8);     ↑x6 * ↑x4 / (32 : ℝ) ≤ ∑ x9 ∈ Finset.range x6, x8 x9) := by
  obtain ⟨C,hC,X₀,hmean⟩ := Vie.V1ew (V7e.Vzg (V6h.Vz5 30))
  obtain ⟨U,hU⟩ := eventual_strip_weight
  obtain ⟨M,hM⟩ := exists_nat_ge (Real.exp (max (max (16*C) 1) (Real.log 4)))
  refine ⟨max (max (8*U) (4*X₀)) (max (4*M) 120), ?_⟩
  intro k hk
  let n : ℕ := 2^k
  let u := n/8
  let X := 2*u
  let H : ℕ := 2^((7*k+11)/12)
  have hk120 : 120 ≤ k := by omega
  have hkn : k < n := Nat.lt_two_pow_self
  have h8 : 8*u = n := Nat.mul_div_cancel' (show (2:ℕ)^3 ∣ 2^k from pow_dvd_pow 2 (by omega))
  have h4 : 4*X = n := by dsimp [X]; omega
  have hXp : (0:ℝ) < X := by exact_mod_cast (show 0<X by omega)
  have hL : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1<X by omega))
  have hlogs : Real.log n = Real.log 4 + Real.log X := by
    rw [← h4, Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hXp.ne']
  have hlarge : max (max (16*C) 1) (Real.log 4) ≤ Real.log X :=
    (Real.le_log_iff_exp_le hXp).mpr (hM.trans (Nat.cast_le.mpr (by omega)))
  have hmax := (le_max_left (max (16*C) 1) (Real.log 4)).trans hlarge
  have hL1 : 1 ≤ Real.log X := (le_max_right ..).trans hmax
  have hDL : Real.log n ≤ 2*Real.log X := by linarith [le_max_right (max (16*C) 1) (Real.log 4)]
  have hcoeff : 8*C*Real.log n ≤ (Real.log X)^12 := calc
    _ ≤ (16*C)*Real.log X := by nlinarith only [mul_le_mul_of_nonneg_left hDL hC.le]
    _ ≤ (Real.log X)^11 * Real.log X :=
      mul_le_mul_of_nonneg_right (((le_max_left ..).trans hmax).trans (le_self_pow₀ hL1 (by decide))) hL.le
    _ = _ := by ring
  have hpos : 0 < H := by dsimp [H]; positivity
  have hwidth : H ≤ u := by
    have : 8*H ≤ n := calc
      8*H = (2:ℕ)^(3+(7*k+11)/12) := by rw [pow_add]; rfl
      _ ≤ n := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hscale : (X:ℝ)^(7/12:ℝ) ≤ (H:ℝ) := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : (12:ℕ)≠0)).mp
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg X)]
    norm_num
    have hX : X^7 ≤ n^7 := Nat.pow_le_pow_left (by omega : X≤n) 7
    have hn : n^7 ≤ H^12 := by
      dsimp [n,H]; rw [← pow_mul, ← pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact_mod_cast hX.trans hn
  have hsum := hmean 1 X H (by omega) (by omega) hpos (by dsimp [X]; omega) (by simpa using hscale)
  rw [← Vbi.Vh1 1 H (by omega : X≤2*X)] at hsum
  have hnat : 2*X = 4*u := by dsimp [X]; omega
  rw [hnat] at hsum
  have herror : Real.log n * (∑ y ∈ Ico X (4*u), V2h.V4z 1 H (y:ℝ)) ≤ (H:ℝ)*u/4 := calc
    _ ≤ Real.log n * (C*H*X/(Real.log X)^12) :=
      mul_le_mul_of_nonneg_left hsum (Real.log_natCast_nonneg _)
    _ = (Real.log n*C*H*X)/(Real.log X)^12 := by ring
    _ ≤ _ := by
      apply (div_le_iff₀ (pow_pos hL 12)).mpr
      have hh := mul_le_mul_of_nonneg_right hcoeff (show 0 ≤ (H:ℝ)*(X:ℝ) by positivity)
      dsimp [X] at hh ⊢
      push_cast at hh ⊢
      nlinarith only [hh]
  have endp := strip_lower u H (by omega) (hU u (by omega)) (by rwa [h8])
  change (H:ℝ)*(n:ℝ)/32 ≤ ∑ d ∈ range H, score u d
  have heq : (8:ℝ)*u = (n:ℝ) := by exact_mod_cast h8
  nlinarith only [endp, congrArg (fun t : ℝ => (H:ℝ)*t) heq]
