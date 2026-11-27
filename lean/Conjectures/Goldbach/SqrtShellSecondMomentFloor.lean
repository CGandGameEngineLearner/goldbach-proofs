import Mathlib
import Conjectures.Goldbach.SqrtArcSecondMomentFloor

/-!
# Second moment on the square-root shell above the cube-root cutoff

On the annulus `sqrtArcs n \ wideArcs n` the second moment of the prime-log
exponential sum is at least `c * n * log n`.  The proof places a one-sided
window of width `1/(6*n)` to the right of each reduced fraction whose
squarefree denominator lies between `n^(1/3)` and `n^(3/8)`.  Rational spacing
keeps the windows out of `wideArcs`, and the centre of each window puts it
inside `sqrtArcs`.  Summing the window energies over geometric denominator
blocks gives the logarithmic gain.
-/

set_option maxHeartbeats 4000000

open MeasureTheory Set
open scoped BigOperators Interval

namespace Conjectures.Goldbach.SqrtShellSecondMomentFloor

open Conjectures.Goldbach.SqrtArcSecondMomentFloor
open Conjectures.Goldbach.SqrtArcSecondMomentFloor.GoldbachSupport

namespace GoldbachSupport

/-- Reduced fractions determine their numerator and denominator. -/
private theorem centers_unique {q r a b : ℕ} (hq : 0 < q)
    (ha : Nat.Coprime a q) (hb : Nat.Coprime b r) (he : a * r = b * q) :
    q = r ∧ a = b := by
  have hdq : q ∣ a * r := he ▸ Nat.dvd_mul_left q b
  have hdr : r ∣ b * q := he.symm ▸ Nat.dvd_mul_left r a
  have hqr := Nat.dvd_antisymm (ha.symm.dvd_of_dvd_mul_left hdq)
    (hb.symm.dvd_of_dvd_mul_left hdr)
  subst hqr
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hq he⟩

/-- Sum the disjoint shifted intervals at reduced fractions and keep only their
contribution to the integral over the part of the square-root arc family that
avoids the cube-root wide-arc mask. -/
theorem assembleShell (s : Finset ℕ) (D H D₂ H₂ n : ℕ) (S : ℝ → ℂ) (hS : Continuous S)
    (hn : 0 < n)
    (hD : 1 ≤ D)
    (hden : ∀ q ∈ s, D < q)
    (hend : ∀ q ∈ s, (q : ℝ) ≤ 6 * n)
    (hmask : ∀ q ∈ s, (q : ℝ) * H + (q : ℝ) * D / 6 < n)
    (hpair : ∀ q ∈ s, ∀ r ∈ s, (q : ℝ) * r < 6 * n)
    (hden₂ : ∀ q ∈ s, (q : ℝ) ≤ (D₂ : ℝ))
    (hrad : ∀ q ∈ s, (q : ℝ) ≤ 6 * (H₂ : ℝ))
    (hamp : ∀ q ∈ s, ∀ h ∈ Icc (0 : ℝ) (1 / (6 * n)),
      (n : ℝ) / 8 ≤ ‖∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          S ((a : ℝ) / q + h)‖) :
    ∑ q ∈ s, (n : ℝ) / (384 * (q : ℝ)) ≤
      ∫ t in (0 : ℝ)..1,
        (publishedWideArcs D₂ H₂ n \ publishedWideArcs D H n).indicator (fun x => ‖S x‖ ^ 2) t := by
  classical
  let A := fun q : ℕ => (Finset.range q).filter (fun a => Nat.Coprime a q)
  let indices := s.sigma A
  let w : ℝ := 1 / (6 * (n : ℝ))
  let f : ℝ → ℝ := fun t => ‖S t‖ ^ 2
  let c : (Σ _ : ℕ, ℕ) → ℝ := fun i => (i.2 : ℝ) / i.1
  let W := fun i => Ioc (c i) (c i + w)
  let target := Ioc (0 : ℝ) 1 ∩ (publishedWideArcs D₂ H₂ n \ publishedWideArcs D H n)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hcont : Continuous f := by
    have h : f = fun t => ‖S t‖ * ‖S t‖ := by funext t; simp [f, pow_two]
    rw [h]
    exact hS.norm.mul hS.norm
  have hindex {i : Σ _ : ℕ, ℕ} (hi : i ∈ indices) :
      i.1 ∈ s ∧ i.2 < i.1 ∧ Nat.Coprime i.2 i.1 := by
    simpa [indices, A] using hi
  have hqpos {q : ℕ} (hq : q ∈ s) : 0 < q := Nat.zero_lt_of_lt (hden q hq)
  have hge {q : ℕ} (hq : q ∈ s) : 0 < (q : ℝ) := by exact_mod_cast hqpos hq
  have hsubset {i : Σ _ : ℕ, ℕ} (hi : i ∈ indices) : W i ⊆ target := by
    rcases hindex hi with ⟨hq, ha, hcop⟩
    intro t ht
    change c i < t ∧ t ≤ c i + w at ht
    have hfirst : 0 ≤ c i := by dsimp [c]; positivity
    have hqv := hge hq
    have ha1 : (i.2 : ℝ) + 1 ≤ i.1 := by exact_mod_cast ha
    have hsmall : w ≤ 1 / (i.1 : ℝ) := one_div_le_one_div_of_le hqv (hend _ hq)
    have hlast : t ≤ 1 := calc
      t ≤ (i.2 : ℝ) / i.1 + 1 / i.1 := by
        change t ≤ c i + 1 / i.1
        linarith only [ht.2, hsmall]
      _ = ((i.2 : ℝ) + 1) / i.1 := by ring
      _ ≤ 1 := (div_le_one hqv).2 ha1
    refine ⟨⟨hfirst.trans_lt ht.1, hlast⟩, ?_, ?_⟩
    · have hqD₂ : (i.1 : ℝ) ≤ (D₂ : ℝ) := hden₂ _ hq
      have hqrad : (i.1 : ℝ) ≤ 6 * (H₂ : ℝ) := hrad _ hq
      have hr : (1 : ℝ) / 6 ≤ (H₂ : ℝ) / (i.1 : ℝ) :=
        (le_div_iff₀ hqv).2 (by linarith only [hqrad])
      have hb : w ≤ (H₂ : ℝ) / ((i.1 : ℝ) * n) := by
        calc w = ((1 : ℝ) / 6) / n := by dsimp [w]; field_simp
          _ ≤ ((H₂ : ℝ) / (i.1 : ℝ)) / n := div_le_div_of_nonneg_right hr hn'.le
          _ = (H₂ : ℝ) / ((i.1 : ℝ) * n) := by field_simp
      have hDq : (1 : ℕ) ≤ i.1 := by have := hD.trans_lt (hden _ hq); omega
      refine ⟨i.1, i.2, hDq, Nat.cast_le.mp hqD₂, le_of_lt ha, hcop, ?_⟩
      · have hnn : (0 : ℝ) ≤ t - c i := by linarith only [ht.1.le]
        have habs : |t - (i.2 : ℝ) / (i.1 : ℝ)| = t - c i := by
          rw [abs_of_nonneg hnn]
        rw [habs]
        linarith only [ht.2, hb]
    · have hout := outsideWideArcs i.2 i.1 D H n (t - c i) hcop (hden _ hq) hn
        (sub_nonneg.mpr ht.1.le) (by change t - c i ≤ w; linarith only [ht.2]) (hmask _ hq)
      change c i + (t - c i) ∉ publishedWideArcs D H n at hout
      rwa [add_sub_cancel] at hout
  have hdisj : Set.Pairwise (↑indices) (fun i j => Disjoint (W i) (W j)) := by
    intro i hi j hj hne
    rcases hindex hi with ⟨hqi, hai, hci⟩
    rcases hindex hj with ⟨hqj, haj, hcj⟩
    have hcross : i.2 * j.1 ≠ j.2 * i.1 := by
      intro he
      obtain ⟨h₁, h₂⟩ := centers_unique (hqpos hqi) hci hcj he
      apply hne
      cases i
      cases j
      simp_all
    apply Set.disjoint_left.mpr
    intro t ht hu
    change c i < t ∧ t ≤ c i + w at ht
    change c j < t ∧ t ≤ c j + w at hu
    have hne' := deepArcWindowsDisjoint i.2 j.2 i.1 j.1 n (t - c i) (t - c j)
      (hge hqi) (hge hqj) hn' hcross (hpair i.1 hqi j.1 hqj)
      (sub_nonneg.mpr ht.1.le) (by change t - c i ≤ w; linarith only [ht.2])
      (sub_nonneg.mpr hu.1.le) (by change t - c j ≤ w; linarith only [hu.2])
    apply hne'
    dsimp only [c] at *
    linarith only [ht.1.le, hu.1.le]
  have hmeasArc : MeasurableSet (publishedWideArcs D₂ H₂ n \ publishedWideArcs D H n) :=
    (measurable_publishedWideArcs ..).diff (measurable_publishedWideArcs ..)
  have htarget : MeasurableSet target :=
    measurableSet_Ioc.inter ((measurable_publishedWideArcs ..).diff (measurable_publishedWideArcs ..))
  have hWmeas : ∀ i ∈ indices, MeasurableSet (W i) := fun i _ => measurableSet_Ioc
  have hWint : ∀ i ∈ indices, IntegrableOn f (W i) :=
    fun i _ => hcont.integrableOn_Ioc
  have hunion : ∀ x ∈ ⋃ i ∈ indices, W i, x ∈ target :=
    fun x hx => by
      simp only [mem_iUnion] at hx
      obtain ⟨i, hi, hxi⟩ := hx
      exact hsubset hi hxi
  have hbase : IntegrableOn f (Ioc (0 : ℝ) 1) := hcont.integrableOn_Ioc
  have hmain := setIntegral_mono_set (hbase.mono_set (Set.inter_subset_left))
    (Filter.Eventually.of_forall (fun x => by dsimp [f]; positivity))
    (Filter.Eventually.of_forall hunion)
  calc ∑ q ∈ s, (n : ℝ) / (384 * (q : ℝ))
      ≤ ∑ q ∈ s, ∑ a ∈ A q, ∫ h in (0 : ℝ)..w, ‖S ((a : ℝ) / q + h)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro q hq
        exact residueWindowEnergy (A q) (fun a h => S ((a : ℝ) / q + h)) hn' (hqpos hq)
          (by simpa [A] using Finset.card_filter_le (Finset.range q) (fun a => Nat.Coprime a q))
          (fun a _ => hS.comp (by continuity))
          (fun h hh => hamp q hq h hh)
    _ = ∑ i ∈ indices, ∫ t in W i, f t := by
        rw [Finset.sum_sigma]
        refine Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun a ha => ?_
        have hshift : ∫ h in (0 : ℝ)..w, ‖S ((a : ℝ) / q + h)‖ ^ 2 = ∫ t in W ⟨q, a⟩, f t :=
          calc ∫ h in (0 : ℝ)..w, ‖S ((a : ℝ) / q + h)‖ ^ 2
              = ∫ h in (0 : ℝ)..w, f (c ⟨q, a⟩ + h) := rfl
            _ = ∫ h in c ⟨q, a⟩ + 0..c ⟨q, a⟩ + w, f h :=
                intervalIntegral.integral_comp_add_left (f := f) (a := (0 : ℝ)) (b := w) (d := c ⟨q, a⟩)
            _ = ∫ h in c ⟨q, a⟩..c ⟨q, a⟩ + w, f h := by rw [add_zero]
            _ = ∫ t in W ⟨q, a⟩, f t := by
                rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right hw)]
        exact hshift
    _ = ∫ t in ⋃ i ∈ indices, W i, f t := by
        rw [integral_biUnion_finset indices hWmeas hdisj hWint]
    _ ≤ ∫ t in target, f t := hmain
    _ = ∫ t in (0 : ℝ)..1,
          (publishedWideArcs D₂ H₂ n \ publishedWideArcs D H n).indicator (fun x => ‖S x‖ ^ 2) t := by
        rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
          setIntegral_indicator hmeasArc]

end GoldbachSupport

section
open Filter
open scoped Topology

namespace ShellCount

noncomputable def maskD (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
noncomputable def logSquare (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2
noncomputable def maskH (n : ℕ) : ℕ := 256 * maskD n * logSquare n
noncomputable def shellD (n : ℕ) : ℕ := ⌊Real.sqrt (n : ℝ) / ((Nat.log 2 (n + 2) : ℝ) ^ 4)⌋₊
noncomputable def shellH (n : ℕ) : ℕ := 256 * shellD n * logSquare n

theorem eventually_log_small : ∀ᶠ n : ℕ in atTop,
    (Nat.log 2 (n + 2) : ℝ) ≤ (1 / 16) * (n : ℝ) ^ (1 / 48 : ℝ) := by
  have hsmall : ∀ᶠ x : ℝ in atTop, Real.log x ≤ (1 / 64) * x ^ (1 / 96 : ℝ) := by
    have h := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 96 by norm_num)).bound
      (show (0 : ℝ) < 1 / 64 by norm_num)
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) _)] using hx
  have hN : ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ (1 / 64) * (n : ℝ) ^ (1 / 96 : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmall
  filter_upwards [hN, eventually_ge_atTop 16] with n hn h16
  let l := Nat.log 2 (n + 2)
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hp : (2 : ℝ) ^ l ≤ (n : ℝ) + 2 := by
    have h := Nat.pow_log_le_self 2 (by omega : n + 2 ≠ 0)
    exact_mod_cast h
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (l : ℝ) * Real.log 2 ≤ Real.log ((n : ℝ) + 2) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ l) hp
    rwa [Real.log_pow] at h
  have h2 : Real.log ((n : ℝ) + 2) ≤ 2 * Real.log (n : ℝ) := by
    have hle : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by
      have hnf : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h16
      have h2 : (0 : ℝ) ≤ (n : ℝ) - 2 := by linarith only [hnf]
      have h3 : (0 : ℝ) ≤ (n : ℝ) + 1 := by linarith only [hnf]
      nlinarith only [mul_nonneg h2 h3, hnf]
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) + 2) hle
    rw [Real.log_pow] at h
    push_cast at h
    linarith only [h]
  let x : ℝ := (n : ℝ) ^ (1 / 96 : ℝ)
  have hrw : (n : ℝ) ^ (1 / 48 : ℝ) = x ^ 2 := by
    show (n : ℝ) ^ (1 / 48 : ℝ) = ((n : ℝ) ^ (1 / 96 : ℝ)) ^ 2
    rw [← Real.rpow_natCast ((n : ℝ) ^ (1 / 96 : ℝ)) 2, ← Real.rpow_mul (le_of_lt hnpos)]
    norm_num
  have hx1 : (1 : ℝ) ≤ x := by
    show (1 : ℝ) ≤ (n : ℝ) ^ (1 / 96 : ℝ)
    have hnf : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h16
    exact Real.one_le_rpow (by linarith only [hnf]) (by norm_num)
  have hchain : (l : ℝ) * Real.log 2 ≤ x / 32 := by
    have h4 : 2 * Real.log (n : ℝ) ≤ 2 * ((1 / 64) * x) := by
      have := hn
      show 2 * Real.log (n : ℝ) ≤ 2 * ((1 / 64) * ((n : ℝ) ^ (1 / 96 : ℝ)))
      linarith only [this]
    linarith only [h1, h2, h4]
  have hhalf : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hl_nonneg : (0 : ℝ) ≤ (l : ℝ) := by positivity
  have hfinal : (l : ℝ) ≤ (1 / 16) * (n : ℝ) ^ (1 / 48 : ℝ) := by
    rw [hrw]
    have h6 : (l : ℝ) ≤ (l : ℝ) * (2 * Real.log 2) := by nlinarith only [hhalf, hl_nonneg]
    have h7 : 2 * ((l : ℝ) * Real.log 2) ≤ 2 * (x / 32) := by nlinarith only [hchain]
    have h8 : (2 : ℝ) * (x / 32) = x / 16 := by ring
    have h9 : x / 16 ≤ x ^ 2 / 16 := by nlinarith only [hx1, sq_nonneg x]
    have h10 : (l : ℝ) * (2 * Real.log 2) = 2 * ((l : ℝ) * Real.log 2) := by ring
    linarith only [h6, h7, h8, h9, h10]
  exact hfinal

theorem main_bound : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    c * (n : ℝ) * Real.log (n : ℝ) ≤
      ∫ t in (0 : ℝ)..1,
        (publishedWideArcs (shellD n) (shellH n) n \ publishedWideArcs (maskD n) (maskH n) n).indicator
          (fun u => ‖GoldbachL2Arithmetic.primeSum n u‖ ^ 2) t := by
  classical
  refine ⟨(1 / (2304 * Real.log 2)) / 384, by positivity, Filter.eventually_atTop.1 ?_⟩
  filter_upwards [eventually_log_small, primeAmplitudeBounds, eventually_ge_atTop (2 ^ 1000 : ℕ)]
    with n hl hPA hbig
  obtain ⟨hn2, hθ, hqlog⟩ := hPA
  let l := Nat.log 2 (n + 2)
  let m := Nat.log 2 n
  let J := m / 72
  let D := maskD n
  let Q₂ := shellD n
  let H₂ := shellH n
  let H := maskH n
  let M := 8 ^ J * max D 1
  let s := (Finset.Ioc (max D 1) M).filter Squarefree
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h : 0 < n := by
      have h2 : (0 : ℕ) < 2 ^ 1000 := by positivity
      omega
    exact_mod_cast h
  let t : ℝ := (n : ℝ) ^ (1 / 48 : ℝ)
  have h48 : ((16 : ℝ)) ^ (48 : ℕ) ≤ (n : ℝ) := by
    have h0 : (16 : ℕ) ^ 48 ≤ n := by
      calc (16 : ℕ) ^ 48 = (2 : ℕ) ^ 192 := by
            rw [show (16 : ℕ) = (2 : ℕ) ^ 4 by norm_num, ← pow_mul]
        _ ≤ (2 : ℕ) ^ 1000 := pow_le_pow_right₀ (by norm_num) (by norm_num)
        _ ≤ n := hbig
    have h3 : ((16 : ℕ) ^ 48 : ℝ) = (16 : ℝ) ^ (48 : ℕ) := by norm_num
    have h4 : ((16 : ℕ) ^ 48 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h0
    linarith only [h3, h4]
  have ht16 : 16 ≤ t := by
    have hid : ((16 : ℝ) ^ (48 : ℕ)) ^ (1 / 48 : ℝ) = 16 := by
      rw [← Real.rpow_natCast (16 : ℝ) 48, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 16)]
      norm_num
    calc (16 : ℝ) = ((16 : ℝ) ^ (48 : ℕ)) ^ (1 / 48 : ℝ) := hid.symm
      _ ≤ (n : ℝ) ^ (1 / 48 : ℝ) := Real.rpow_le_rpow (by positivity) h48 (by norm_num)
      _ = t := rfl
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have htpow : ∀ k : ℕ, t ^ k = (n : ℝ) ^ ((k : ℝ) / 48) := by
    intro k
    show ((n : ℝ) ^ (1 / 48 : ℝ)) ^ k = (n : ℝ) ^ ((k : ℝ) / 48)
    rw [← Real.rpow_natCast ((n : ℝ) ^ (1 / 48 : ℝ)) k, ← Real.rpow_mul (le_of_lt hnpos)]
    congr 1
    ring
  have ht2 : t ^ 2 = (n : ℝ) ^ (1 / 24 : ℝ) := by rw [htpow 2]; norm_num
  have ht16' : t ^ 16 = (n : ℝ) ^ (1 / 3 : ℝ) := by rw [htpow 16]; norm_num
  have ht18 : t ^ 18 = (n : ℝ) ^ (3 / 8 : ℝ) := by rw [htpow 18]; norm_num
  have ht24 : t ^ 24 = Real.sqrt (n : ℝ) := by
    rw [htpow 24, Real.sqrt_eq_rpow]
    congr 1
    ring
  have ht48 : t ^ 48 = (n : ℝ) := by rw [htpow 48]; norm_num
  have hlt : (l : ℝ) ≤ t / 16 := by
    rw [show t = (n : ℝ) ^ (1 / 48 : ℝ) from rfl]
    linarith only [hl]
  have hl2le : (l : ℝ) ^ 2 ≤ t ^ 2 / 256 := by
    have hl0 : (0 : ℝ) ≤ (l : ℝ) := by exact_mod_cast Nat.zero_le l
    have h1 : (l : ℝ) ^ 2 ≤ (t / 16) ^ 2 := pow_le_pow_left₀ hl0 hlt 2
    have h2 : (t / 16) ^ 2 = t ^ 2 / 256 := by ring
    calc (l : ℝ) ^ 2 ≤ (t / 16) ^ 2 := h1
      _ = t ^ 2 / 256 := h2
  have hl4le : (l : ℝ) ^ 4 ≤ t ^ 6 := by
    have hl0 : (0 : ℝ) ≤ (l : ℝ) := by exact_mod_cast Nat.zero_le l
    have h1 : (l : ℝ) ^ 4 ≤ (t / 16) ^ 4 := pow_le_pow_left₀ hl0 hlt 4
    have h2 : (t / 16) ^ 4 = t ^ 4 / 65536 := by ring
    have h3 : t ^ 4 / 65536 ≤ t ^ 4 := div_le_self (by positivity) (by norm_num)
    have h4 : t ^ 4 ≤ t ^ 6 := pow_le_pow_right₀ ht1 (by norm_num)
    calc (l : ℝ) ^ 4 ≤ (t / 16) ^ 4 := h1
      _ = t ^ 4 / 65536 := h2
      _ ≤ t ^ 4 := h3
      _ ≤ t ^ 6 := h4
  have hDle : (D : ℝ) ≤ t ^ 16 := by
    have h := Nat.floor_le (show (0 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) by positivity)
    have h' : (D : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := h
    rw [← ht16'] at h'
    exact h'
  have hHle : (H : ℝ) ≤ t ^ 18 := by
    have hHH : H = 256 * D * l ^ 2 := rfl
    rw [hHH]
    push_cast
    calc 256 * (D : ℝ) * (l : ℝ) ^ 2 ≤ 256 * t ^ 16 * (t ^ 2 / 256) := by gcongr
      _ = t ^ 18 := by ring
  have h72 : 72 * J ≤ m := by
    have h := Nat.div_mul_le_self m 72
    omega
  have h72' : (72 : ℝ) * (J : ℝ) ≤ (m : ℝ) := by exact_mod_cast h72
  have h2m : (2 : ℝ) ^ (m : ℕ) ≤ (n : ℝ) := by
    have h := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
    exact_mod_cast h
  have h8J : (8 : ℝ) ^ J ≤ t ^ 2 := by
    refine (Real.rpow_le_rpow_iff (by positivity) (by positivity)
      (by norm_num : (0 : ℝ) < ((24 : ℕ) : ℝ))).1 ?_
    rw [Real.rpow_natCast, Real.rpow_natCast]
    have hcast1 : ((8 : ℝ) ^ J) ^ 24 = (2 : ℝ) ^ (72 * J) := by
      rw [← pow_mul, show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num, ← pow_mul]
      congr 1
      ring
    have hcast2 : (t ^ 2) ^ 24 = (n : ℝ) := by
      rw [← pow_mul, show (2 * 24 : ℕ) = 48 by norm_num, ht48]
    have h3 : (2 : ℝ) ^ (72 * J) ≤ (2 : ℝ) ^ (Nat.log 2 n) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h4 : (2 : ℝ) ^ (Nat.log 2 n) ≤ (n : ℝ) := h2m
    rw [hcast1, hcast2]
    exact h3.trans h4
  have hmaxle : max (D : ℝ) 1 ≤ t ^ 16 :=
    max_le hDle (one_le_pow₀ ht1)
  have hMle : (M : ℝ) ≤ t ^ 18 := by
    have hMM : M = 8 ^ J * max D 1 := rfl
    rw [hMM]
    push_cast
    calc (8 : ℝ) ^ J * max (D : ℝ) 1 ≤ t ^ 2 * t ^ 16 := by gcongr
      _ = t ^ 18 := by ring
  have hDpos : 1 ≤ D := by
    have hnf2 : (1 : ℝ) ≤ (n : ℝ) := by
      have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      linarith
    have h := Nat.le_floor (show (1 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) by
      exact Real.one_le_rpow hnf2 (by norm_num))
    exact h
  have hMleQ₂ : M ≤ Q₂ := by
    have hlt4 : (0 : ℝ) < (l : ℝ) ^ 4 := by
      have h0 : (0 : ℝ) < (l : ℝ) := by
        have h1l : 1 ≤ l := Nat.le_log_of_pow_le (by norm_num) (by omega : 2 ≤ n + 2)
        exact_mod_cast (by omega : 0 < l)
      positivity
    apply Nat.le_floor
    show (M : ℝ) ≤ Real.sqrt (n : ℝ) / (l : ℝ) ^ 4
    rw [le_div_iff₀ hlt4]
    have h1 : (M : ℝ) * (l : ℝ) ^ 4 ≤ t ^ 18 * t ^ 6 := by gcongr
    have h2 : t ^ 18 * t ^ 6 = t ^ 24 := by ring
    have h3 : t ^ 24 = Real.sqrt (n : ℝ) := ht24
    linarith only [h1, h2, h3]
  have hMleL : M ≤ ⌊Real.sqrt (n : ℝ) / 4⌋₊ := by
    apply Nat.le_floor
    have h4 : (4 : ℝ) ≤ t ^ 6 := by
      have h : (16 : ℝ) ^ 6 ≤ t ^ 6 := pow_le_pow_left₀ (by norm_num) ht16 6
      nlinarith only [h]
    have h2 : (M : ℝ) ≤ t ^ 18 := hMle
    have h3 : t ^ 18 ≤ Real.sqrt (n : ℝ) / 4 := by
      rw [← ht24, le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
      have h6 : t ^ 18 * 4 ≤ t ^ 18 * t ^ 6 := mul_le_mul_of_nonneg_left h4 (by positivity)
      calc t ^ 18 * 4 ≤ t ^ 18 * t ^ 6 := h6
        _ = t ^ 24 := by ring
    linarith only [h2, h3]
  have hm142 : (142 : ℝ) ≤ (m : ℝ) := by
    have h2 : (2 : ℕ) ^ 142 ≤ (2 : ℕ) ^ 1000 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    have h3 : 142 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (h2.trans hbig)
    exact_mod_cast h3
  have hmass : (1 / (2304 * Real.log 2)) * Real.log (n : ℝ) ≤ ∑ q ∈ s, 1 / (q : ℝ) := by
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hblocks := GoldbachCount.mass_blocks (max D 1) J (by omega : 0 < max D 1)
    have hJge : (m : ℝ) / 144 ≤ (J : ℝ) := by
      have h1 : m ≤ 72 * J + 71 := by
        have h := Nat.div_add_mod m 72
        have hmod : m % 72 < 72 := Nat.mod_lt m (by norm_num)
        omega
      have h2 : (m : ℝ) ≤ 72 * (J : ℝ) + 71 := by exact_mod_cast h1
      linarith only [h2, hm142]
    have hlogn : Real.log (n : ℝ) ≤ 2 * (m : ℝ) * Real.log 2 := by
      have h1 : (n : ℝ) < (2 : ℝ) ^ (m + 1) := by
        have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
        exact_mod_cast h
      have h2 := Real.log_le_log hnpos h1.le
      rw [Real.log_pow] at h2
      push_cast at h2
      have h3 : ((m : ℝ) + 1) ≤ 2 * (m : ℝ) := by linarith only [hm142]
      have h4 : ((m : ℝ) + 1) * Real.log 2 ≤ (2 * (m : ℝ)) * Real.log 2 :=
        mul_le_mul_of_nonneg_right h3 (le_of_lt hlog2pos)
      linarith only [h2, h4]
    have hstep : (1 / (2304 * Real.log 2)) * Real.log (n : ℝ) ≤ (J : ℝ) / 8 := by
      have h4 : (1 / (2304 * Real.log 2)) * Real.log (n : ℝ) ≤ (1 / (2304 * Real.log 2)) * (2 * (m : ℝ) * Real.log 2) := by
        gcongr
      have h5 : (1 / (2304 * Real.log 2)) * (2 * (m : ℝ) * Real.log 2) = (m : ℝ) / 1152 := by
        field_simp
        ring
      linarith only [h4, h5, hJge]
    have h7 : GoldbachCount.mass (max D 1) (8 ^ J * max D 1) = ∑ q ∈ s, 1 / (q : ℝ) := rfl
    linarith only [hblocks, hstep, h7]
  have hscale := scaleDenominatorMass s n (1 / (2304 * Real.log 2)) (Real.log (n : ℝ)) hmass
  refine hscale.trans ?_
  have hcont : Continuous (GoldbachL2Arithmetic.primeSum n) := by
    unfold GoldbachL2Arithmetic.primeSum GoldbachL2Arithmetic.primeTerm GoldbachL2Arithmetic.E
    fun_prop
  refine GoldbachSupport.assembleShell s D H Q₂ H₂ n _ hcont (by omega : 0 < n) hDpos ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro q hq
    have h1 : max D 1 < q := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).1
    omega
  · intro q hq
    have hqle : (q : ℝ) ≤ t ^ 18 := by
      have h1 : (q : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).2
      linarith only [h1, hMle]
    have h6 : t ^ 18 ≤ 6 * t ^ 48 := by
      have h30 : (1 : ℝ) ≤ t ^ 30 := one_le_pow₀ ht1
      have h18 : (0 : ℝ) ≤ t ^ 18 := pow_nonneg (by linarith only [ht1]) 18
      have h1 : t ^ 18 ≤ t ^ 18 * t ^ 30 := by
        calc t ^ 18 = t ^ 18 * 1 := by ring
          _ ≤ t ^ 18 * t ^ 30 := mul_le_mul_of_nonneg_left h30 h18
      have h2 : t ^ 18 * t ^ 30 = t ^ 48 := by ring
      have h3 : (0 : ℝ) ≤ t ^ 48 := pow_nonneg (by linarith only [ht1]) 48
      nlinarith only [h1, h2, h3]
    have h7 : 6 * t ^ 48 = 6 * (n : ℝ) := by rw [ht48]
    linarith only [hqle, h6, h7]
  · intro q hq
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1
    have hqle : (q : ℝ) ≤ t ^ 18 := by
      have h1 : (q : ℝ) ≤ (M : ℝ) := by exact_mod_cast hhi
      linarith only [h1, hMle]
    have h1 : (q : ℝ) * (H : ℝ) ≤ t ^ 36 := by
      have h2 : (q : ℝ) * (H : ℝ) ≤ t ^ 18 * t ^ 18 := by gcongr
      have h3 : t ^ 18 * t ^ 18 = t ^ 36 := by ring
      linarith only [h2, h3]
    have h2 : (q : ℝ) * (D : ℝ) / 6 ≤ t ^ 34 / 6 := by
      have h3 : (q : ℝ) * (D : ℝ) / 6 ≤ t ^ 18 * t ^ 16 / 6 := by gcongr
      have h5 : t ^ 18 * t ^ 16 / 6 = t ^ 34 / 6 := by ring
      linarith only [h3, h5]
    have h4 : (0 : ℝ) < t := by linarith
    have h5 : (2 : ℝ) ≤ t ^ 12 := by
      have h : (16 : ℝ) ^ 12 ≤ t ^ 12 := pow_le_pow_left₀ (by norm_num) ht16 12
      nlinarith only [h]
    have h6 : t ^ 36 + t ^ 34 / 6 < t ^ 48 := by
      have hA : t ^ 34 / 6 ≤ t ^ 36 := by
        have h1 : (1 / 6 : ℝ) ≤ t ^ 2 := by nlinarith only [ht16]
        have h2 : t ^ 34 / 6 = t ^ 34 * (1 / 6) := by ring
        have h3 : t ^ 34 * (1 / 6) ≤ t ^ 34 * t ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (pow_nonneg (by linarith : (0 : ℝ) ≤ t) 34)
        have h4 : t ^ 34 * t ^ 2 = t ^ 36 := by ring
        linarith only [h2, h3, h4]
      have h5' : (2 : ℝ) < t ^ 12 := by
        have h6 : (16 : ℝ) ^ 12 ≤ t ^ 12 := pow_le_pow_left₀ (by norm_num) ht16 12
        nlinarith only [h6]
      have hB : (2 : ℝ) * t ^ 36 < t ^ 48 := by
        have h2 : (2 : ℝ) * t ^ 36 < t ^ 12 * t ^ 36 :=
          mul_lt_mul_of_pos_right h5' (pow_pos h4 36)
        have h3 : t ^ 12 * t ^ 36 = t ^ 48 := by ring
        linarith only [h2, h3]
      linarith only [hA, hB]
    have h9 : (n : ℝ) = t ^ 48 := by rw [ht48]
    linarith only [h1, h2, h6, h9]
  · intro q hq r hr
    have h1 : (q : ℝ) ≤ t ^ 18 := by
      have h2 : (q : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).2
      linarith only [h2, hMle]
    have h3 : (r : ℝ) ≤ t ^ 18 := by
      have h2 : (r : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hr).1).2
      linarith only [h2, hMle]
    have h4 : (q : ℝ) * (r : ℝ) ≤ t ^ 36 := by
      have h5 : (q : ℝ) * (r : ℝ) ≤ t ^ 18 * t ^ 18 := by gcongr
      have h6 : t ^ 18 * t ^ 18 = t ^ 36 := by ring
      linarith only [h5, h6]
    have h5 : (0 : ℝ) < t := by linarith
    have h6 : t ^ 36 < 6 * t ^ 48 := by
      have h7 : (1 : ℝ) ≤ t ^ 12 := one_le_pow₀ ht1
      have h8 : t ^ 36 * 1 ≤ t ^ 36 * t ^ 12 :=
        mul_le_mul_of_nonneg_left h7 (pow_nonneg (by linarith : (0 : ℝ) ≤ t) 36)
      have h9 : t ^ 36 * t ^ 12 = t ^ 48 := by ring
      have h11 : t ^ 36 ≤ t ^ 48 := by
        calc t ^ 36 = t ^ 36 * 1 := by ring
          _ ≤ t ^ 36 * t ^ 12 := h8
          _ = t ^ 48 := h9
      have h10 : (0 : ℝ) < t ^ 48 := pow_pos h5 48
      nlinarith only [h11, h10]
    have h8 : 6 * t ^ 48 = 6 * (n : ℝ) := by rw [ht48]
    linarith only [h4, h6, h8]
  · intro q hq
    have h1 : (q : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).2
    have h2 : (M : ℝ) ≤ (Q₂ : ℝ) := by exact_mod_cast hMleQ₂
    linarith only [h1, h2]
  · intro q hq
    have h1 : (q : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).2
    have h2 : (Q₂ : ℝ) ≤ (H₂ : ℝ) := by
      have h3 : (H₂ : ℝ) = 256 * (Q₂ : ℝ) * (l : ℝ) ^ 2 := by
        have hHH : H₂ = 256 * Q₂ * l ^ 2 := rfl
        rw [hHH]
        push_cast
        ring
      have h1l : (1 : ℝ) ≤ (l : ℝ) := by
        have h : 1 ≤ l := Nat.le_log_of_pow_le (by norm_num) (by omega : 2 ≤ n + 2)
        exact_mod_cast h
      have h4 : (1 : ℝ) ≤ 256 * (l : ℝ) ^ 2 := by nlinarith only [h1l]
      have h6 : (0 : ℝ) ≤ (Q₂ : ℝ) := by positivity
      nlinarith only [h3, h4, h6]
    have h7 : (M : ℝ) ≤ (Q₂ : ℝ) := by exact_mod_cast hMleQ₂
    linarith only [h1, h7, h2]
  · intro q hq h hh
    have hsq : Squarefree q := (Finset.mem_filter.mp hq).2
    have hqleL : q ≤ ⌊Real.sqrt (n : ℝ) / 4⌋₊ := by
      have h1 : q ≤ M := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).2
      exact h1.trans hMleL
    exact GoldbachL2Arithmetic.reduced_amplitude n q (by omega) hsq hθ (hqlog q hqleL) h hh.1 hh.2

end ShellCount

end

end Conjectures.Goldbach.SqrtShellSecondMomentFloor

open Conjectures.Goldbach.SqrtArcSecondMomentFloor in
theorem Conjectures.Goldbach.SqrtShellSecondMomentFloor :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let Q₂ := fun n : ℕ => ⌊Real.sqrt (n : ℝ) / ((Nat.log 2 (n + 2) : ℝ) ^ 4)⌋₊; let sqrtArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q₂ n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ ((256 * Q₂ n * Q n : ℕ) : ℝ) / ((q : ℝ) * (n : ℝ))}; ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c * (n : ℝ) * Real.log (n : ℝ) ≤ intervalIntegral (fun t => (sqrtArcs n \ wideArcs n).indicator (fun u => ‖S n w u‖ ^ 2) t) (0 : ℝ) 1 MeasureTheory.volume := by
  obtain ⟨c, hc, N, hN⟩ := Conjectures.Goldbach.SqrtShellSecondMomentFloor.ShellCount.main_bound
  refine ⟨c, hc, N, fun n hn => ?_⟩
  simpa only [Conjectures.Goldbach.SqrtShellSecondMomentFloor.ShellCount.maskD,
    Conjectures.Goldbach.SqrtShellSecondMomentFloor.ShellCount.logSquare,
    Conjectures.Goldbach.SqrtShellSecondMomentFloor.ShellCount.maskH,
    Conjectures.Goldbach.SqrtShellSecondMomentFloor.ShellCount.shellD,
    Conjectures.Goldbach.SqrtShellSecondMomentFloor.ShellCount.shellH,
    GoldbachSupport.publishedWideArcs, GoldbachL2Arithmetic.primeSum_eq_catalogue,
    GoldbachL2Arithmetic.E] using hN n hn