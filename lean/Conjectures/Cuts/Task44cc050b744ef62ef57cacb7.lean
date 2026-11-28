import Mathlib
import Conjectures.Goldbach.EstermannAlmostAllPolylog

namespace GoldbachCentralDyadic

open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachMajorArc Finset MeasureTheory

/-- With the twist centered at the length D, replacing the scale in the widths
by N costs no kernel mass at the origin as long as N is at most six times D. -/
theorem narrow_model_floor (N D Q : ℕ) (hD : 0 < D) (hDN : D ≤ N)
    (hND : N ≤ 6 * D) (hQ : 1 ≤ Q) (hdis : 2 * Q ≤ D) (heven : Even N) :
    (D : ℝ) / 72 ≤ ∑ q ∈ Icc 1 Q, (coefficient q N).re *
      ∫ t in -(blockWidth N Q q)..blockWidth N Q q,
        (GoldbachEstermannKernel.twisted D D t).re := by
  let W (q : ℕ) := if q ≤ Q then kernelMass D (blockWidth N Q q) else 0
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hD.trans_le hDN
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hQr : 1 ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hwr (q : ℕ) : 0 ≤ blockWidth N Q q := by unfold blockWidth; positivity
  have hnon (q : ℕ) : 0 ≤ W q := by
    dsimp only [W]; split_ifs
    · apply intervalIntegral.integral_nonneg (by linarith [hwr q])
      intro t _
      exact sq_nonneg _
    · rfl
  have hmono (i j : ℕ) (hi : 0 < i) (hij : i ≤ j) : W j ≤ W i := by
    by_cases hj : j ≤ Q
    · simp only [W, ite_eq_left hj, ite_eq_left (hij.trans hj)]
      apply kernelMass_mono (hwr j)
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos (by exact_mod_cast hi) hNr)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hNr.le
    · simp only [W, ite_eq_right hj]
      exact hnon i
  have hs := arithmetic_floor (Q := Q) heven W hnon hmono
    (by intro q hq; simp [W, not_le.mpr hq])
  have h1 : 1 / (6 * (D : ℝ)) ≤ blockWidth N Q 1 := by
    unfold blockWidth
    simp only [Nat.cast_one, one_mul]
    rw [div_le_div_iff₀ (by positivity) hNr]
    have hND' : (N : ℝ) ≤ 6 * D := by exact_mod_cast hND
    nlinarith [mul_le_mul_of_nonneg_right hQr hDr.le]
  rw [show W 1 = kernelMass D (blockWidth N Q 1) by simp [W, hQ]] at hs
  have hmodel : (D : ℝ) / 72 ≤ ∑ q ∈ Icc 1 Q, (coefficient q N).re * W q := by
    linarith [kernelMass_floor hD h1]
  apply hmodel.trans_eq
  apply sum_congr rfl
  intro q hq
  congr 1
  rw [show W q = kernelMass D (blockWidth N Q q) by simp [W, (mem_Icc.mp hq).2]]
  have hle : blockWidth N Q q ≤ 1/2 := by
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast (mem_Icc.mp hq).1
    have hdis' : 2 * (Q : ℝ) ≤ N := by exact_mod_cast hdis.trans hDN
    unfold blockWidth
    apply (div_le_iff₀ (mul_pos (by linarith) hNr)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hq' hNr.le]
  obtain ⟨hlo, hhi⟩ := GoldbachEstermannKernel.loss_on_interval D D le_rfl
    (neg_le_neg hle) (by linarith [hwr q] : -(blockWidth N Q q) ≤ blockWidth N Q q) hle
  change kernelMass D (blockWidth N Q q) - _ ≤ (D : ℝ) - D at hhi
  change 0 ≤ kernelMass D (blockWidth N Q q) - _ at hlo
  linarith

end GoldbachCentralDyadic

namespace CentralNarrow

open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachMajorArc BulkCircle Finset Filter MeasureTheory
open scoped Topology

-- Adapted from BulkCircle.major_error in the Apache-2.0 EstermannAlmostAllPolylog
-- community proof. The integral of the norm on each narrow arc is bounded
-- by the corresponding integral on the original, wider arc.
theorem major_error {n Q L D : ℕ} (hx : n ≤ 64*D) (hL : 0 < L) (hux : L+D+1 ≤ n)
    (hn : n = D+2*(L+1)) (hsep : 2*Q^2 < n) (hQ : 1 ≤ Q) {E : ℝ} (hE0 : 0 ≤ E)
    (hE : ∀ q a : ℕ, 0 < q → q ≤ Q → prefixError n ((a:ℝ)/q) (unitMean q a) ≤ q*E) :
    (∑ q ∈ Icc 1 Q, (coefficient q n).re *
      ∫ β in -(blockWidth n Q q)..blockWidth n Q q, (GoldbachEstermannKernel.twisted D D β).re) -
      (GoldbachBlockGeometry.majorContribution Q n (integrand L D n)).re ≤ 2048000*(Q:ℝ)^4*E := by
  let C (q a : ℕ) := unitMean q a ^ 2 * phase (-(n:ℝ)*GoldbachBlockGeometry.center q a)
  let K := GoldbachEstermannKernel.twisted D D
  have hC : C 1 0 = C 1 1 := by
    have hu (a : ℕ) : unitMean 1 a = 1 := by rw [unitMean_eq_ram (by simp),ram_one]; simp
    have hz : phase 0 = 1 := by simp [phase]
    have hint : phase (-(n:ℝ)) = 1 := by
      unfold phase
      convert Complex.exp_int_mul_two_pi_mul_I (-(n:ℤ)) using 2
      push_cast
      ring
    simp [C,hu,GoldbachBlockGeometry.center,hz,hint]
  have hF : Continuous (integrand L D n) := by unfold integrand S primeSum phase; fun_prop
  have hK : Continuous K := by
    unfold K GoldbachEstermannKernel.twisted GoldbachEstermannKernel.kernel GoldbachEstermannKernel.phase
    fun_prop
  have h := GoldbachBlockGeometry.major_error (integrand L D n) K hF hK C hC hsep
  have hcoef (q : ℕ) : (∑ a ∈ (range q).filter (fun a => a.Coprime q), C q a) = coefficient q n :=
    sum_centers_eq_coefficient q n
  simp_rw [hcoef] at h
  let model := ∑ q ∈ Icc 1 Q, coefficient q n * ∫ β in -(blockWidth n Q q)..blockWidth n Q q, K β
  have ht (q a : ℕ) (t : ℝ) : ‖integrand L D n (GoldbachBlockGeometry.center q a + t)-C q a*K t‖ =
      ‖S L D ((a:ℝ)/q+t)^2-(unitMean q a*U L D t)^2‖ := remove_phase q a L D n D hn t
  simp_rw [ht] at h
  have hreal : model.re = (∑ q ∈ Icc 1 Q, (coefficient q n).re *
      ∫ β in -(blockWidth n Q q)..blockWidth n Q q, (K β).re) := by
    unfold model
    rw [Complex.re_sum]
    apply sum_congr rfl
    intro q hq
    rw [Complex.mul_re, coefficient_im_zero n (by have := (mem_Icc.mp hq).1; omega),
      zero_mul, sub_zero]
    exact congrArg ((coefficient q n).re * ·)
      (intervalIntegral.intervalIntegral_re (𝕜 := ℂ) (hK.intervalIntegrable _ _)).symm
  rw [← hreal]
  have hr := Complex.re_le_norm (model - GoldbachBlockGeometry.majorContribution Q n (integrand L D n))
  rw [Complex.sub_re, norm_sub_rev] at hr
  apply hr.trans
  apply h.trans
  apply le_trans _ (total_squared hx hL hux hQ hE0 hE)
  apply sum_le_sum
  intro q hq
  apply sum_le_sum
  intro a _
  have hqr : (0:ℝ) < q := by exact_mod_cast (show 0 < q from (mem_Icc.mp hq).1)
  have hDr : (0:ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hwidth : blockWidth n Q q ≤ blockWidth D Q q := by
    unfold blockWidth
    apply div_le_div_of_nonneg_left (by positivity) (mul_pos hqr hDr)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show D ≤ n by omega)) hqr.le
  have hnw : 0 ≤ blockWidth n Q q := by unfold blockWidth; positivity
  apply intervalIntegral.integral_mono_interval (neg_le_neg hwidth) (by linarith only [hnw]) hwidth
  · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
  · apply Continuous.intervalIntegrable
    unfold S U primeSum kernel phase
    fun_prop

end CentralNarrow

namespace DyadicCentralMajor
open Finset Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachMajorArc

theorem central_window_sum (n : ℕ) (hn : 4 ≤ n) (t : ℝ) :
    (∑ p ∈ range (n+1), ((if n ≤ 3*p ∧ 3*p ≤ 2*n ∧ p.Prime then Real.log (p:ℝ) else 0 : ℝ) : ℂ) *
      phase ((p:ℝ)*t)) =
    BulkCircle.S ((n+2)/3 - 1) (n-2*((n+2)/3)) t := by
  let c := (n+2)/3
  let d := n-2*c
  let f (p : ℕ) : ℂ := (primeWeight p : ℂ) * phase ((p:ℝ)*t)
  have hc : 1 ≤ c := by dsimp [c]; omega
  have hu : c+d = 2*n/3 := by dsimp [c,d]; omega
  have hge : c ≤ c+d+1 := by omega
  have hS : BulkCircle.S (c-1) d t = ∑ p ∈ Ico c (c+d+1), f p := by
    rw [Finset.sum_Ico_eq_sub _ hge]
    dsimp only [BulkCircle.S,primeSum,f]
    rw [show c-1+d+1+1=c+d+1 by omega, show c-1+1=c by omega]
  change _ = BulkCircle.S (c-1) d t
  rw [hS]
  have hset : ((range (n+1)).filter fun p => n ≤ 3*p ∧ 3*p ≤ 2*n) = Ico c (c+d+1) := by
    ext p
    simp only [mem_filter,mem_range,mem_Ico]
    rw [show c+d+1=(2*n)/3+1 by omega]
    dsimp only [c]
    omega
  rw [←hset,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hc1 : n ≤ 3*p <;> by_cases hc2 : 3*p ≤ 2*n <;> by_cases hp' : p.Prime <;>
    simp [hc1,hc2,hp',f,primeWeight]

end DyadicCentralMajor

open Filter
open scoped Topology
namespace CentralNarrow

private theorem small_cutoff (Q : ℕ → ℕ)
    (hQ : ∀ n ≥ 2, (Q n : ℝ) ≤ (4 * Real.log n)^2) :
    ∀ᶠ n in atTop, 12 * (Q n)^2 < n := by
  have hlog : Tendsto (fun n : ℕ => (Real.log n)^4 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_natCast, Real.rpow_one] using
      ((isLittleO_log_rpow_rpow_atTop (4:ℕ) (by norm_num : (0:ℝ) < 1)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [hlog.eventually_lt_const (by norm_num : (0:ℝ)<1/4096),
    eventually_ge_atTop (2:ℕ)] with n h hn
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  change (Real.log n)^4 / (n : ℝ) < 1/4096 at h
  have h₁ := (div_lt_iff₀ hn').mp h
  have h₂ := pow_le_pow_left₀ (Nat.cast_nonneg (Q n) (α := ℝ)) (hQ n hn) 2
  exact_mod_cast (show 12 * (Q n : ℝ)^2 < n by nlinarith only [h₁,h₂,hn'])

end CentralNarrow

namespace CentralNarrow
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachMajorArc Filter
open scoped Topology

theorem eventual_central :
    ∀ᶠ n : ℕ in atTop, Even n →
      let L := (n+2)/3 - 1
      let D := n - 2*((n+2)/3)
      (1/1000 : ℝ) * n ≤
        (GoldbachBlockGeometry.majorContribution (Polylog.cutoff 2 n) n (BulkCircle.integrand L D n)).re := by
  obtain ⟨M,hM,hpre⟩ := Polylog.uniform_prefix_error 2 8 (by decide)
  let C : ℝ := 2048000 * (4^2)^4
  have hlim := (Polylog.envelope_saving 2 8 M).const_mul C
  simp only [mul_zero] at hlim
  have hsmall := small_cutoff (Polylog.cutoff 2) (fun n hn => Polylog.cutoff_le_log 2 hn)
  filter_upwards [hpre, hlim.eventually_lt_const (by norm_num : (0:ℝ)<1/1000),
    hsmall, eventually_ge_atTop (24:ℕ)] with n hp herr hs hn
  intro heven L D
  let Q := Polylog.cutoff 2 n
  have hQ : 1 ≤ Q := pow_pos (Nat.log_pos (by decide : 1<2) (by omega : 2≤n+2)) _
  change 12*Q^2 < n at hs
  have hND : n ≤ 6*D := by dsimp [D]; omega
  have hDN : D ≤ n := Nat.sub_le _ _
  have hL : 0<L := by dsimp [L]; omega
  have hux : L+D+1 ≤ n := by dsimp [L,D]; omega
  have hmode : n = D+2*(L+1) := by dsimp [L,D]; omega
  have hsep : 2*Q^2<n := by omega
  have hdis : 2*Q ≤ D := by
    have hq2 : Q ≤ Q^2 := Nat.le_self_pow (by decide : 2≠0) Q
    omega
  let env := Polylog.errorEnvelope 2 8 M n
  have hE : 0 ≤ env := by unfold env Polylog.errorEnvelope; positivity
  have hlow := GoldbachCentralDyadic.narrow_model_floor n D Q (by omega) hDN hND hQ hdis heven
  have happ := CentralNarrow.major_error (by omega : n ≤ 64*D) hL hux hmode hsep hQ hE hp
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) Q)
    (Polylog.cutoff_le_log 2 (by omega : 2 ≤ n)) 4
  have hcomp : (Q:ℝ)^4 ≤ (4^2)^4 * (Real.log n)^8 := by
    calc
      _ ≤ ((4 * Real.log n)^2)^4 := hpow
      _ = _ := by ring
  have hnr : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  change C * (((Real.log n)^8*env)/(n:ℝ)) < _ at herr
  rw [← mul_div_assoc, div_lt_iff₀ hnr] at herr
  dsimp [C] at herr
  have hnrD : (n:ℝ) ≤ 6*(D:ℝ) := by exact_mod_cast hND
  have hcost := mul_le_mul_of_nonneg_right hcomp hE
  nlinarith only [happ, hlow, herr, hcost, hnrD, hnr]

end CentralNarrow

open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux

theorem Conjectures.Cuts.Task44cc050b744ef62ef57cacb7 : (have x1 : ℝ → ℂ := fun (x1 : ℝ) => Complex.exp (↑((2 : ℝ) * Real.pi * x1) * Complex.I); have x2 : ℕ → ℕ → ℝ := fun (x2 x3 : ℕ) => if x2 ≤ (3 : ℕ) * x3 ∧ (3 : ℕ) * x3 ≤ (2 : ℕ) * x2 ∧ Nat.Prime x3 then Real.log ↑x3 else (0 : ℝ); have x3 : ℕ → ℕ := fun (x3 : ℕ) => Nat.log (2 : ℕ) (x3 + (2 : ℕ)) ^ (2 : ℕ); have x4 : ℕ → Set ℝ := fun (x4 : ℕ) => {x5 : ℝ | ∃ (x6 : ℕ) (x7 : ℕ), (1 : ℕ) ≤ x6 ∧ x6 ≤ x3 x4 ∧ x7 ≤ x6 ∧ x7.Coprime x6 ∧ |x5 - ↑x7 / ↑x6| ≤ ↑(x3 x4) / (↑x6 * ↑x4)}; have x5 : ℕ → ℝ → ℂ := fun (x5 : ℕ) (x6 : ℝ) => (∑ x7 ∈ Finset.range (x5 + (1 : ℕ)), ↑(x2 x5 x7) * x1 (↑x7 * x6)) ^ (2 : ℕ) * x1 (-↑x5 * x6); ∃ (x6 : ℝ),   (0 : ℝ) < x6 ∧     ∃ (x7 : ℕ),       ∀ x8 ≥ x7,         have x10 : ℕ := (2 : ℕ) ^ x8;         x6 * ↑x10 ≤ (intervalIntegral ((x4 x10).indicator (x5 x10)) (0 : ℝ) (1 : ℝ) MeasureTheory.MeasureSpace.volume).re) := by
  intro E W Q A F
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp CentralNarrow.eventual_central
  refine ⟨1/1000, by norm_num, max N 4, ?_⟩
  intro k hk n
  have hk4 : 4 ≤ k := (le_max_right N 4).trans hk
  have hkn : k < n := by
    dsimp [n]
    exact Nat.lt_two_pow_self
  have hnN : N ≤ n := (le_max_left N 4).trans (hk.trans hkn.le)
  have he : Even n := by
    exact (even_two.pow_of_ne_zero (by omega : k ≠ 0))
  have h := hN n hnN he
  have hfun : F n = BulkCircle.integrand ((n+2)/3-1) (n-2*((n+2)/3)) n := by
    funext t
    change (∑ p ∈ Finset.range (n+1),
      ((if n ≤ 3*p ∧ 3*p ≤ 2*n ∧ p.Prime then Real.log (p:ℝ) else 0 : ℝ) : ℂ) *
        GoldbachMajorArc.phase ((p:ℝ)*t))^2 * GoldbachMajorArc.phase (-(n:ℝ)*t) = _
    rw [DyadicCentralMajor.central_window_sum n (by omega)]
    rfl
  rw [hfun]
  exact h
