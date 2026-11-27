import Conjectures.Goldbach.SqrtArcSecondMomentFloor
import Conjectures.Goldbach.ThreeQuartersExceptionalDirichletWindows

/-! A lower count of reduced rational windows meeting the three-quarters
threshold. The Ramanujan amplitude and squarefree block count come from
the square-root exterior second-moment proof, and the sampling inequality
and prime energy from the published upper count for Dirichlet windows. -/

namespace Conjectures.Goldbach.ThreeQuartersWindowLower

open Finset Filter
open Conjectures.Goldbach.SqrtArcSecondMomentFloor
open GoldbachSupport GoldbachL2Arithmetic GoldbachMovingWindows
open scoped BigOperators Topology

private theorem series_eq_primeSum (n : ℕ) (t : ℝ) : series n primeLog t = primeSum n t := by
  rw [primeSum_eq_catalogue]
  simp only [series,primeLog,wave_eq,E]

private theorem high_sum {ι : Type*} (R : Finset ι) (z : ι → ℂ) {n D : ℝ}
    (hn : 0 < n) (hD : 0 < D) (hcard : (R.card : ℝ) ≤ 8*D)
    (hamp : n/8 ≤ ‖∑ a ∈ R, z a‖) :
    n/16 ≤ ∑ a ∈ R.filter (fun a => n/(128*D) ≤ ‖z a‖), ‖z a‖ := by
  classical
  let b := n/(128*D)
  have h : ∑ a ∈ R, ‖z a‖ ≤ ∑ a ∈ R, ((if b ≤ ‖z a‖ then ‖z a‖ else 0)+b) := by
    apply sum_le_sum
    intro i _
    split_ifs with hi
    · exact le_add_of_nonneg_right (by dsimp [b]; positivity)
    · simp only [zero_add]; exact le_of_not_ge hi
  rw [sum_add_distrib, ← sum_filter, sum_const, nsmul_eq_mul] at h
  have hsmall : (R.card : ℝ)*b ≤ n/16 := calc
    _ ≤ (8*D)*b := mul_le_mul_of_nonneg_right hcard (by dsimp [b]; positivity)
    _ = _ := by dsimp [b]; field_simp; ring
  change n/16 ≤ ∑ a ∈ R.filter (fun a => b ≤ ‖z a‖), ‖z a‖
  linarith only [h, hsmall, hamp.trans (norm_sum_le _ _)]

noncomputable def WConstant : ℝ := 128^2 * GoldbachMovingWindows.windowConstant

/-- A lower count in the denominator block (D,8D], at the rational centres. -/
theorem block_lower : ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, 0 < D → 32*(D : ℝ) ≤ Real.sqrt n →
    ∃ P : Finset (ℕ×ℕ),
      (∀ p ∈ P, D < p.1 ∧ p.1 ≤ 8*D ∧ Squarefree p.1 ∧ p.2 < p.1 ∧ p.2.Coprime p.1 ∧
        (n : ℝ)/(128*D) ≤ ‖primeSum n ((p.2 : ℝ)/p.1)‖) ∧
      (D : ℝ)^2 ≤ WConstant*(P.card : ℝ)*Real.log n := by
  classical
  filter_upwards [primeAmplitudeBounds] with n hprime
  obtain ⟨hn,hθ,hlog⟩ := hprime
  intro D hd hcut
  have hn0 : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hd
  let s := (Ioc D (8*D)).filter Squarefree
  have hq {q : ℕ} (h : q ∈ s) : (D < q ∧ q ≤ 8*D) ∧ Squarefree q := by simpa [s] using h
  have hmass : (1/8 : ℝ) ≤ ∑ q ∈ s, 1/(q : ℝ) := by
    simpa [s,GoldbachCount.mass] using GoldbachCount.mass_blocks D 1 hd
  have hnum : (D : ℝ)/8 ≤ s.card := by
    have hu : ∑ q ∈ s, 1/(q : ℝ) ≤ ∑ _q ∈ s, 1/(D : ℝ) := by
      apply sum_le_sum
      intro q h
      exact one_div_le_one_div_of_le hDR (by exact_mod_cast (hq h).1.1.le)
    rw [sum_const,nsmul_eq_mul,mul_one_div] at hu
    have hr := (le_div_iff₀ hDR).1 (hmass.trans hu)
    linarith only [hr]
  let R := fun q : ℕ => (range q).filter (fun a => a.Coprime q)
  let t := fun p : ℕ×ℕ => (p.2 : ℝ)/p.1
  let v := fun p : ℕ×ℕ => ‖primeSum n (t p)‖
  let B := (n : ℝ)/(128*D)
  let G := fun q : ℕ => (R q).filter (fun a => B ≤ v (q,a))
  let P := (s ×ˢ range (8*D)).filter (fun p => p.2 ∈ G p.1)
  have memG {q a : ℕ} (h : a ∈ G q) : (a < q ∧ a.Coprime q) ∧ B ≤ v (q,a) := by
    simpa [G,R] using h
  have good (p : ℕ×ℕ) (h : p ∈ P) : D < p.1 ∧ p.1 ≤ 8*D ∧ Squarefree p.1 ∧
      p.2 < p.1 ∧ p.2.Coprime p.1 ∧ B ≤ v p := by
    obtain ⟨hI,hG⟩ := mem_filter.mp h
    obtain ⟨hblock,hsq⟩ := hq (mem_product.mp hI).1
    obtain ⟨⟨ha,hc⟩,hv⟩ := memG hG
    exact ⟨hblock.1,hblock.2,hsq,ha,hc,hv⟩
  refine ⟨P,good,?_⟩
  have hfit : 8*D ≤ ⌊Real.sqrt n/4⌋₊ := by apply Nat.le_floor; push_cast; linarith only [hcut]
  have row (q : ℕ) (hm : q ∈ s) : (n : ℝ)/16 ≤ ∑ a ∈ G q, v (q,a) := by
    apply high_sum (R q) (fun a => primeSum n ((a : ℝ)/q)) hnR hDR
    · exact_mod_cast ((Finset.card_filter_le ..).trans_eq (Finset.card_range q)).trans (hq hm).1.2
    · simpa only [add_zero] using reduced_amplitude n q hn0 (hq hm).2 hθ
        (hlog q ((hq hm).1.2.trans hfit)) 0 le_rfl (by positivity)
  have htotal : ((D : ℝ)*n)/128 ≤ ∑ p ∈ P, v p := calc
    _ ≤ (s.card : ℝ)*((n : ℝ)/16) := by nlinarith only [mul_le_mul_of_nonneg_right hnum hnR.le]
    _ = ∑ _q ∈ s, (n : ℝ)/16 := by simp
    _ ≤ ∑ q ∈ s, ∑ a ∈ G q, v (q,a) := sum_le_sum row
    _ = _ := by
      dsimp only [P]
      conv_rhs => rw [sum_filter, sum_product]
      apply sum_congr rfl
      intro q h
      conv_rhs => rw [← sum_filter]
      congr 1
      ext a
      simpa only [mem_filter,mem_range,iff_and_self] using
        (show a ∈ G q → a < 8*D from fun ha => (memG ha).1.1.trans_le (hq h).1.2)
  have hS := moving_large_sieve hn0 primeLog P t (by
    intro p hp
    obtain ⟨hl,hu,_,ha,hc,_⟩ := good p hp
    have hpos : 0 < p.1 := by omega
    have hqR : 0 < (p.1 : ℝ) := by exact_mod_cast hpos
    have hu' : (p.1 : ℝ) ≤ 8*(D : ℝ) := by exact_mod_cast hu
    refine ⟨hpos,by linarith only [hu',hcut,hDR],hc,⟨by dsimp [t]; positivity,?_⟩,?_⟩
    · exact (div_le_one hqR).2 (by exact_mod_cast ha.le)
    · simp only [t,sub_self,abs_zero]; positivity)
  simp only [series_eq_primeSum] at hS
  have hupper : ∑ p ∈ P, v p ^ 2 ≤ GoldbachMovingWindows.windowConstant*(n : ℝ)^2*Real.log n := calc
    _ ≤ _ := hS
    _ ≤ 7*(1+4*Real.pi)*(n : ℝ) * (Real.log 4*n*Real.log n) := by
      exact mul_le_mul_of_nonneg_left (primeLog_energy n) (by positivity)
    _ = _ := by unfold GoldbachMovingWindows.windowConstant; ring
  have hlower := (pow_le_pow_left₀ (show 0 ≤ ((D : ℝ)*n)/128 by positivity) htotal 2).trans
    (sq_sum_le_card_mul_sum_sq (s := P) (f := v))
  have hfinal := hlower.trans (mul_le_mul_of_nonneg_left hupper (Nat.cast_nonneg _))
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hnR)).1
  dsimp [WConstant]
  linarith only [hfinal]

theorem sharp_lower : ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 ≤ η → η < 1/4 →
    ∃ N : ℕ, ∀ n ≥ N, ∃ P : Finset (ℕ×ℕ),
      (∀ p ∈ P, (n : ℝ)^(1/4-η)/256 < p.1 ∧ (p.1 : ℝ) ≤ (n : ℝ)^(1/4-η)/16 ∧
        Squarefree p.1 ∧ p.2 < p.1 ∧ p.2.Coprime p.1 ∧
        (n : ℝ)^(3/4+η) ≤ ‖primeSum n ((p.2 : ℝ)/p.1)‖) ∧
      c*(n : ℝ)^(1/2-2*η) ≤ (P.card : ℝ)*Real.log n := by
  have hC : 0 < WConstant := by unfold WConstant GoldbachMovingWindows.windowConstant; positivity
  refine ⟨1/(256^2*WConstant),by positivity,?_⟩
  intro η hη hup
  have hlim : Tendsto (fun n : ℕ => (n : ℝ)^(1/4-η)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hup)).comp tendsto_natCast_atTop_atTop
  apply eventually_atTop.1
  filter_upwards [block_lower, hlim.eventually_ge_atTop 256, eventually_ge_atTop (2 : ℕ)] with n hblock hlarge hn
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hpos : 0 < (n : ℝ) := zero_lt_one.trans_le hnR
  let Y := (n : ℝ)^(1/4-η)
  let D := ⌊Y/128⌋₊
  change 256 ≤ Y at hlarge
  have hdhi : (D : ℝ) ≤ Y/128 := Nat.floor_le (by dsimp [Y]; positivity)
  have hdlo : Y/256 ≤ (D : ℝ) := by
    have near := Nat.lt_floor_add_one (Y/128)
    change Y/128 < (D : ℝ)+1 at near
    linarith only [near,hlarge]
  have hd : 0 < D := by exact_mod_cast (show 0 < (D : ℝ) by linarith only [hdlo,hlarge])
  have hyroot : Y ≤ Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hnR (by linarith only [hη])
  obtain ⟨P,hP,hcount⟩ := hblock D hd (by linarith only [hyroot,hdhi,hlarge])
  have hmul : (n : ℝ)^(3/4+η)*Y = n := by
    dsimp [Y]
    rw [← Real.rpow_add hpos, show (3/4:ℝ)+η+(1/4-η)=1 by ring,Real.rpow_one]
  have hthreshold : (n : ℝ)^(3/4+η) ≤ (n : ℝ)/(128*D) := by
    apply (le_div_iff₀ (by positivity)).2
    exact (mul_le_mul_of_nonneg_left (by linarith only [hdhi] : 128*(D : ℝ) ≤ Y)
      (Real.rpow_nonneg hpos.le _)).trans_eq hmul
  refine ⟨P,?_,?_⟩
  · intro p hp
    obtain ⟨hl,hu,hsq,ha,hcop,hpeak⟩ := hP p hp
    have hu' : (p.1 : ℝ) ≤ 8*(D : ℝ) := by exact_mod_cast hu
    exact ⟨hdlo.trans_lt (by exact_mod_cast hl),by linarith only [hu',hdhi],hsq,ha,hcop,hthreshold.trans hpeak⟩
  · have hy2 : Y^2 = (n : ℝ)^(1/2-2*η) := by
      dsimp [Y]
      rw [← Real.rpow_mul_natCast hpos.le]; congr 1; ring
    have hs := pow_le_pow_left₀ (by dsimp [Y]; positivity : 0 ≤ Y)
      (by linarith only [hdlo] : Y ≤ 256*(D : ℝ)) 2
    rw [← hy2, one_div_mul_eq_div, div_le_iff₀ (by positivity)]
    linarith only [hs, mul_le_mul_of_nonneg_left hcount (by norm_num : (0 : ℝ) ≤ 256^2)]

end Conjectures.Goldbach.ThreeQuartersWindowLower

open Conjectures.Goldbach.ThreeQuartersWindowLower Conjectures.Goldbach.SqrtArcSecondMomentFloor in
/-- Reduced rational centres attain the upper bound's power of n, up to logarithmic factors. -/
theorem Conjectures.Goldbach.ThreeQuartersWindowLower :
    let w := fun k : ℕ => if k.Prime then Real.log (k : ℝ) else 0
    let E := fun t : ℝ => Complex.exp (((2*Real.pi*t : ℝ) : ℂ)*Complex.I)
    let S := fun (n : ℕ) (t : ℝ) => ∑ k ∈ Finset.range (n+1), (w k : ℂ)*E ((k : ℝ)*t)
    ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 ≤ η → η < 1/4 → ∃ N : ℕ, ∀ n ≥ N, ∃ P : Finset (ℕ×ℕ),
      (∀ p ∈ P, (n : ℝ)^(1/4-η)/256 < p.1 ∧ (p.1 : ℝ) ≤ (n : ℝ)^(1/4-η)/16 ∧
        Squarefree p.1 ∧ p.2 < p.1 ∧ p.2.Coprime p.1 ∧
        (n : ℝ)^(3/4+η) ≤ ‖S n ((p.2 : ℝ)/p.1)‖) ∧
      c*(n : ℝ)^(1/2-2*η) ≤ (P.card : ℝ)*Real.log n := by
  simpa only [GoldbachL2Arithmetic.primeSum_eq_catalogue,GoldbachL2Arithmetic.E] using sharp_lower
