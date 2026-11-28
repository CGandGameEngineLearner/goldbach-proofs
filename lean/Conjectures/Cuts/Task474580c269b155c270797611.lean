import Mathlib
import Conjectures.Goldbach.BeaumontOneSidedHoleCluster

/-!
Adapted from `Conjectures.Goldbach.BeaumontOneSidedHoleCluster` (accepted module
L-goldbach-beaumont-one-sided-hole-cluster): the same cell-local minor-arc chain
with every polylog margin exponent scaled by a free parameter `m ≥ 1`.
-/

open Finset Filter MeasureTheory
open scoped BigOperators Topology
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachBeaumontParameters GoldbachBeaumont GoldbachBeaumontMainArc
open GoldbachBeaumontFourier GoldbachBeaumontCompletion GoldbachBeaumontHigh
open GoldbachBeaumontSharpBoxes BeaumontHighScales GoldbachBeaumontFinish

namespace Conjectures.Cuts.Task474580c269b155c270797611_aux

/-! ### Parametric polylog margins (all polylog exponents scaled by `m ≥ 1`).
For `m = 1` these are literally the accepted module's `denominatorCutoff`,
`approximationBound`, `lowerFactor`, `upperFactor`. -/

def denCutM (m X : ℕ) : ℕ := logScale X ^ (1000 * m)
def appBoundM (m X : ℕ) : ℕ := window X / logScale X ^ (2000 * m)
def progWinM (m X : ℕ) : ℕ := appBoundM m X / 24
def lowFacM (m X : ℕ) : ℕ := logScale X ^ (101 * m)
def upFacM (m X : ℕ) : ℕ := physicalWindow X / logScale X ^ (100 * m)
def majCutM (m X : ℕ) : ℕ := logScale X ^ (18 * m)
noncomputable def pktRadM (m X : ℕ) : ℝ :=
  1 / (appBoundM m X : ℝ) + 1 / (window X : ℝ)
def majArcsM (m X : ℕ) : Set ℝ :=
  GoldbachBlockGeometry.arcs (majCutM m X) (centralWidth X)

/-! ### Interfaces -/

/-- Parametric form of `GoldbachBeaumontCompletion.eventually_typeII_cells`. -/
def typeIICellBound (m : ℕ) : Prop :=
  ∀ᶠ X : ℕ in Filter.atTop, ∀ C ≤ scale X, ∀ j < 3,
    ∀ b ∈ activeChoices (scale X) (mobiusCutoff X) j (Finset.Ioc 0 C),
    ∀ α : ℝ, ∀ a q : ℕ,
    denCutM m X < q →
    q ≤ appBoundM m X → a.Coprime q →
    |α - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * (appBoundM m X : ℝ)) →
    (∃ t ⊆ (slots j).attach,
      (lowFacM m X : ℝ) ≤ ∏ i ∈ t, upper j b i ∧
      (∏ i ∈ t, upper j b i) ≤ (upFacM m X : ℝ)) →
    (∫ θ in α..(α + 1 / (window X : ℝ)),
      ‖boxPrefix (mobiusCutoff X) j b C θ‖ ^ 2) ≤
      (scale X : ℝ) / (logScale X : ℝ) ^ (30 * m)

/-- Parametric form of `GoldbachBeaumontCompletion.residualCells`. -/
def residualCellBound (m : ℕ) : Prop :=
  ∀ᶠ X : ℕ in Filter.atTop, ∀ C ≤ scale X, ∀ j < 3, ∀ b : Choice j,
    ∀ t ⊆ (slots j).attach,
    upperNat b t ≤ logScale X ^ (101 * m) →
    upperNat b t ≤ scale X →
    ((slots j).attach \ t).card ≤ 2 →
    (∀ i ∈ (slots j).attach \ t, i.1 < j + 1) →
    ∀ α : ℝ, ∀ a : ℚ,
    denCutM m X < a.den →
    a.den ≤ appBoundM m X →
    |α - (a : ℝ)| ≤ 1 / ((a.den : ℝ) * (appBoundM m X : ℝ)) →
    (∫ θ in α..(α + 1 / (window X : ℝ)),
      ‖boxPrefix (mobiusCutoff X) j b C θ‖ ^ 2) ≤
      (scale X : ℝ) / (logScale X : ℝ) ^ (30 * m)

/-- Parametric form of `GoldbachBeaumontCompletion.eventually_all_box_cells`. -/
def boxBound (m : ℕ) : Prop :=
  ∀ᶠ X : ℕ in Filter.atTop, ∀ C ≤ scale X, ∀ j < 3,
    ∀ b ∈ activeChoices (scale X) (mobiusCutoff X) j (Finset.Ioc 0 C),
    ∀ α : ℝ, ∀ a q : ℕ,
    denCutM m X < q →
    q ≤ appBoundM m X → a.Coprime q →
    |α - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * (appBoundM m X : ℝ)) →
    (∫ θ in α..(α + 1 / (window X : ℝ)),
      ‖boxPrefix (mobiusCutoff X) j b C θ‖ ^ 2) ≤
      (scale X : ℝ) / (logScale X : ℝ) ^ (30 * m)

/-- Parametric form of `GoldbachBeaumontCompletion.eventually_high_band_cells`. -/
def highBound (m : ℕ) : Prop :=
  ∀ᶠ X : ℕ in Filter.atTop, ∀ L D : ℕ,
    L + D + 1 ≤ scale X →
    ∀ α : ℝ, ∀ a q : ℕ,
    denCutM m X < q →
    q ≤ appBoundM m X → a.Coprime q →
    |α - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * (appBoundM m X : ℝ)) →
    (∫ θ in α..(α + 1 / (window X : ℝ)),
      ‖BulkCircle.S L D θ‖ ^ 2) ≤
      (scale X : ℝ) / (logScale X : ℝ) ^ (3 * m)

/-- Parametric form of `BeaumontLowScales.eventually_low_denominator_cell`. -/
def lowBound (m : ℕ) : Prop :=
  ∀ᶠ X : ℕ in Filter.atTop, ∀ L D q a j : ℕ,
    scale X ≤ 10 * L →
    L + D + 1 ≤ scale X →
    2 * majCutM m X ≤ D →
    0 < q → q ≤ denCutM m X → a ≤ q → a.Coprime q →
    |(j : ℝ) / (window X : ℝ) - (a : ℝ) / (q : ℝ)| ≤
      1 / ((q : ℝ) * (appBoundM m X : ℝ)) →
    (∫ t in ((j : ℝ) / (window X : ℝ))..(((j : ℝ) + 1) / (window X : ℝ)),
      (GoldbachBlockGeometry.arcs (majCutM m X) D)ᶜ.indicator
        (fun t => ‖BulkCircle.S L D t‖ ^ 2) t) ≤
      (scale X : ℝ) / (logScale X : ℝ) ^ (3 * m)

/-- Parametric form of `GoldbachBeaumontFinish.localMinorBound`. -/
def cellBound (m : ℕ) : Prop :=
  ∀ᶠ X : ℕ in Filter.atTop, ∀ y : ℕ, X ≤ y → y ≤ 2 * X → ∀ j < Nat.sqrt X,
    (∫ t in ((j : ℝ) / (Nat.sqrt X : ℝ))..(((j : ℝ) + 1) / (Nat.sqrt X : ℝ)),
      (majArcsM m X)ᶜ.indicator
        (fun u => ‖BulkCircle.S (centralStart X y) (centralWidth X) u‖ ^ 2) t) ≤
      ((3 * X : ℕ) : ℝ) / (logScale X : ℝ) ^ (3 * m)


/-- Parametric version of `BeaumontSmallModuli.energy_charge`: the same three
absorption conditions with the exponents scaled, giving the saving `N / L^K`
for an arbitrary `K`. -/
theorem energy_chargeK (A K : ℕ) (N H Q L D E : ℝ)
    (hN : 0 ≤ N) (hH : 0 < H) (hQ : 0 ≤ Q) (hL : 0 < L)
    (hsmall : 480*Q^3*H*L^(K+2) ≤ N)
    (hbulk : 96*D*Q^3*L^(K+1) ≤ L^A)
    (hdiagonal : 36*Q^2*L^(K+2) ≤ H^2)
    (hE : H^2/4*E ≤
      40*Q^3*H^3*L^2 + 8*D*Q^3*N*H^2*L/L^A + 3*Q^2*N*L^2) :
    E ≤ N/L^K := by
  rw [pow_add] at hsmall hbulk hdiagonal
  have hfirst : (12*L^K)*(40*Q^3*H^3*L^2) ≤ N*H^2 := by
    have hm := mul_le_mul_of_nonneg_right hsmall (sq_nonneg H)
    convert hm using 1 <;> ring
  have hsecond : (12*L^K)*(8*D*Q^3*N*H^2*L/L^A) ≤ N*H^2 := by
    have hm := mul_le_mul_of_nonneg_right hbulk (by positivity : 0 ≤ N*H^2)
    have he : (12*L^K)*(8*D*Q^3*N*H^2*L/L^A) =
        (96*D*Q^3*(L^K*L^1)*(N*H^2))/L^A := by ring
    rw [he]
    apply (div_le_iff₀ (by positivity : 0 < L^A)).2
    convert hm using 1 <;> ring
  have hthird : (12*L^K)*(3*Q^2*N*L^2) ≤ N*H^2 := by
    have hm := mul_le_mul_of_nonneg_right hdiagonal hN
    convert hm using 1 <;> ring
  have hmul := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 12*L^K)
  have hlast : (H^2/4*E)*(12*L^K) ≤ 3*(N*H^2) := by
    nlinarith only [hmul, hfirst, hsecond, hthird]
  apply (le_div_iff₀ (by positivity : 0 < L^K)).2
  apply le_of_mul_le_mul_left (a := 3*H^2) ?_ (by positivity : 0 < 3*H^2)
  nlinarith only [hlast]

/-- Parametric version of `BeaumontSmallModuliPolylog.totalError_small`. -/
theorem totalError_smallK (J A K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, ∀ n Q h : ℕ, ∀ δ : ℝ,
      2 ≤ n → 0 < h → h ≤ n → Q ≤ n → T ≤ 2*h →
      (n : ℝ) ≤ (2*(h : ℝ))^3 →
      (Q : ℝ)^2*(n : ℝ)^(4/9 : ℝ) ≤ (h : ℝ) →
      (Q : ℝ) ≤ (Real.log (2*(h : ℝ)))^J →
      0 ≤ δ → 6*(h : ℝ)*δ ≤ 1 → 16 ≤ Real.log (n : ℝ) →
      480*(Q : ℝ)^3*(h : ℝ)*(Real.log (n : ℝ))^(K+2) ≤ (n : ℝ) →
      96*(C*3^A)*(Q : ℝ)^3*(Real.log (n : ℝ))^(K+1) ≤ (Real.log (n : ℝ))^A →
      36*(Q : ℝ)^2*(Real.log (n : ℝ))^(K+2) ≤ (h : ℝ)^2 →
      BeaumontSmallModuliPolylog.totalError n Q δ ≤ (n : ℝ)/(Real.log (n : ℝ))^K := by
  obtain ⟨C,hC,T,hT⟩ := BeaumontSmallModuliPolylog.totalError_bound J A
  refine ⟨C,hC,T,?_⟩
  intro n Q h δ hn hh hhn hQn hTh hcube hscale hQ hd hw hlog hsmall hbulk hdiag
  let L := Real.log (n : ℝ)
  have hL : 16 ≤ L := hlog
  have hL0 : 0 < L := by linarith
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hh0 : 0 < (h : ℝ) := by exact_mod_cast hh
  have hn1 : ((n+1 : ℕ) : ℝ) ≤ 2*(n : ℝ) := by exact_mod_cast (by omega : n+1 ≤ 2*n)
  have hn2 : ((n+1+h : ℕ) : ℝ) ≤ 3*(n : ℝ) := by exact_mod_cast (by omega : n+1+h ≤ 3*n)
  have hlogplus : L+1 ≤ 2*L := by linarith
  have hlogfive0 : 0 ≤ Real.log (5*(n : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 5*n))
  have hlogfive : Real.log (5*(n : ℝ))+1 ≤ 4*L := by
    rw [Real.log_mul (by norm_num) hn0.ne']
    have hf := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
    dsimp [L] at *
    linarith
  apply energy_chargeK A K (n : ℝ) (h : ℝ) (Q : ℝ) L (C*3^A)
    (BeaumontSmallModuliPolylog.totalError n Q δ) hn0.le hh0 (by positivity) hL0
    hsmall hbulk hdiag
  apply (hT n Q h δ hn hh hhn hQn hTh hcube hscale hQ hd hw).trans
  calc
    _ ≤ (Q : ℝ)^2*((h : ℝ)*(2*L))*
          (4*(Q : ℝ)*(h : ℝ)^2*(4*L) +
            2*(2*(n : ℝ))*(C*(Q : ℝ)*(h : ℝ)*3^A/L^A) +
            (Q : ℝ)*2*(h : ℝ)^2*(2*L)) +
          (Q : ℝ)^2*(3*(n : ℝ))*L^2 := by
      gcongr
    _ = _ := by ring

/-- The packet radius of the parametric parameters is admissible. -/
theorem pktRadM_bounds (m X : ℕ) (hR : 4 ≤ appBoundM m X) :
    0 ≤ pktRadM m X ∧ pktRadM m X ≤ 1/2 ∧
      6*(progWinM m X : ℝ)*pktRadM m X ≤ 1 := by
  have hRH : appBoundM m X ≤ window X := Nat.div_le_self _ _
  have hRp : 0 < (appBoundM m X : ℝ) :=
    by exact_mod_cast (by omega : 0 < appBoundM m X)
  have hHp : 0 < (window X : ℝ) := by exact_mod_cast (by omega : 0 < window X)
  have hRHr : (appBoundM m X : ℝ) ≤ window X := by exact_mod_cast hRH
  have hR4 : (4 : ℝ) ≤ appBoundM m X := by exact_mod_cast hR
  have hrec : 1/(window X : ℝ) ≤ 1/(appBoundM m X : ℝ) :=
    one_div_le_one_div_of_le hRp hRHr
  have hδ : pktRadM m X ≤ 2/(appBoundM m X : ℝ) := by
    dsimp [pktRadM]
    calc
      1/(appBoundM m X : ℝ)+1/(window X : ℝ) ≤
          1/(appBoundM m X : ℝ)+1/(appBoundM m X : ℝ) := add_le_add le_rfl hrec
      _ = _ := by ring
  have hhR : 24*(progWinM m X : ℝ) ≤ (appBoundM m X : ℝ) := by
    exact_mod_cast Nat.mul_div_le (appBoundM m X) 24
  refine ⟨by unfold pktRadM; positivity, ?_, ?_⟩
  · exact hδ.trans ((div_le_iff₀ hRp).2 (by linarith))
  · calc
      _ ≤ 6*(progWinM m X : ℝ)*(2/(appBoundM m X : ℝ)) := by
        gcongr
      _ ≤ 1 := by
        rw [← mul_div_assoc]
        exact (div_le_iff₀ hRp).2 (by nlinarith)

/-- Parametric version of `BeaumontLowScales.eventually_prefix_error`. -/
theorem prefix_errorM (m : ℕ) (hm : 1 ≤ m) :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ n : ℕ, scale X ≤ 10*n → n ≤ scale X →
      BeaumontSmallModuliPolylog.totalError n (denCutM m X) (pktRadM m X) ≤
        (8:ℝ)^(4*m) * (scale X : ℝ) / (logScale X : ℝ)^(4*m) := by
  obtain ⟨C,hC,T,hT⟩ := totalError_smallK (2000*m) (12000*m) (4*m)
  have hgC : ∀ᶠ X : ℕ in Filter.atTop,
      8*(96*(C*3^(12000*m))) ≤ (logScale X : ℝ) :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp logScale_tendsto).eventually_ge_atTop _
  have hpowM : ∀ᶠ X : ℕ in Filter.atTop,
      (X : ℝ)^(17/36 : ℝ) ≤ (progWinM m X : ℝ) := by
    simpa only [progWinM, appBoundM, Nat.div_div_eq_div_mul] using
      BeaumontLowScales.eventually_divided_window_power (2000*m)
  filter_upwards [hpowM,
      logScale_tendsto.eventually_ge_atTop (max 1000000 T),
      eventually_ge_atTop (100 : ℕ), hgC,
      eventually_mul_logScale_power_le_rpow 3 (by norm_num) (2000*m) (1/36) (by norm_num),
      eventually_mul_logScale_power_le_rpow 1600 (by norm_num) (3006*m) (1/2) (by norm_num),
      eventually_mul_logScale_power_le_rpow 6 (by norm_num) (1003*m) (17/36) (by norm_num)]
    with X hpow hg hX hgC hAP hEP hDG
  intro n hnlo hnhi
  let g : ℝ := logScale X
  let h : ℝ := progWinM m X
  let L : ℝ := Real.log (n : ℝ)
  have hgN : 1000000 ≤ logScale X := (le_max_left _ _).trans hg
  have hgT : T ≤ logScale X := (le_max_right _ _).trans hg
  have hgR : (1000000 : ℝ) ≤ g := by dsimp [g]; exact_mod_cast hgN
  have hg0 : 0 < g := by linarith only [hgR]
  have hg1 : 1 ≤ g := by linarith only [hgR]
  have hXp : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hn : 2 ≤ n := by dsimp [scale] at hnlo; omega
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnlor : 3*(X : ℝ) ≤ 10*(n : ℝ) := by exact_mod_cast hnlo
  have hnhir : (n : ℝ) ≤ 3*(X : ℝ) := by exact_mod_cast hnhi
  obtain ⟨hgL,hLg⟩ := BeaumontLowScales.prefix_log_bounds hX (by omega : 32 ≤ logScale X)
    hnlo hnhi
  change g ≤ 8*L at hgL
  change L ≤ g at hLg
  have hL : 16 ≤ L := by linarith only [hgR,hgL]
  have hL0 : 0 < L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  have hpow1 : 1 ≤ (X : ℝ)^(17/36 : ℝ) := Real.one_le_rpow hX1 (by norm_num)
  have hh1 : 1 ≤ h := hpow1.trans hpow
  have hh0 : 0 < h := by linarith only [hh1]
  have hh : 0 < progWinM m X := by
    have he : (0 : ℝ) < progWinM m X := hh0
    exact_mod_cast he
  have hH10 : 10 ≤ window X := Nat.le_sqrt'.mpr (by norm_num; exact hX)
  have hHsq := Nat.sqrt_le' X
  have hHn : window X ≤ n := by
    dsimp [window] at hH10 hHsq ⊢
    dsimp [scale] at hnlo
    nlinarith only [hH10,hHsq,hnlo]
  have hprogW : progWinM m X ≤ window X :=
    (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)
  have hhn : progWinM m X ≤ n := hprogW.trans hHn
  have hQc : (denCutM m X : ℝ) = g^(1000*m) := by
    simp only [denCutM,Nat.cast_pow,g]
  have hQh : (denCutM m X : ℝ) ≤ h := by
    rw [hQc]
    have hmono := pow_le_pow_right₀ hg1 (by omega : 1000*m ≤ 1003*m)
    have hcap : g^(1003*m) ≤ (X : ℝ)^(17/36 : ℝ) := by
      change 6*g^(1003*m) ≤ _ at hDG
      linarith only [hDG,pow_nonneg hg0.le (1003*m)]
    exact hmono.trans (hcap.trans hpow)
  have hQhn : denCutM m X ≤ progWinM m X := by
    have he : (denCutM m X : ℝ) ≤ (progWinM m X : ℝ) := hQh
    exact_mod_cast he
  have hQn : denCutM m X ≤ n := hQhn.trans hhn
  have hgQ : logScale X ≤ denCutM m X := by
    dsimp [denCutM]
    exact Nat.le_self_pow (by omega : 1000*m ≠ 0) _
  have hTh : T ≤ 2*progWinM m X := by
    have := hgT.trans (hgQ.trans hQhn)
    omega
  have hroot := BeaumontLowScales.window_root_bounds (by omega : 1 ≤ X)
  have hhW : h ≤ (window X : ℝ) := by
    change (progWinM m X : ℝ) ≤ (window X : ℝ)
    exact_mod_cast hprogW
  have hhroot : h ≤ (X : ℝ)^(1/2 : ℝ) := hhW.trans hroot.1
  have hcubelow : (X : ℝ)^(1/3 : ℝ) ≤ h :=
    (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num : (1/3 : ℝ) ≤ 17/36)).trans hpow
  have hcubeX : (X : ℝ) ≤ h^3 := by
    have hp := pow_le_pow_left₀ (Real.rpow_nonneg hXp.le (1/3 : ℝ)) hcubelow 3
    have he : ((X : ℝ)^(1/3 : ℝ))^3 = (X : ℝ) := by
      simpa only [one_div,Nat.cast_ofNat] using
        Real.rpow_inv_natCast_pow hXp.le (by norm_num : (3 : ℕ) ≠ 0)
    rwa [he] at hp
  have hcube : (n : ℝ) ≤ (2*h)^3 := by
    nlinarith only [hnhir,hcubeX,pow_nonneg hh0.le 3]
  have hnpow : (n : ℝ)^(4/9 : ℝ) ≤ 3*(X : ℝ)^(4/9 : ℝ) := by
    calc
      _ ≤ (3*(X : ℝ))^(4/9 : ℝ) := Real.rpow_le_rpow hnp.le hnhir (by norm_num)
      _ = (3 : ℝ)^(4/9 : ℝ)*(X : ℝ)^(4/9 : ℝ) := Real.mul_rpow (by norm_num) hXp.le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 3) (by norm_num))
        (Real.rpow_nonneg hXp.le _)
  have hAP' := mul_le_mul_of_nonneg_right hAP (Real.rpow_nonneg hXp.le (4/9 : ℝ))
  rw [← Real.rpow_add hXp] at hAP'
  norm_num only [show (1/36 : ℝ)+4/9 = 17/36 by norm_num] at hAP'
  have hg2 : (g^(1000*m))^2 = g^(2000*m) := by
    rw [← pow_mul, show (1000*m)*2 = 2000*m by ring]
  have hg3 : (g^(1000*m))^3 = g^(3000*m) := by
    rw [← pow_mul, show (1000*m)*3 = 3000*m by ring]
  have hg2' : (g^(1003*m))^2 = g^(2006*m) := by
    rw [← pow_mul, show (1003*m)*2 = 2006*m by ring]
  have hpowL : L^(4*m+2) ≤ g^(4*m+2) := pow_le_pow_left₀ hL0.le hLg (4*m+2)
  have hscale : (denCutM m X : ℝ)^2*(n : ℝ)^(4/9 : ℝ) ≤ h := by
    rw [hQc]
    calc
      _ ≤ (g^(1000*m))^2*(3*(X : ℝ)^(4/9 : ℝ)) :=
        mul_le_mul_of_nonneg_left hnpow (by positivity)
      _ = (3*g^(2000*m))*(X : ℝ)^(4/9 : ℝ) := by rw [hg2]; ring
      _ ≤ (X : ℝ)^(17/36 : ℝ) := hAP'
      _ ≤ h := hpow
  have hloghx := Real.log_le_log (Real.rpow_pos_of_pos hXp _) hcubelow
  rw [Real.log_rpow hXp] at hloghx
  have hglog := logScale_le_four_log (by omega : 4 ≤ X)
  change g ≤ _ at hglog
  have hghlog : g ≤ 12*Real.log h := by linarith only [hloghx,hglog]
  have hlogh : 12 ≤ Real.log h := by linarith only [hghlog,hgR]
  have hlog2h := Real.log_le_log hh0 (show h ≤ 2*h by linarith only [hh0])
  have hglog2sq : g ≤ (Real.log (2*h))^2 := by
    nlinarith only [hghlog,hlogh,hlog2h,sq_nonneg (Real.log (2*h)-12)]
  have hQlog : (denCutM m X : ℝ) ≤ (Real.log (2*h))^(2000*m) := by
    rw [hQc]
    have he := pow_le_pow_left₀ hg0.le hglog2sq (1000*m)
    have hkm : 2*(1000*m) = 2000*m := by ring
    simpa only [← pow_mul, hkm] using he
  have hR : 4 ≤ appBoundM m X := by
    have hd : 24*progWinM m X ≤ appBoundM m X := Nat.mul_div_le (appBoundM m X) 24
    omega
  obtain ⟨hδ,hδhalf,hw⟩ := pktRadM_bounds m X hR
  have hsmall : 480*(denCutM m X : ℝ)^3*h*L^(4*m+2) ≤ (n : ℝ) := by
    have hcap := mul_le_mul_of_nonneg_right hEP (Real.rpow_nonneg hXp.le (1/2 : ℝ))
    have hroot_sq : ((X : ℝ)^(1/2 : ℝ))^2 = (X : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.sq_sqrt hXp.le
    have hcap' : 1600*g^(3006*m)*(X : ℝ)^(1/2 : ℝ) ≤ (X : ℝ) := by
      simpa only [g, ← pow_two, hroot_sq] using hcap
    have hexp : g^(3000*m)*g^(4*m+2) ≤ g^(3006*m) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hg1 (by omega)
    have h1 : h*L^(4*m+2) ≤ ((X : ℝ)^(1/2 : ℝ))*g^(4*m+2) :=
      mul_le_mul hhroot hpowL (by positivity) (by positivity)
    calc
      _ = 480*(denCutM m X : ℝ)^3*(h*L^(4*m+2)) := by ring
      _ ≤ 480*(g^(1000*m))^3*(((X : ℝ)^(1/2 : ℝ))*g^(4*m+2)) := by
        rw [hQc]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 480*(g^(3000*m)*g^(4*m+2))*((X : ℝ)^(1/2 : ℝ)) := by rw [hg3]; ring
      _ ≤ 480*g^(3006*m)*((X : ℝ)^(1/2 : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by norm_num))
          (Real.rpow_nonneg hXp.le _)
      _ ≤ (n : ℝ) := by nlinarith only [hcap',hnlor]
  have hbulk : 96*(C*3^(12000*m))*(denCutM m X : ℝ)^3*L^(4*m+1) ≤ L^(12000*m) := by
    have hgLsq : g ≤ L^2 := by nlinarith only [hgL,hL,sq_nonneg (L-8)]
    have hPcube : (denCutM m X : ℝ)^3 ≤ L^(6000*m) := by
      rw [hQc, hg3]
      have hp := pow_le_pow_left₀ hg0.le hgLsq (3000*m)
      have hkm : 2*(3000*m) = 6000*m := by ring
      simpa only [← pow_mul, hkm] using hp
    have hK : 96*(C*3^(12000*m)) ≤ L := by
      change 8*(96*(C*3^(12000*m))) ≤ g at hgC
      exact le_of_mul_le_mul_left (hgC.trans hgL) (by norm_num : (0 : ℝ) < 8)
    have h1 : 96*(C*3^(12000*m))*(denCutM m X : ℝ)^3 ≤ L*L^(6000*m) :=
      mul_le_mul hK hPcube (by positivity) hL0.le
    calc
      _ = (96*(C*3^(12000*m))*(denCutM m X : ℝ)^3)*L^(4*m+1) := by ring
      _ ≤ (L*L^(6000*m))*L^(4*m+1) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = L^(6000*m+1)*L^(4*m+1) := by rw [pow_add L (6000*m) 1, pow_one]; ring
      _ = L^((6000*m+1)+(4*m+1)) := by rw [← pow_add]
      _ ≤ _ := pow_le_pow_right₀ hL1 (by omega)
  have hdiag : 36*(denCutM m X : ℝ)^2*L^(4*m+2) ≤ h^2 := by
    have hbase : 6*g^(1003*m) ≤ h := hDG.trans hpow
    have hexp : g^(2000*m)*g^(4*m+2) ≤ g^(2006*m) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hg1 (by omega)
    calc
      _ ≤ 36*(g^(1000*m))^2*g^(4*m+2) := by
        rw [hQc]
        exact mul_le_mul_of_nonneg_left hpowL (by positivity)
      _ = 36*(g^(2000*m)*g^(4*m+2)) := by rw [hg2]; ring
      _ ≤ 36*g^(2006*m) := mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ = (6*g^(1003*m))^2 := by rw [← hg2']; ring
      _ ≤ h^2 := pow_le_pow_left₀ (by positivity) hbase 2
  have herr := hT n (denCutM m X) (progWinM m X) (pktRadM m X)
    hn hh hhn hQn hTh hcube hscale hQlog hδ hw hL hsmall hbulk hdiag
  apply herr.trans
  have hgpow := pow_le_pow_left₀ hg0.le hgL (4*m)
  have hgp : 0 < g^(4*m) := by positivity
  have hLp : 0 < L^(4*m) := by positivity
  apply (div_le_div_iff₀ hLp hgp).2
  have hNn : (n : ℝ) ≤ (scale X : ℝ) := by exact_mod_cast hnhi
  change (n : ℝ)*g^(4*m) ≤ (8:ℝ)^(4*m) * (scale X : ℝ)*L^(4*m)
  calc
    _ ≤ (n : ℝ)*(8*L)^(4*m) := mul_le_mul_of_nonneg_left hgpow hnp.le
    _ ≤ (scale X : ℝ)*(8*L)^(4*m) := mul_le_mul_of_nonneg_right hNn (by positivity)
    _ = _ := by rw [mul_pow]; ring
/-! ### Parametric geometry (adapted from `BeaumontHighScales`) -/

lemma eventually_upper_powerM (m : ℕ) :
    ∀ᶠ X : ℕ in atTop, (X : ℝ)^(17/36 : ℝ) ≤ (upFacM m X : ℝ) := by
  simpa only [upFacM, physicalWindow, Nat.div_div_eq_div_mul, Nat.mul_comm] using
    BeaumontLowScales.eventually_divided_window_power (100*m)

lemma eventually_progression_powerM (m : ℕ) :
    ∀ᶠ X : ℕ in atTop, (X : ℝ)^(17/36 : ℝ) ≤ (progWinM m X : ℝ) := by
  simpa only [progWinM, appBoundM, Nat.div_div_eq_div_mul, Nat.mul_comm] using
    BeaumontLowScales.eventually_divided_window_power (2000*m)

lemma rational_separation_scaleM {X m : ℕ} (hm : 1 ≤ m) (hg : 2 ≤ logScale X) :
    4*denCutM m X*appBoundM m X ≤ window X := by
  dsimp only [denCutM, appBoundM]
  have hpow : 4 ≤ logScale X^(1000*m) := by
    calc
      _ ≤ logScale X^2 := by nlinarith
      _ ≤ _ := pow_le_pow_right₀ (by omega : 1 ≤ logScale X) (by omega : 2 ≤ 1000*m)
  have hsq : 4*logScale X^(1000*m) ≤ logScale X^(2000*m) := by
    have h2 : 4*logScale X^(1000*m) ≤ (logScale X^(1000*m))^2 := by
      rw [pow_two]; exact Nat.mul_le_mul_right _ hpow
    have h3 : (logScale X^(1000*m))^2 = logScale X^(2000*m) := by
      rw [← pow_mul]; congr 1; omega
    rwa [h3] at h2
  have hdiv : logScale X^(2000*m)*(window X/logScale X^(2000*m)) ≤ window X :=
    Nat.mul_div_le (window X) (logScale X^(2000*m))
  exact (Nat.mul_le_mul_right (window X/logScale X^(2000*m)) hsq).trans hdiv

lemma eventually_grouping_geomM (m : ℕ) (hm : 1 ≤ m) :
    ∀ᶠ X : ℕ in atTop,
      lowFacM m X ^ 2 ≤ upFacM m X ∧
      64*scale X < upFacM m X ^ 3 ∧
      2*⌊(scale X : ℝ)^(1/3 : ℝ)⌋₊ ≤ upFacM m X ∧
      4*denCutM m X*appBoundM m X ≤ window X ∧
      2*denCutM m X ≤ appBoundM m X := by
  filter_upwards [eventually_upper_powerM m,
      eventually_mul_logScale_power_le_rpow 1 (by norm_num) (202*m) (17/36) (by norm_num),
      eventually_mul_logScale_power_le_rpow 384 (by norm_num) 0 (5/12) (by norm_num),
      eventually_mul_logScale_power_le_rpow 6 (by norm_num) 0 (5/36) (by norm_num),
      eventually_mul_logScale_power_le_rpow 1 (by norm_num) (1000*m) (17/36) (by norm_num),
      eventually_progression_powerM m,
      logScale_tendsto.eventually_ge_atTop 2, eventually_ge_atTop (1 : ℕ)]
    with X hB hApow hlarge hroot hQ hprog hg hX
  have hXp : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hX0 : 0 ≤ (X : ℝ) := hXp.le
  have hN : (scale X : ℝ) = 3*(X : ℝ) := by simp [scale]
  have hA' : lowFacM m X^2 ≤ upFacM m X := by
    have ha : (logScale X : ℝ)^(202*m) ≤ (upFacM m X : ℝ) := by
      simpa only [one_mul] using hApow.trans hB
    have hcast : ((lowFacM m X^2 : ℕ) : ℝ) = (logScale X : ℝ)^(202*m) := by
      simp only [lowFacM, Nat.cast_pow, ← pow_mul]
      rw [show (101*m)*2 = 202*m by omega]
    have h2 : ((lowFacM m X^2 : ℕ) : ℝ) ≤ (upFacM m X : ℝ) := by rw [hcast]; exact ha
    exact_mod_cast h2
  have hB0 : 0 ≤ (upFacM m X : ℝ) := by positivity
  have hBcube := pow_le_pow_left₀ (Real.rpow_nonneg hX0 _) hB 3
  have hBcube' : (X : ℝ)^(17/12 : ℝ) ≤ (upFacM m X : ℝ)^3 := by
    simpa only [← Real.rpow_mul_natCast hX0, Nat.cast_ofNat,
      show (17/36 : ℝ)*3 = 17/12 by norm_num] using hBcube
  have hlarge' : 384 ≤ (X : ℝ)^(5/12 : ℝ) := by simpa using hlarge
  have hlargeX := mul_le_mul_of_nonneg_right hlarge' hX0
  have hprod : (X : ℝ)^(5/12 : ℝ)*(X : ℝ) = (X : ℝ)^(17/12 : ℝ) := by
    conv_lhs => rhs; rw [← Real.rpow_one (X : ℝ)]
    rw [← Real.rpow_add hXp]
    congr 1
    norm_num
  rw [hprod] at hlargeX
  have hcube : 64*scale X < upFacM m X^3 := by
    have h : 192*(X : ℝ) < (upFacM m X : ℝ)^3 := by
      linarith [hlargeX.trans hBcube']
    have hh : 64*(scale X:ℝ)<(upFacM m X:ℝ)^3 := by rw [hN]; nlinarith only [h]
    exact_mod_cast hh
  have hroot' : 6 ≤ (X : ℝ)^(5/36 : ℝ) := by simpa using hroot
  have hrootX := mul_le_mul_of_nonneg_right hroot' (Real.rpow_nonneg hX0 (1/3 : ℝ))
  rw [← Real.rpow_add hXp] at hrootX
  norm_num only [show (5/36 : ℝ)+1/3 = 17/36 by norm_num] at hrootX
  have hcut : ((⌊(scale X : ℝ)^(1/3 : ℝ)⌋₊ : ℕ) : ℝ) ≤
      3*(X : ℝ)^(1/3 : ℝ) := by
    calc
      _ ≤ (scale X : ℝ)^(1/3 : ℝ) := Nat.floor_le (by positivity)
      _ = (3 : ℝ)^(1/3 : ℝ)*(X : ℝ)^(1/3 : ℝ) := by rw [hN,Real.mul_rpow (by norm_num) hX0]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 3) (by norm_num))
        (Real.rpow_nonneg hX0 _)
  have hcut' : 2*⌊(scale X : ℝ)^(1/3 : ℝ)⌋₊ ≤ upFacM m X := by
    have ht : 2*((⌊(scale X : ℝ)^(1/3 : ℝ)⌋₊ : ℕ) : ℝ) ≤ (upFacM m X : ℝ) := by
      linarith [hrootX.trans hB]
    exact_mod_cast ht
  have hQh : denCutM m X ≤ progWinM m X := by
    exact_mod_cast (by simpa only [one_mul,denCutM,Nat.cast_pow] using hQ.trans hprog :
      (denCutM m X : ℝ) ≤ (progWinM m X : ℝ))
  have hqR : 2*denCutM m X ≤ appBoundM m X := by
    have hr : 24*(appBoundM m X/24) ≤ appBoundM m X :=
      Nat.mul_div_le (appBoundM m X) 24
    dsimp only [progWinM] at hQh
    omega
  exact ⟨hA',hcube,hcut',rational_separation_scaleM hm hg,hqR⟩

lemma eventually_aux_geomM (m : ℕ) (hm : 1 ≤ m) :
    ∀ᶠ X : ℕ in atTop,
      0 < physicalWindow X ∧
      (appBoundM m X : ℝ)*(logScale X : ℝ)^(100*m) ≤ (physicalWindow X : ℝ) ∧
      4*logScale X^(12*m) ≤ window X ∧
      6*(physicalWindow X : ℝ)/(window X : ℝ) ≤ 1 := by
  filter_upwards [eventually_grouping_geomM m hm,
      eventually_auxiliary_geometry,
      logScale_tendsto.eventually_ge_atTop 24] with X hgeom haux hg
  have hg1 : 1 ≤ logScale X := (by decide : 1 ≤ 24).trans hg
  have hR1 : 1 ≤ appBoundM m X := by
    have hQpos : 0 < denCutM m X := pow_pos (logScale_pos X) _
    have h2 : denCutM m X ≤ appBoundM m X :=
      (Nat.le_mul_of_pos_left (denCutM m X) (by decide : 0 < 2)).trans hgeom.2.2.2.2
    omega
  have hQH : denCutM m X ≤ window X :=
    ((Nat.le_mul_of_pos_left (denCutM m X) (by decide : 0 < 2)).trans
      hgeom.2.2.2.2).trans (Nat.div_le_self _ _)
  have hpow : 24*logScale X^(100*m) ≤ logScale X^(2000*m) := by
    calc
      _ ≤ logScale X*logScale X^(100*m) := Nat.mul_le_mul_right _ hg
      _ = logScale X^(100*m+1) := (pow_succ' (logScale X) (100*m)).symm
      _ ≤ _ := pow_le_pow_right₀ hg1 (by omega : 100*m+1 ≤ 2000*m)
  have hdiv : logScale X^(2000*m)*appBoundM m X ≤ window X :=
    Nat.mul_div_le (window X) (logScale X^(2000*m))
  have hprod : appBoundM m X*logScale X^(100*m) ≤ physicalWindow X := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 24)).2
    calc
      _ = (24*logScale X^(100*m))*appBoundM m X := by ac_rfl
      _ ≤ logScale X^(2000*m)*appBoundM m X := Nat.mul_le_mul_right _ hpow
      _ ≤ window X := hdiv
  have h12 : 4*logScale X^(12*m) ≤ window X := by
    calc
      _ ≤ logScale X*logScale X^(12*m) := Nat.mul_le_mul_right _ ((by decide : 4 ≤ 24).trans hg)
      _ = logScale X^(12*m+1) := (pow_succ' (logScale X) (12*m)).symm
      _ ≤ logScale X^(1000*m) := pow_le_pow_right₀ hg1 (by omega : 12*m+1 ≤ 1000*m)
      _ ≤ window X := by simpa only [denCutM] using hQH
  refine ⟨haux.1, by exact_mod_cast hprod, h12, haux.2.2.2⟩

lemma eventually_residual_geomM (m : ℕ) (hm : 1 ≤ m) :
    ∀ᶠ X : ℕ in atTop,
      logScale X ^ (5000*m) ≤ window X ∧
      window X^2 ≤ scale X ∧ scale X ≤ 12*window X^2 ∧
      (window X : ℝ)/(2*(logScale X : ℝ)^(2000*m)) ≤ (appBoundM m X : ℝ) ∧
      appBoundM m X ≤ window X ∧
      1+Real.log (64*(scale X : ℝ)) ≤ (logScale X : ℝ) := by
  filter_upwards [eventually_grouping_geomM m hm, eventually_logScale_power_le (10000*m),
      logScale_tendsto.eventually_ge_atTop 32, eventually_ge_atTop (1 : ℕ)]
    with X hgeom hpower hg hX
  have hgpos : 0 < logScale X := logScale_pos X
  have hgposr : (0 : ℝ) < logScale X := by exact_mod_cast hgpos
  have hH : logScale X^(5000*m) ≤ window X := by
    change logScale X^(5000*m) ≤ Nat.sqrt X
    apply Nat.le_sqrt'.2
    rw [← pow_mul, show (5000*m)*2 = 10000*m by omega]
    exact hpower
  have hH1 : 1 ≤ window X := Nat.le_sqrt'.2 (by simpa using hX)
  have hsq : window X^2 ≤ X := Nat.sqrt_le' X
  have hsuc : X < (window X+1)^2 := Nat.lt_succ_sqrt' X
  have hNlo : window X^2 ≤ scale X :=
    hsq.trans (Nat.le_mul_of_pos_left X (by decide : 0 < 3))
  have hNhi : scale X ≤ 12*window X^2 := by
    have hww : window X ≤ window X^2 := Nat.le_self_pow (by decide : 2 ≠ 0) _
    change 3*X ≤ 12*window X^2
    nlinarith only [hsuc,hH1,hww]
  have hR1 : 1 ≤ appBoundM m X := by
    have hQpos : 0 < denCutM m X := pow_pos hgpos _
    have h2 : denCutM m X ≤ appBoundM m X :=
      (Nat.le_mul_of_pos_left (denCutM m X) (by decide : 0 < 2)).trans hgeom.2.2.2.2
    omega
  have hf : (window X : ℝ) < (logScale X : ℝ)^(2000*m)*
      ((appBoundM m X : ℝ)+1) := by
    exact_mod_cast Nat.lt_mul_div_succ (window X)
      (show 0 < logScale X^(2000*m) from pow_pos hgpos (2000*m))
  have hR1r : (1 : ℝ) ≤ appBoundM m X := by exact_mod_cast hR1
  have hden : 0 < (logScale X : ℝ)^(2000*m) := pow_pos hgposr _
  have hRlo : (window X : ℝ)/(2*(logScale X : ℝ)^(2000*m)) ≤ (appBoundM m X : ℝ) := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hden)).2
    have hmul := mul_le_mul_of_nonneg_left
      (show (appBoundM m X : ℝ)+1 ≤ 2*(appBoundM m X : ℝ) by linarith only [hR1r]) hden.le
    calc
      (window X : ℝ) ≤ (logScale X : ℝ)^(2000*m)*(2*(appBoundM m X : ℝ)) := hf.le.trans hmul
      _ = (appBoundM m X : ℝ)*(2*(logScale X : ℝ)^(2000*m)) := by ac_rfl
  exact ⟨hH,hNlo,hNhi,hRlo,Nat.div_le_self _ _, natural_log_margin hX hg⟩

/-! ### The four interfaces -/

theorem typeII_cells (m : ℕ) (hm : 1 ≤ m) : typeIICellBound m := by
  unfold typeIICellBound
  filter_upwards [eventually_aux_geomM m hm,
    logScale_tendsto.eventually_ge_atTop 128, eventually_ge_atTop (1:ℕ)] with X haux hg hX
  intro C hCN j hj b hb α a q hqlo hqhi hc ha ht
  obtain ⟨t,ht,hlo,hhi⟩ := ht
  have hq : 0 < q := (pow_pos (logScale_pos X) (1000*m)).trans hqlo
  have hRp : 0 < (appBoundM m X : ℝ) := by exact_mod_cast hq.trans_le hqhi
  have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
  have hgL : (128:ℝ) ≤ logScale X := by exact_mod_cast hg
  have hgL1 : (1:ℝ) ≤ logScale X := by linarith
  have hgmL : (logScale X : ℝ) ≤ (logScale X : ℝ)^m := by
    exact_mod_cast Nat.le_self_pow (by omega : m ≠ 0) (logScale X)
  have hgR : (128:ℝ) ≤ (logScale X : ℝ)^m := hgL.trans hgmL
  have happ : |α-(a:ℝ)/q| ≤ 1/(q:ℝ)^2 := by
    apply ha.trans
    apply one_div_le_one_div_of_le (by positivity)
    have hh : (q:ℝ) ≤ appBoundM m X := by exact_mod_cast hqhi
    nlinarith only [hh,hqr]
  have hwidth : 6*(physicalWindow X:ℝ)*(1/(window X:ℝ)) ≤ 1 := by
    simpa only [mul_one_div] using haux.2.2.2
  have hlo' : ((logScale X:ℝ)^m)^101 ≤ ∏ i ∈ t, upper j b i := by
    have h1 : ((logScale X:ℝ)^m)^101 = (logScale X:ℝ)^(101*m) := by
      rw [← pow_mul, Nat.mul_comm m 101]
    rw [h1]
    simpa only [lowFacM, Nat.cast_pow] using hlo
  have hbound : (upFacM m X : ℝ)*(logScale X : ℝ)^(100*m) ≤ (physicalWindow X : ℝ) := by
    have hh : upFacM m X*logScale X^(100*m) ≤ physicalWindow X :=
      Nat.div_mul_le_self (physicalWindow X) (logScale X^(100*m))
    exact_mod_cast hh
  have hhi' : (∏ i ∈ t,upper j b i)*((logScale X:ℝ)^m)^100 ≤ (physicalWindow X:ℝ) := by
    have h1 : ((logScale X:ℝ)^m)^100 = (logScale X:ℝ)^(100*m) := by
      rw [← pow_mul, Nat.mul_comm m 100]
    rw [h1]
    exact (mul_le_mul_of_nonneg_right hhi (by positivity)).trans hbound
  have hqlo' : ((logScale X:ℝ)^m)^100 ≤ (q:ℝ) := by
    have h1 : ((logScale X:ℝ)^m)^100 = (logScale X:ℝ)^(100*m) := by
      rw [← pow_mul, Nat.mul_comm m 100]
    rw [h1]
    have h2 : (logScale X:ℝ)^(100*m) ≤ (logScale X:ℝ)^(1000*m) :=
      pow_le_pow_right₀ hgL1 (by omega : 100*m ≤ 1000*m)
    have h3 : (logScale X:ℝ)^(1000*m) ≤ (q:ℝ) := by
      have h4 : logScale X^(1000*m) ≤ q := hqlo.le
      exact_mod_cast h4
    exact h2.trans h3
  have hqhi' : (q:ℝ)*((logScale X:ℝ)^m)^100 ≤ (physicalWindow X:ℝ) := by
    have h1 : ((logScale X:ℝ)^m)^100 = (logScale X:ℝ)^(100*m) := by
      rw [← pow_mul, Nat.mul_comm m 100]
    rw [h1]
    have h2 : (q:ℝ) ≤ appBoundM m X := by exact_mod_cast hqhi
    exact (mul_le_mul_of_nonneg_right h2 (by positivity)).trans haux.2.1
  have hlogq : 1+Real.log (2*(q:ℝ)) ≤ (logScale X:ℝ)^m := by
    have hqH : q ≤ window X := hqhi.trans (Nat.div_le_self _ _)
    have hqN : q ≤ scale X := hqH.trans
      ((Nat.sqrt_le_self X).trans (by exact Nat.le_mul_of_pos_left X (by decide : 0 < 3)))
    have hqr' : (q:ℝ) ≤ (scale X:ℝ) := by exact_mod_cast hqN
    have hn := natural_log_margin hX ((by decide : 32 ≤ 128).trans hg)
    have hN0 : (0:ℝ) ≤ scale X := Nat.cast_nonneg _
    have hl := Real.log_le_log (show 0 < 2*(q:ℝ) by positivity)
      (show 2*(q:ℝ) ≤ 64*(scale X:ℝ) by linarith [hqr'])
    linarith only [hn,hl,hgmL]
  have hlogN : 1+Real.log (64*(scale X:ℝ)) ≤ (logScale X:ℝ)^m :=
    (natural_log_margin hX ((by decide : 32 ≤ 128).trans hg)).trans hgmL
  have hlo' : ((logScale X:ℝ)^m)^101 ≤ ∏ i ∈ t, upper j b i := by
    have h1 : ((logScale X:ℝ)^m)^101 = (logScale X:ℝ)^(101*m) := by
      rw [← pow_mul, Nat.mul_comm m 101]
    have h2 : (lowFacM m X : ℝ) = (logScale X : ℝ)^(101*m) := by
      simp only [lowFacM, Nat.cast_pow]
    rw [h1]
    rw [h2] at hlo
    exact hlo
  have hres := typeII_box_cell hj b hb hCN t ht α (1/(window X:ℝ)) ((logScale X:ℝ)^m)
    hgR haux.1 hq (by positivity) hwidth (a:ℤ) hc.isCoprime
    (by simpa using happ) hlo' hhi' hqlo' hqhi' hlogq hlogN
  have h30 : ((logScale X:ℝ)^m)^30 = (logScale X:ℝ)^(30*m) := by
    rw [← pow_mul, Nat.mul_comm m 30]
  simpa only [h30] using hres

theorem residual_cells (m : ℕ) (hm : 1 ≤ m) : residualCellBound m := by
  unfold residualCellBound
  filter_upwards [eventually_grouping_geomM m hm, eventually_residual_geomM m hm,
    logScale_tendsto.eventually_ge_atTop 1000000, eventually_ge_atTop (1:ℕ)]
    with X hgeom hrgeom hg hX
  intro C hCN j hj b t ht hU hUN hcard hsmooth α a hQq hqR happ
  have hN : 1 ≤ scale X := hX.trans (Nat.le_mul_of_pos_left X (by decide : 0 < 3))
  have hRN : appBoundM m X ≤ scale X := hrgeom.2.2.2.2.1.trans
    ((Nat.sqrt_le_self X).trans (by exact Nat.le_mul_of_pos_left X (by decide : 0 < 3)))
  set g : ℕ := logScale X ^ m with hgdef
  have hg' : 1000000 ≤ g := by
    rw [hgdef]
    exact hg.trans (Nat.le_self_pow (by omega : m ≠ 0) (logScale X))
  have gpow : ∀ k : ℕ, ((g : ℝ))^k = (logScale X : ℝ)^(k*m) := by
    intro k
    rw [hgdef, Nat.cast_pow, ← pow_mul, Nat.mul_comm m k]
  have hH : (g:ℝ)^5000 ≤ (window X:ℝ) := by
    rw [gpow 5000]; exact_mod_cast hrgeom.1
  have hNlo : ((window X:ℝ))^2 ≤ (scale X:ℝ) := by exact_mod_cast hrgeom.2.1
  have hNhi : ((scale X:ℝ)) ≤ 12*((window X:ℝ))^2 := by exact_mod_cast hrgeom.2.2.1
  have hRlo : (window X:ℝ)/(2*(g:ℝ)^2000) ≤ (appBoundM m X:ℝ) := by
    rw [gpow 2000]; exact hrgeom.2.2.2.1
  have hRhi : (appBoundM m X:ℝ) ≤ (window X:ℝ) := by
    exact_mod_cast hrgeom.2.2.2.2.1
  have hQR : 2*(g:ℝ)^1000 ≤ (appBoundM m X:ℝ) := by
    rw [gpow 1000]; exact_mod_cast hgeom.2.2.2.2
  have hQH : 4*(g:ℝ)^1000*(appBoundM m X:ℝ) ≤ (window X:ℝ) := by
    rw [gpow 1000]; exact_mod_cast hgeom.2.2.2.1
  have hlog : 1+Real.log (64*(scale X:ℝ)) ≤ (g:ℝ) := by
    have hgmL : (logScale X : ℝ) ≤ (logScale X : ℝ)^m := by
      exact_mod_cast Nat.le_self_pow (by omega : m ≠ 0) (logScale X)
    rw [hgdef, Nat.cast_pow]
    exact hrgeom.2.2.2.2.2.trans hgmL
  have hU' : upperNat b t ≤ g^101 := by
    have h1 : g^101 = logScale X^(101*m) := by rw [hgdef, ← pow_mul, Nat.mul_comm m 101]
    rw [h1]; exact hU
  have hQq' : g^1000 < a.den := by
    have h1 : g^1000 = logScale X^(1000*m) := by rw [hgdef, ← pow_mul, Nat.mul_comm m 1000]
    rw [h1]; exact hQq
  have he := GoldbachBeaumontResidualSmooth.residual_box_cell
    (HC:=mobiusCutoff X) (N:=scale X) (g:=g) (H:=window X) (R:=appBoundM m X)
    hj hCN b t ht hU' hUN hcard hsmooth hg' hN hH hNlo hNhi hRlo hRhi hRN hQR hQH hlog
    a hQq' hqR happ
  have h30 : ((g : ℝ))^30 = (logScale X : ℝ)^(30*m) := gpow 30
  simpa only [boxPrefix, coefficientPolynomial, h30] using he

theorem all_box_cells (m : ℕ) (hm : 1 ≤ m)
    (htype : typeIICellBound m) (hres : residualCellBound m) : boxBound m := by
  unfold boxBound
  unfold typeIICellBound at htype
  unfold residualCellBound at hres
  filter_upwards [hres, htype, eventually_grouping_geomM m hm,
    eventually_residual_geomM m hm, eventually_ge_atTop (1:ℕ)]
    with X hres htype hgeom hrgeom hX
  intro C hCN j hj b hb α a q hqlo hqhi hc happ
  have hcut := mobiusCutoff_bounds hX
  obtain ⟨n,hn,hnz⟩ := (mem_filter.mp hb).2
  have hnN := (mem_Ioc.mp hn).2.trans hCN
  have hA : (1:ℝ) ≤ lowFacM m X := by
    exact_mod_cast one_le_pow₀ (logScale_pos X) (n:=101*m)
  have hAB : (lowFacM m X:ℝ)^2 ≤ upFacM m X := by exact_mod_cast hgeom.1
  have hN : (n:ℝ) ≤ scale X := by exact_mod_cast hnN
  have hB : 64*(scale X:ℝ) < (upFacM m X:ℝ)^3 := by exact_mod_cast hgeom.2.1
  rcases box_grouping hj b hnz hA hAB hN hB with hbalanced | hrest
  · exact htype C hCN j hj b hb α a q hqlo hqhi hc happ hbalanced
  let S := (slots j).attach
  let t := S.filter (fun i => upper j b i < (lowFacM m X:ℝ))
  have ht : t ⊆ S := filter_subset _ _
  have hts : upperNat b t ≤ logScale X^(101*m) := by
    have hh : (upperNat b t:ℝ) < (lowFacM m X:ℝ) := by
      simpa only [cast_upperNat] using hrest.1
    exact_mod_cast hh.le
  have hg1 : 1 ≤ logScale X := logScale_pos X
  have htN : upperNat b t ≤ scale X := hts.trans
    ((pow_le_pow_right₀ hg1 (by omega : 101*m ≤ 5000*m)).trans
      (hrgeom.1.trans ((Nat.sqrt_le_self X).trans
        (by exact Nat.le_mul_of_pos_left X (by decide : 0 < 3)))))
  have hcomp (i : {i // i ∈ slots j}) (hi : i ∈ S \ t) :
      (upFacM m X:ℝ) < upper j b i := by
    have hh := mem_sdiff.mp hi
    rcases hrest.2.2 i hh.1 with hs | hb'
    · exact False.elim (hh.2 (mem_filter.mpr ⟨hh.1,hs⟩))
    · exact hb'
  have hcompcard : (S \ t).card ≤ 2 := by
    apply (card_le_card (show S \ t ⊆ S.filter (fun i => (upFacM m X:ℝ) < upper j b i) from
      fun i hi => mem_filter.mpr ⟨(mem_sdiff.mp hi).1,hcomp i hi⟩)).trans hrest.2.1
  have hlarge : ∀ i ∈ S \ t, i.1 < j+1 := by
    intro i hi
    apply large_box_factor_is_smooth (mem_filter.mp hb).1 (Nat.ne_of_gt hcut.1)
      (B:=(upFacM m X:ℝ)) _ (hcomp i hi)
    have hh : 2*mobiusCutoff X ≤ upFacM m X := hgeom.2.2.1
    exact_mod_cast hh
  have hq : 0 < q := (pow_pos (logScale_pos X) (1000*m)).trans hqlo
  let r := reducedRational a q hq hc
  have hrden : r.den=q := rfl
  have hrcast : (r:ℝ)=(a:ℝ)/q := reducedRational_cast a q hq hc
  exact hres C hCN j hj b t ht hts htN hcompcard hlarge α r
    (by simpa only [hrden] using hqlo) (by simpa only [hrden] using hqhi)
    (by simpa only [hrden,hrcast] using happ)

theorem high_cells (m : ℕ) (hm : 1 ≤ m) (hbox : boxBound m) : highBound m := by
  unfold highBound
  unfold boxBound at hbox
  filter_upwards [hbox, eventually_aux_geomM m hm,
    logScale_tendsto.eventually_ge_atTop 128, eventually_ge_atTop (1:ℕ)]
    with X hboxes haux hg hX
  intro L D hupper α a q hqlo hqhi hc happ
  have hcut := mobiusCutoff_bounds hX
  have hHp : 0 < window X := haux.1.trans_le (Nat.div_le_self _ _)
  have hHpR : 0 < (window X:ℝ) := by exact_mod_cast hHp
  have hgL : (128:ℝ) ≤ logScale X := by exact_mod_cast hg
  have hgmL : (logScale X : ℝ) ≤ (logScale X : ℝ)^m := by
    exact_mod_cast Nat.le_self_pow (by omega : m ≠ 0) (logScale X)
  have hgR : (16:ℝ) ≤ (logScale X:ℝ)^m := (by linarith : (16:ℝ) ≤ logScale X).trans hgmL
  have hN : 1 ≤ scale X := hX.trans (Nat.le_mul_of_pos_left X (by decide : 0 < 3))
  have hNpos : 0 < (scale X:ℝ) := by exact_mod_cast hN
  have hlog : Real.log (scale X:ℝ) ≤ (logScale X:ℝ)^m := by
    have hn := natural_log_margin hX ((by decide : 32 ≤ 128).trans hg)
    have hh := Real.log_le_log hNpos (show (scale X:ℝ) ≤ 64*(scale X:ℝ) by linarith [hNpos])
    linarith only [hn,hh,hgmL]
  have hlarge : 4*((logScale X:ℝ)^m)^12 ≤ (window X:ℝ) := by
    have h1 : ((logScale X:ℝ)^m)^12 = (logScale X:ℝ)^(12*m) := by
      rw [← pow_mul, Nat.mul_comm m 12]
    rw [h1]
    exact_mod_cast haux.2.2.1
  have h30 : ((logScale X:ℝ)^m)^30 = (logScale X:ℝ)^(30*m) := by
    rw [← pow_mul, Nat.mul_comm m 30]
  have hlog2 : ((Nat.log 2 (scale X)+1:ℕ):ℝ) ≤ 2*((logScale X:ℝ)^m) :=
    (log2_scale_count X).trans (by linarith [hgmL])
  have hres : (∫ t in α..(α+1/(window X:ℝ)), ‖BulkCircle.S L D t‖^2) ≤
      (scale X:ℝ)/((logScale X:ℝ)^m)^3 :=
    band_cell_of_mangoldt (scale X) L D (window X) α ((logScale X:ℝ)^m)
      hN hupper hHp hgR hlog hlarge (by
        intro C hCN
        have he := mangoldt_prefix_energy (scale X) (mobiusCutoff X) C hCN hcut.2.1 hcut.2.2
          ((logScale X:ℝ)^m) α (α+1/(window X:ℝ)) hgR (by linarith [one_div_pos.mpr hHpR])
          hlog2 (fun j hj b hb =>
            by simpa only [h30] using hboxes C hCN j hj b hb α a q hqlo hqhi hc happ)
        simpa only [mangoldtPrefix_eq_prefixPoly] using he)
  have h3 : ((logScale X:ℝ)^m)^3 = (logScale X:ℝ)^(3*m) := by
    rw [← pow_mul, Nat.mul_comm m 3]
  simpa only [h3] using hres



/-! ### Parametric geometry -/

theorem geometryM (m : ℕ) (hm : 1 ≤ m) :
    ∀ᶠ X : ℕ in Filter.atTop,
      2 * denCutM m X ≤ appBoundM m X ∧
      4 * denCutM m X * appBoundM m X ≤ window X ∧
      0 < physicalWindow X ∧
      4 * majCutM m X ≤ centralWidth X ∧
      (X : ℝ) ^ (17 / 36 : ℝ) ≤ (progWinM m X : ℝ) ∧
      4 ≤ appBoundM m X ∧
      (8 : ℝ) ^ (4 * m + 1) + 8 ≤ (logScale X : ℝ) ^ m := by
  have hprog : ∀ᶠ X : ℕ in Filter.atTop,
      (X : ℝ) ^ (17 / 36 : ℝ) ≤ (progWinM m X : ℝ) := by
    simpa only [progWinM, appBoundM, Nat.div_div_eq_div_mul] using
      BeaumontLowScales.eventually_divided_window_power (2000 * m)
  have hcut : ∀ᶠ X : ℕ in Filter.atTop, 4 * majCutM m X ≤ centralWidth X := by
    filter_upwards [GoldbachBeaumontParameters.eventually_mul_logScale_power_le_rpow
        384 (by norm_num) (18 * m) 1 (by norm_num)] with X hX
    norm_num only [Real.rpow_one] at hX
    have hXN : 384 * logScale X ^ (18 * m) ≤ X := by exact_mod_cast hX
    change 4 * majCutM m X ≤ 3 * X / 32
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 32)).mpr
    calc
      4 * majCutM m X * 32 = 128 * logScale X ^ (18 * m) := by dsimp [majCutM]; ring
      _ ≤ 384 * logScale X ^ (18 * m) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ X := hXN
      _ ≤ 3 * X := by omega
  filter_upwards [GoldbachBeaumontParameters.logScale_tendsto.eventually_ge_atTop 1000000,
      GoldbachBeaumontParameters.eventually_mul_logScale_power_le_rpow
        1 (by norm_num) (1000 * m) (17 / 36) (by norm_num),
      hprog, hcut, Filter.eventually_ge_atTop (1000000 : ℕ),
      (GoldbachBeaumontParameters.logScale_tendsto.eventually_ge_atTop
        (8 ^ (4 * m + 1) + 8))] with X hg hQ hP hC hX hg8
  have hg1 : 1 ≤ logScale X := by omega
  have hQ' : (denCutM m X : ℝ) ≤ (X : ℝ) ^ (17 / 36 : ℝ) := by
    simpa only [denCutM, Nat.cast_pow, one_mul] using hQ
  have hQh : (denCutM m X : ℝ) ≤ (progWinM m X : ℝ) := hQ'.trans hP
  have hQhn : denCutM m X ≤ progWinM m X := by exact_mod_cast hQh
  have hqr : 2 * denCutM m X ≤ appBoundM m X := by
    have hr : 24 * progWinM m X ≤ appBoundM m X := Nat.mul_div_le (appBoundM m X) 24
    omega
  have hpow' : 4 ≤ logScale X ^ (1000 * m) := by
    calc 4 ≤ logScale X ^ 2 := by nlinarith
      _ ≤ logScale X ^ (1000 * m) := pow_le_pow_right₀ hg1 (by omega)
  have hpow : 4 ≤ denCutM m X := hpow'
  have hsq : 4 * denCutM m X ≤ logScale X ^ (2000 * m) := by
    dsimp [denCutM]
    have h2 : 4 * logScale X ^ (1000 * m) ≤ (logScale X ^ (1000 * m)) ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul_right _ hpow'
    have h3 : (logScale X ^ (1000 * m)) ^ 2 = logScale X ^ (2000 * m) := by
      rw [← pow_mul]; congr 1; omega
    rwa [h3] at h2
  have hdiv : logScale X ^ (2000 * m) * appBoundM m X ≤ window X :=
    Nat.mul_div_le (window X) (logScale X ^ (2000 * m))
  have hQH : 4 * denCutM m X * appBoundM m X ≤ window X :=
    (Nat.mul_le_mul_right (appBoundM m X) hsq).trans hdiv
  have hHp : 24 ≤ window X := Nat.le_sqrt'.mpr (by omega)
  have hphys : 0 < physicalWindow X := Nat.div_pos hHp (by norm_num)
  have hR4 : 4 ≤ appBoundM m X := by omega
  have hg8' : (8 : ℝ) ^ (4 * m + 1) + 8 ≤ (logScale X : ℝ) ^ m := by
    have h1 : (8 : ℝ) ^ (4 * m + 1) + 8 ≤ (logScale X : ℝ) := by exact_mod_cast hg8
    have h2 : (1 : ℝ) ≤ (logScale X : ℝ) := by exact_mod_cast hg1
    calc (8 : ℝ) ^ (4 * m + 1) + 8 ≤ (logScale X : ℝ) := h1
      _ ≤ (logScale X : ℝ) ^ m := le_self_pow₀ h2 (by omega)
  exact ⟨hqr, hQH, hphys, hC, hP, hR4, hg8'⟩

/-! ### Parametric major/minor package -/

theorem majCutM_eq_root (m X : ℕ) (hm : 1 ≤ m) :
    majCutM m X = BulkCircle.root (18 * m - 18) (3 * X) := by
  have h : 18 * m - 18 + 18 = 18 * m := by omega
  dsimp [majCutM, BulkCircle.root, GoldbachMajorArc.Polylog.cutoff, logScale]
  rw [h]

noncomputable def majorCoefficientM (m X y n : ℕ) : ℂ :=
  GoldbachBlockGeometry.majorContribution (majCutM m X) (centralWidth X)
    (BulkCircle.integrand (centralStart X y) (centralWidth X) n)

noncomputable def minorCoefficientM (m X y n : ℕ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (majArcsM m X)ᶜ.indicator
    (BulkCircle.integrand (centralStart X y) (centralWidth X) n) t

theorem majArcsM_measurable (m X : ℕ) : MeasurableSet (majArcsM m X) :=
  GoldbachEstermann.measurable_block_arcs _ _

theorem major_add_minorM (m X y n : ℕ) :
    majorCoefficientM m X y n + minorCoefficientM m X y n =
      ∫ t in (0 : ℝ)..1, BulkCircle.integrand (centralStart X y) (centralWidth X) n t := by
  have hc : Continuous (BulkCircle.integrand (centralStart X y) (centralWidth X) n) := by
    unfold BulkCircle.integrand BulkCircle.S GoldbachMajorArc.primeSum
      GoldbachMajorArc.phase
    fun_prop
  exact WindowBessel.ExceptionalCoefficients.indicator_integral_split
    (majArcsM_measurable m X) (hc.intervalIntegrable 0 1)

theorem eventually_major_floor_rootM (m : ℕ) (hm : 1 ≤ m) :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ y : ℕ, X ≤ y → y ≤ 2 * X →
      ∀ n ∈ Icc y (y + Nat.sqrt X), Even n →
      (centralWidth X : ℝ) / 288 ≤
        (GoldbachBlockGeometry.majorContribution (majCutM m X) (centralWidth X)
          (BulkCircle.integrand (centralStart X y) (centralWidth X) n)).re := by
  filter_upwards [GoldbachBeaumontMainArc.eventually_major_floor_root (18 * m - 18)] with X hX y hy hy2 n hn heven
  simpa only [majCutM_eq_root m X hm] using hX y hy hy2 n hn heven

theorem major_minor_packageM (m : ℕ) (hm : 1 ≤ m) :
    ∀ᶠ X : ℕ in Filter.atTop, 1024 ≤ X ∧ ∀ y : ℕ, X ≤ y → y ≤ 2 * X →
      ∀ n ∈ GoldbachBeaumont.centralHoles X y,
        majorCoefficientM m X y n + minorCoefficientM m X y n = 0 ∧
          (X : ℝ) / 4096 ≤ (majorCoefficientM m X y n).re := by
  filter_upwards [GoldbachBeaumontMainArc.eventually_sqrt_small,
      eventually_major_floor_rootM m hm] with X hsmall hmajor
  refine ⟨hsmall.1, ?_⟩
  intro y hy hy2 n hn
  have hnwin := (mem_filter.mp hn).1
  have heven := (mem_filter.mp hn).2.1
  have hcount := (mem_filter.mp hn).2.2
  obtain ⟨hL, hupper, hxD, hcentral, hfreq⟩ :=
    GoldbachBeaumontMainArc.fixed_window_geometry hsmall.1 hsmall.2 hy hy2
  constructor
  · rw [major_add_minorM]
    exact GoldbachBeaumontFourier.full_coefficient_zero hupper
      (fun k hk1 hk2 => (hcentral n hnwin k hk1 hk2).2) hcount
  · exact (GoldbachBeaumontMainArc.centralWidth_floor hsmall.1).trans
      (hmajor y hy hy2 n hnwin heven)

theorem minorCoefficient_eq_maskedM (m X y n : ℕ) :
    minorCoefficientM m X y n = GoldbachBeaumontLocalBessel.maskedCoeff (majArcsM m X)ᶜ
      (fun t => (BulkCircle.S (centralStart X y) (centralWidth X) t) ^ 2) n := by
  unfold minorCoefficientM GoldbachBeaumontLocalBessel.maskedCoeff BulkCircle.integrand
  simp_rw [GoldbachBeaumontLocalBessel.conj_wave]
  rfl

theorem global_band_energyM (N L D : ℕ) (hupper : L + D + 1 ≤ N)
    (W : Set ℝ) (hW : MeasurableSet W) :
    (∫ t in (0 : ℝ)..1, W.indicator (fun u => ‖BulkCircle.S L D u‖ ^ 2) t) ≤
      ((N : ℝ) + 1) * (Real.log N) ^ 2 :=
  GoldbachBeaumontFinish.global_band_energy N L D hupper W hW

theorem eventual_global_band_energyM (m : ℕ) :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ y : ℕ, X ≤ y → y ≤ 2 * X →
      (∫ t in (0 : ℝ)..1, (majArcsM m X)ᶜ.indicator
        (fun u => ‖BulkCircle.S (centralStart X y) (centralWidth X) u‖ ^ 2) t) ≤
        (4 * (X : ℝ)) * (logScale X : ℝ) ^ 2 := by
  filter_upwards [GoldbachBeaumontMainArc.eventually_sqrt_small,
      GoldbachBeaumontParameters.logScale_tendsto.eventually_ge_atTop 32]
    with X hsmall hg
  intro y hy hy2
  obtain ⟨hL, hupper, hsize, hcentral, hfreq⟩ :=
    GoldbachBeaumontMainArc.fixed_window_geometry hsmall.1 hsmall.2 hy hy2
  have hX : 0 < X := by omega
  have hmargin := GoldbachBeaumontParameters.natural_log_margin hX hg
  have hN : 0 < (scale X : ℝ) := by dsimp [scale]; positivity
  have hlog : Real.log (3 * X : ℕ) ≤ (logScale X : ℝ) := by
    have hh := Real.log_le_log hN
      (show (scale X : ℝ) ≤ 64 * (scale X : ℝ) by nlinarith)
    change Real.log (3 * X : ℕ) ≤ _
    dsimp [scale] at hh hmargin
    linarith
  have hNN : ((3 * X : ℕ) : ℝ) + 1 ≤ 4 * (X : ℝ) := by
    have : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
    push_cast
    linarith
  exact (global_band_energyM (3 * X) (centralStart X y) (centralWidth X)
    hupper (majArcsM m X)ᶜ (majArcsM_measurable m X).compl).trans
    (mul_le_mul hNN (pow_le_pow_left₀ (Real.log_natCast_nonneg _) hlog 2)
      (sq_nonneg _) (by positivity))

/-! ### Parametric low-denominator branch -/

theorem low_denominator_cellM (m : ℕ) (hm : 1 ≤ m)
    (hprefix : ∀ᶠ X : ℕ in Filter.atTop, ∀ n : ℕ, scale X ≤ 10 * n → n ≤ scale X →
      BeaumontSmallModuliPolylog.totalError n (denCutM m X) (pktRadM m X) ≤
        (8 : ℝ) ^ (4 * m) * (scale X : ℝ) / (logScale X : ℝ) ^ (4 * m))
    (hpkt : ∀ X : ℕ, 4 ≤ appBoundM m X →
      0 ≤ pktRadM m X ∧ pktRadM m X ≤ 1 / 2 ∧
        6 * (progWinM m X : ℝ) * pktRadM m X ≤ 1) :
    lowBound m := by
  filter_upwards [hprefix, geometryM m hm,
      GoldbachBeaumontParameters.logScale_tendsto.eventually_ge_atTop 1000000,
      Filter.eventually_ge_atTop (1 : ℕ)] with X herror hgeom hg hX
  intro L D q a j hL hD hmajor hq hqP ha hc happrox
  obtain ⟨_hqr, _hQH, _hphys, _hcut, _hprog, hR4, hg8⟩ := hgeom
  let g : ℝ := logScale X
  let N : ℝ := scale X
  let H : ℝ := window X
  let R : ℝ := appBoundM m X
  let c : ℝ := (a : ℝ) / (q : ℝ)
  let l : ℝ := (j : ℝ) / H
  let u : ℝ := ((j : ℝ) + 1) / H
  have hgR : (1000000 : ℝ) ≤ g := by dsimp [g]; exact_mod_cast hg
  have hg0 : 0 < g := by linarith only [hgR]
  have hg1 : 1 ≤ g := by linarith only [hgR]
  have hN0 : 0 ≤ N := by positivity
  have hRp : 0 < R := by dsimp [R]; exact_mod_cast (by omega : 0 < appBoundM m X)
  have hRH : appBoundM m X ≤ window X := Nat.div_le_self _ _
  have hHp : 0 < H := by dsimp [H]; exact_mod_cast (by omega : 0 < window X)
  have hqp : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  obtain ⟨hδ, hδhalf, hw⟩ := hpkt X hR4
  have hinv : 1 / ((q : ℝ) * R) ≤ 1 / R := by
    apply one_div_le_one_div_of_le hRp
    nlinarith only [mul_nonneg (sub_nonneg.mpr hq1) hRp.le]
  have hnear : |l - c| ≤ 1 / R := happrox.trans hinv
  have habs := abs_le.mp hnear
  have hlu : l ≤ u := by
    dsimp [l, u]
    exact div_le_div_of_nonneg_right (by linarith) hHp.le
  have hu_eq : u = l + 1 / H := by dsimp [u, l]; ring
  have hl : c - pktRadM m X ≤ l := by
    have hinvH : 0 ≤ 1 / H := by positivity
    dsimp [pktRadM] at *
    change -(1 / R) ≤ l - c ∧ l - c ≤ 1 / R at habs
    change c - (1 / R + 1 / H) ≤ l
    linarith
  have hu : u ≤ c + pktRadM m X := by
    change u ≤ c + (1 / R + 1 / H)
    rw [hu_eq]
    linarith only [habs.2]
  have hmainpos : 0 < majCutM m X := pow_pos (logScale_pos X) _
  have he := BeaumontLowPacket.cell_minor_energy L D q a (majCutM m X)
    (denCutM m X) hq hqP ha hc hmainpos hmajor (pktRadM m X) l u
    hδ hδhalf hlu hl hu
  have hLhi : L ≤ scale X := by omega
  have hLupper : scale X ≤ 10 * (L + D + 1) := by omega
  have heL := herror L hL hLhi
  have heU := herror (L + D + 1) hLupper hD
  have hDp : (D : ℝ) + 1 ≤ N := by
    dsimp [N]
    exact_mod_cast (show D + 1 ≤ scale X by omega)
  have hmaincast : ((majCutM m X : ℕ) : ℝ) = g ^ (18 * m) := by
    simp only [majCutM, Nat.cast_pow, g]
  change (∫ t in l..u, _) ≤ N / g ^ (3 * m)
  apply he.trans
  rw [hmaincast]
  change BeaumontSmallModuliPolylog.totalError L (denCutM m X) (pktRadM m X) ≤
    8 ^ (4 * m) * N / g ^ (4 * m) at heL
  change BeaumontSmallModuliPolylog.totalError (L + D + 1) (denCutM m X) (pktRadM m X) ≤
    8 ^ (4 * m) * N / g ^ (4 * m) at heU
  have hmodel : 8 * ((D : ℝ) + 1) / g ^ (18 * m) ≤ 8 * N / g ^ (4 * m) := by
    calc
      _ ≤ 8 * N / g ^ (18 * m) := div_le_div_of_nonneg_right (by linarith only [hDp]) (by positivity)
      _ ≤ 8 * N / g ^ (4 * m) := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ hg1 (by omega : 4 * m ≤ 18 * m))
  have hconst : (8 : ℝ) * 8 ^ (4 * m) + 8 ≤ g ^ m := by
    have hg8' : (8 : ℝ) ^ (4 * m + 1) + 8 ≤ g ^ m := hg8
    have h1 : (8 : ℝ) * 8 ^ (4 * m) = 8 ^ (4 * m + 1) := by
      rw [pow_succ]; ring
    linarith [hg8']
  calc
    _ ≤ 4 * (8 ^ (4 * m) * N / g ^ (4 * m) + 8 ^ (4 * m) * N / g ^ (4 * m)) +
        8 * N / g ^ (4 * m) := by gcongr
    _ = (8 * 8 ^ (4 * m) + 8) * N / g ^ (4 * m) := by ring
    _ ≤ N / g ^ (3 * m) := by
      apply (div_le_div_iff₀ (by positivity : 0 < g ^ (4 * m))
        (by positivity : 0 < g ^ (3 * m))).2
      calc
        _ = (8 * 8 ^ (4 * m) + 8) * (N * g ^ (3 * m)) := by ring
        _ ≤ g ^ m * (N * g ^ (3 * m)) :=
          mul_le_mul_of_nonneg_right hconst (by positivity)
        _ = N * (g ^ m * g ^ (3 * m)) := by ring
        _ = N * g ^ (m + 3 * m) := by rw [← pow_add]
        _ = N * g ^ (4 * m) := by rw [show m + 3 * m = 4 * m by ring]

/-! ### Cell-local minor-arc bound -/

theorem local_minorM (m : ℕ) (hm : 1 ≤ m) (hhigh : highBound m) (hlow : lowBound m) :
    cellBound m := by
  filter_upwards [GoldbachBeaumontCompletion.eventually_central_low_geometry, hhigh, hlow,
      geometryM m hm, Filter.eventually_ge_atTop (1 : ℕ)] with X hcentral hhi hlo hgeom hX
  intro y hy hy2 j hj
  obtain ⟨hL, hupper, hmajor18⟩ := hcentral y hy hy2
  obtain ⟨hqr, _hQH, _hphys, hcut, _hprog, _hR4, _hg8⟩ := hgeom
  have hQpos : 0 < denCutM m X := pow_pos (logScale_pos X) _
  have hRpos : 0 < appBoundM m X := by omega
  have hHp : 0 < window X := hRpos.trans_le (Nat.div_le_self _ _)
  have hHr : 0 < (window X : ℝ) := by exact_mod_cast hHp
  let α : ℝ := (j : ℝ) / (window X : ℝ)
  have hα : α ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [α]; positivity
    · apply (div_le_one hHr).mpr
      exact_mod_cast hj.le
  obtain ⟨q, a, hq, hqR, ha, hc, happ⟩ :=
    GoldbachBeaumontHigh.endpoint_approximant (appBoundM m X) hRpos α hα
  by_cases hqsmall : q ≤ denCutM m X
  · have hD : 2 * majCutM m X ≤ centralWidth X := by omega
    simpa only [majArcsM, scale, window, Nat.cast_mul, Nat.cast_ofNat] using
      hlo (centralStart X y) (centralWidth X) q a j hL hupper hD hq hqsmall ha hc happ
  · have hqbig : denCutM m X < q := Nat.lt_of_not_ge hqsmall
    have he := hhi (centralStart X y) (centralWidth X) hupper α a q hqbig hqR hc happ
    have hS : Continuous (BulkCircle.S (centralStart X y) (centralWidth X)) := by
      unfold BulkCircle.S GoldbachMajorArc.primeSum GoldbachMajorArc.phase
      fun_prop
    have hmask := GoldbachBeaumontHigh.masked_cell_le (majArcsM m X)ᶜ
      (majArcsM_measurable m X).compl _ hS
      α (α + 1 / (window X : ℝ)) (by linarith [one_div_pos.mpr hHr])
    have hend : α + 1 / (window X : ℝ) = ((j : ℝ) + 1) / (window X : ℝ) := by
      dsimp [α]; ring
    have hresult := hmask.trans he
    rw [hend] at hresult
    simpa only [α, scale, window, Nat.cast_mul, Nat.cast_ofNat] using hresult

/-! ### Exceptional sets and the single-scale window bound -/

def excSetM (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun n => 4 ≤ n ∧ Even n ∧
    ∀ p ∈ Finset.range (n + 1), ¬(Nat.Prime p ∧ Nat.Prime (n - p)))

def sqWindowM (X y : ℕ) : Finset ℕ :=
  excSetM (Finset.Icc y (y + Nat.sqrt X))

private theorem sq_div_pow_le (A g : ℝ) (m : ℕ)
    (hg : 1 ≤ g) (hA : 0 ≤ A) (hm : 1 ≤ m) :
    A * g ^ 2 / g ^ (3 * m) ≤ A / g ^ m := by
  have hgm : (0 : ℝ) < g ^ m := pow_pos (by linarith) m
  have h1 : g ^ 2 ≤ g ^ (2 * m) := pow_le_pow_right₀ hg (by omega)
  have h2 : g ^ (3 * m) = g ^ (2 * m) * g ^ m := by
    rw [← pow_add]; congr 1; omega
  have hA' : A * g ^ 2 ≤ A * g ^ (2 * m) := mul_le_mul_of_nonneg_left h1 hA
  have h3 : A * g ^ 2 / g ^ (2 * m) ≤ A := (div_le_iff₀ (by positivity)).mpr hA'
  rw [h2]
  calc A * g ^ 2 / (g ^ (2 * m) * g ^ m) = (A * g ^ 2 / g ^ (2 * m)) / g ^ m := by ring
    _ ≤ A / g ^ m := div_le_div_of_nonneg_right h3 hgm.le

theorem sqWindowM_subset_centralHoles (X y : ℕ) :
    sqWindowM X y ⊆ GoldbachBeaumont.centralHoles X y := by
  intro n hn
  obtain ⟨hnIcc, _h4, heven, hnp⟩ := Finset.mem_filter.mp hn
  refine Finset.mem_filter.mpr ⟨hnIcc, heven, ?_⟩
  have hemp : GoldbachBeaumont.centralPrimes n = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    have hp' := GoldbachBeaumont.mem_centralPrimes.mp hp
    have hmem : p ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    exact hnp p hmem ⟨hp'.1, hp'.2.2.1⟩
  rw [GoldbachBeaumont.centralCount, hemp, Finset.card_empty]

theorem window_boundM (m : ℕ) (hm : 1 ≤ m) (hcell : cellBound m) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in Filter.atTop, ∀ y : ℕ, X ≤ y → y ≤ 2 * X →
      ((sqWindowM X y).card : ℝ) ≤
        C * (Nat.sqrt X : ℝ) / (logScale X : ℝ) ^ m := by
  refine ⟨24 * (1 + 4 * Real.pi) * 4096 ^ 2, by positivity, ?_⟩
  filter_upwards [hcell, major_minor_packageM m hm, eventual_global_band_energyM m,
      logScale_tendsto.eventually_ge_atTop 32]
    with X hlocal hmain hglobal hgX
  intro y hy hy2
  have hX : 0 < X := by omega
  have hroot : 0 < Nat.sqrt X := Nat.sqrt_pos.2 hX
  have hgr : 0 < (logScale X : ℝ) := by
    exact_mod_cast logScale_pos X
  have hg1 : (1 : ℝ) ≤ (logScale X : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ logScale X)
  have hS : Continuous (BulkCircle.S (centralStart X y) (centralWidth X)) := by
    unfold BulkCircle.S GoldbachMajorArc.primeSum GoldbachMajorArc.phase
    fun_prop
  have hb := GoldbachBeaumontLocalBessel.masked_square_window_bessel (Nat.sqrt X) y hroot
    (majArcsM m X)ᶜ (majArcsM_measurable m X).compl _ hS
    (((3 * X : ℕ) : ℝ) / (logScale X : ℝ) ^ (3 * m))
    (by positivity) (hlocal y hy hy2)
  simp_rw [← minorCoefficient_eq_maskedM] at hb
  have hsmall : (∑ n ∈ GoldbachBeaumont.evenWindow X y,
      ‖minorCoefficientM m X y n‖ ^ 2) ≤
      ((24 * (1 + 4 * Real.pi) * 4096 ^ 2) * (Nat.sqrt X : ℝ) /
        (logScale X : ℝ) ^ m) * ((X : ℝ) / 4096) ^ 2 := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc y (y + Nat.sqrt X),
          ‖minorCoefficientM m X y n‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => sq_nonneg _)
      _ ≤ _ := hb
      _ ≤ (2 * (1 + 4 * Real.pi) * (Nat.sqrt X : ℝ) *
            (((3 * X : ℕ) : ℝ) / (logScale X : ℝ) ^ (3 * m))) *
          ((4 * (X : ℝ)) * (logScale X : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (hglobal y hy hy2) (by positivity)
      _ = (24 * (1 + 4 * Real.pi) * (Nat.sqrt X : ℝ) * (X : ℝ) ^ 2) *
            (logScale X : ℝ) ^ 2 / (logScale X : ℝ) ^ (3 * m) := by
        push_cast; field_simp; ring
      _ ≤ (24 * (1 + 4 * Real.pi) * (Nat.sqrt X : ℝ) * (X : ℝ) ^ 2) /
            (logScale X : ℝ) ^ m :=
        sq_div_pow_le _ _ m hg1 (by positivity) hm
      _ = _ := by ring
  have hcard := GoldbachBeaumont.centralHoles_card_le_of_complex_energy X y
    (majorCoefficientM m X y) (minorCoefficientM m X y)
    ((X : ℝ) / 4096)
    ((24 * (1 + 4 * Real.pi) * 4096 ^ 2) * (Nat.sqrt X : ℝ) /
      (logScale X : ℝ) ^ m)
    (by positivity)
    (fun n hn => (hmain.2 y hy hy2 n hn).1)
    (fun n hn => (hmain.2 y hy hy2 n hn).2) hsmall
  have hsub := Finset.card_le_card (sqWindowM_subset_centralHoles X y)
  have hcard' : ((sqWindowM X y).card : ℝ) ≤
      ((GoldbachBeaumont.centralHoles X y).card : ℝ) := by exact_mod_cast hsub
  exact hcard'.trans hcard

/-! ### Covering a long window by square-root windows -/

theorem coverM (a b s : ℕ) (hs : 0 < s) :
    (excSetM (Finset.Icc a b)).card ≤
      ∑ i ∈ Finset.range ((b - a) / s + 1),
        (excSetM (Finset.Icc (a + i * s) (a + i * s + (s - 1)))).card := by
  have hsub : excSetM (Finset.Icc a b) ⊆
      (Finset.range ((b - a) / s + 1)).biUnion
        (fun i => excSetM (Finset.Icc (a + i * s) (a + i * s + (s - 1)))) := by
    intro n hn
    obtain ⟨hnIcc, hP⟩ := Finset.mem_filter.mp hn
    obtain ⟨ha, hb⟩ := Finset.mem_Icc.mp hnIcc
    refine Finset.mem_biUnion.mpr ⟨(n - a) / s, Finset.mem_range.mpr ?_, ?_⟩
    · have hdiv : (n - a) / s ≤ (b - a) / s := by
        exact Nat.div_le_div_right (by omega)
      omega
    · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hP⟩
      · have h1 := Nat.div_mul_le_self (n - a) s
        omega
      · have h1 : (n - a) / s * s + (n - a) % s = n - a := by
          rw [mul_comm]; exact Nat.div_add_mod (n - a) s
        have h2 := Nat.mod_lt (n - a) hs
        omega
  calc (excSetM (Finset.Icc a b)).card
      ≤ ((Finset.range ((b - a) / s + 1)).biUnion _).card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Finset.range ((b - a) / s + 1),
          (excSetM (Finset.Icc (a + i * s) (a + i * s + (s - 1)))).card :=
        Finset.card_biUnion_le

theorem log_le_logScale {X M : ℕ} (hX : 0 < X)
    (hM : X ≤ 2 * M) (hg : 4 ≤ logScale M) :
    Real.log (X : ℝ) ≤ (logScale M : ℝ) := by
  set L := logScale M
  have hlt : 3 * M + 2 < 2 ^ (L + 1) := by
    dsimp [L, logScale]
    exact Nat.lt_pow_succ_log_self (by decide) (3 * M + 2)
  have hMpos : 0 < M := by omega
  have hXM : (X : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hM
  have hMpos' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
  have harg : (0 : ℝ) < ((3 * M + 2 : ℕ) : ℝ) := by positivity
  have hstep1 : Real.log (X : ℝ) ≤ Real.log ((3 * M + 2 : ℕ) : ℝ) := by
    apply Real.log_le_log (by exact_mod_cast hX)
    push_cast
    linarith
  have hstep2 : Real.log ((3 * M + 2 : ℕ) : ℝ) ≤ Real.log ((2 : ℝ) ^ (L + 1)) := by
    apply Real.log_le_log harg
    exact_mod_cast hlt.le
  have hstep3 : Real.log ((2 : ℝ) ^ (L + 1)) = ((L : ℝ) + 1) * Real.log 2 := by
    rw [Real.log_pow]; push_cast; ring
  have hlog2 : Real.log 2 ≤ 7 / 10 := by linarith [Real.log_two_lt_d9]
  have hL4 : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hg
  nlinarith

theorem excSetM_Icc_zero (X : ℕ) :
    excSetM (Finset.Icc 0 X) =
      (Finset.range (X + 1)).filter (fun n => 4 ≤ n ∧ Even n ∧
        ((Finset.range (n + 1)).filter
          (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).card = 0) := by
  ext n
  simp only [excSetM, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_range, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Nat.lt_succ_iff,
    Nat.zero_le, true_and]

theorem final_of_window_bound
    (hwin : ∀ (m : ℕ), 1 ≤ m → ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in Filter.atTop,
      ∀ y : ℕ, X ≤ y → y ≤ 2 * X →
      ((sqWindowM X y).card : ℝ) ≤
        C * (Nat.sqrt X : ℝ) / (logScale X : ℝ) ^ m) :
    ∀ (x1 : ℝ), (0 : ℝ) < x1 → ∃ (x3 : ℝ) (x4 : ℝ), (0 : ℝ) < x3 ∧ (0 : ℝ) < x4 ∧
      ∃ (x5 : ℕ), ∀ (x6 x7 : ℕ), x5 ≤ x6 → x7 ≤ x6 → x6 ≤ x7 ^ (2 : ℕ) →
      ↑x6 ^ (7 / 120 : ℝ) * Real.log ↑x6 ^ x3 ≤ ↑x7 →
      ↑{x12 ∈ Finset.Icc (x6 - x7) x6 | (4 : ℕ) ≤ x12 ∧ Even x12 ∧
        ∀ x13 ∈ Finset.range (x12 + (1 : ℕ)),
          ¬(Nat.Prime x13 ∧ Nat.Prime (x12 - x13))}.card ≤
        x4 * ↑x7 / Real.log ↑x6 ^ x1 := by
  intro x1 hx1
  have hA : (0 : ℝ) ≤ x1 := le_of_lt hx1
  let m : ℕ := ⌈x1⌉₊ + 1
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hmR : x1 ≤ (m : ℝ) := by
    have h : x1 ≤ (⌈x1⌉₊ : ℝ) := Nat.le_ceil x1
    dsimp [m]; push_cast; linarith
  obtain ⟨C, hC, hwin_ev⟩ := hwin m hm
  obtain ⟨X1, hwin'⟩ := Filter.eventually_atTop.mp hwin_ev
  have hglob := Conjectures.Goldbach.EstermannAlmostAllPolylog
  dsimp only at hglob
  obtain ⟨X2, hest⟩ := hglob.1 x1 hx1
  have hgs_ev : ∀ᶠ X : ℕ in Filter.atTop, 4 ≤ logScale (X / 2) := by
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
      (logScale_tendsto.eventually_ge_atTop 4)
    filter_upwards [Filter.eventually_ge_atTop (2 * T)] with X hX
    exact hT (X / 2) (by omega)
  obtain ⟨X3, hX3w⟩ := Filter.eventually_atTop.mp hgs_ev
  refine ⟨1, 2 * C + 2, by norm_num, by linarith, max (max (2 * X1) X2) (max X3 4), ?_⟩
  intro X H hX5 hHle hHsq _hside
  have hX1 : X1 ≤ X := by omega
  have hX1half : X1 ≤ X / 2 := by omega
  have hX2 : X2 ≤ X := by omega
  have hX3le : X3 ≤ X := by omega
  have hX4 : 4 ≤ X := by omega
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hlogX1 : (1 : ℝ) ≤ Real.log (X : ℝ) := by
    have : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 3 ≤ X)
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 3) this
    linarith [Real.log_three_gt_d9]
  have hrpow_pos : 0 < (Real.log (X : ℝ)) ^ x1 := Real.rpow_pos_of_pos hlogX _
  have hHr : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  by_cases hcase : 2 * H ≤ X
  · set M := X - H
    have hMhalf : X / 2 ≤ M := by omega
    have hM1 : X1 ≤ M := by omega
    have hMH : H ≤ M := by omega
    have hmono : logScale (X / 2) ≤ logScale M := by
      dsimp [logScale]
      exact Nat.log_mono_right (by omega)
    have hgM : 4 ≤ logScale M := (hX3w X hX3le).trans hmono
    have hlog_le : Real.log (X : ℝ) ≤ (logScale M : ℝ) :=
      log_le_logScale (by omega) (by omega) hgM
    have hcov := coverM M X (Nat.sqrt M + 1) (by omega)
    have hXM' : X - M = H := by omega
    rw [hXM'] at hcov
    have hterm : ∀ i ∈ Finset.range (H / (Nat.sqrt M + 1) + 1),
        ((excSetM (Finset.Icc (M + i * (Nat.sqrt M + 1))
            (M + i * (Nat.sqrt M + 1) + (Nat.sqrt M + 1 - 1)))).card : ℝ) ≤
          C * (Nat.sqrt M : ℝ) / (logScale M : ℝ) ^ m := by
      intro i hi
      have hi' : i ≤ H / (Nat.sqrt M + 1) := by
        have := Finset.mem_range.mp hi; omega
      have his : i * (Nat.sqrt M + 1) ≤ H :=
        le_trans (Nat.mul_le_mul_right _ hi') (Nat.div_mul_le_self H _)
      have hy1 : M ≤ M + i * (Nat.sqrt M + 1) := Nat.le_add_right _ _
      have hy2 : M + i * (Nat.sqrt M + 1) ≤ 2 * M := by omega
      have hwb := hwin' M hM1 (M + i * (Nat.sqrt M + 1)) hy1 hy2
      have heq : excSetM (Finset.Icc (M + i * (Nat.sqrt M + 1))
            (M + i * (Nat.sqrt M + 1) + (Nat.sqrt M + 1 - 1))) =
          sqWindowM M (M + i * (Nat.sqrt M + 1)) := by
        dsimp [sqWindowM]
      rw [heq]
      exact hwb
    have hsum : (∑ i ∈ Finset.range (H / (Nat.sqrt M + 1) + 1),
        ((excSetM (Finset.Icc (M + i * (Nat.sqrt M + 1))
            (M + i * (Nat.sqrt M + 1) + (Nat.sqrt M + 1 - 1)))).card : ℝ)) ≤
        ((H / (Nat.sqrt M + 1) + 1 : ℕ) : ℝ) *
          (C * (Nat.sqrt M : ℝ) / (logScale M : ℝ) ^ m) := by
      calc _ ≤ ∑ _i ∈ Finset.range (H / (Nat.sqrt M + 1) + 1),
            (C * (Nat.sqrt M : ℝ) / (logScale M : ℝ) ^ m) :=
          Finset.sum_le_sum hterm
        _ = _ := by simp
    have hKN : (H / (Nat.sqrt M + 1) + 1) * Nat.sqrt M ≤ 2 * H := by
      have h1 : H / (Nat.sqrt M + 1) * Nat.sqrt M ≤ H := by
        calc H / (Nat.sqrt M + 1) * Nat.sqrt M
            ≤ H / (Nat.sqrt M + 1) * (Nat.sqrt M + 1) :=
              Nat.mul_le_mul_left _ (Nat.le_succ _)
          _ ≤ H := Nat.div_mul_le_self H _
      have hN : Nat.sqrt M ≤ H := by
        have hM2 : M ≤ H ^ 2 := le_trans (by omega) hHsq
        have := Nat.sqrt_le_sqrt hM2
        rwa [Nat.sqrt_eq'] at this
      have h2 : (H / (Nat.sqrt M + 1) + 1) * Nat.sqrt M =
          H / (Nat.sqrt M + 1) * Nat.sqrt M + Nat.sqrt M := by ring
      omega
    have hKNr : ((H / (Nat.sqrt M + 1) + 1 : ℕ) : ℝ) * (Nat.sqrt M : ℝ) ≤ 2 * (H : ℝ) := by
      exact_mod_cast hKN
    have hLnn : (0 : ℝ) ≤ (logScale M : ℝ) ^ m := by positivity
    have htotal : ((excSetM (Finset.Icc M X)).card : ℝ) ≤
        2 * C * (H : ℝ) / (logScale M : ℝ) ^ m := by
      calc ((excSetM (Finset.Icc M X)).card : ℝ)
          ≤ (∑ i ∈ Finset.range (H / (Nat.sqrt M + 1) + 1),
              ((excSetM (Finset.Icc (M + i * (Nat.sqrt M + 1))
                (M + i * (Nat.sqrt M + 1) + (Nat.sqrt M + 1 - 1)))).card : ℝ)) := by
            exact_mod_cast hcov
        _ ≤ ((H / (Nat.sqrt M + 1) + 1 : ℕ) : ℝ) *
              (C * (Nat.sqrt M : ℝ) / (logScale M : ℝ) ^ m) := hsum
        _ = C * (((H / (Nat.sqrt M + 1) + 1 : ℕ) : ℝ) * (Nat.sqrt M : ℝ)) /
              (logScale M : ℝ) ^ m := by ring
        _ ≤ C * (2 * (H : ℝ)) / (logScale M : ℝ) ^ m :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hKNr hC.le) hLnn
        _ = 2 * C * (H : ℝ) / (logScale M : ℝ) ^ m := by ring
    have hLpow : (Real.log (X : ℝ)) ^ x1 ≤ (logScale M : ℝ) ^ (m : ℕ) := by
      calc (Real.log (X : ℝ)) ^ x1
          ≤ (Real.log (X : ℝ)) ^ (m : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hlogX1 hmR
        _ ≤ (logScale M : ℝ) ^ (m : ℝ) :=
            Real.rpow_le_rpow (le_of_lt hlogX) hlog_le (Nat.cast_nonneg m)
        _ = (logScale M : ℝ) ^ (m : ℕ) := by
            rw [Real.rpow_natCast]
    have hfin : ((excSetM (Finset.Icc M X)).card : ℝ) ≤
        2 * C * (H : ℝ) / (Real.log (X : ℝ)) ^ x1 := by
      calc _ ≤ 2 * C * (H : ℝ) / (logScale M : ℝ) ^ m := htotal
        _ ≤ 2 * C * (H : ℝ) / (Real.log (X : ℝ)) ^ x1 :=
            div_le_div_of_nonneg_left (by positivity) hrpow_pos hLpow
    calc ((excSetM (Finset.Icc M X)).card : ℝ)
        ≤ 2 * C * (H : ℝ) / (Real.log (X : ℝ)) ^ x1 := hfin
      _ ≤ (2 * C + 2) * (H : ℝ) / (Real.log (X : ℝ)) ^ x1 := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hrpow_pos)
          nlinarith
  · have hsub : excSetM (Finset.Icc (X - H) X) ⊆ excSetM (Finset.Icc 0 X) := by
      intro n hn
      obtain ⟨hnIcc, hP⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨Finset.Icc_subset_Icc_left (Nat.zero_le _) hnIcc, hP⟩
    have hcard : ((excSetM (Finset.Icc (X - H) X)).card : ℝ) ≤
        ((excSetM (Finset.Icc 0 X)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    rw [excSetM_Icc_zero X] at hcard
    have hestX := hest X hX2
    have h2H : (X : ℝ) ≤ 2 * (H : ℝ) := by exact_mod_cast (by omega : X ≤ 2 * H)
    have hfin : ((excSetM (Finset.Icc (X - H) X)).card : ℝ) ≤
        2 * (H : ℝ) / (Real.log (X : ℝ)) ^ x1 := by
      calc ((excSetM (Finset.Icc (X - H) X)).card : ℝ)
          ≤ ((Finset.range (X + 1)).filter (fun n => 4 ≤ n ∧ Even n ∧
              ((Finset.range (n + 1)).filter
                (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).card = 0)).card := hcard
        _ ≤ (X : ℝ) * (Real.log (X : ℝ)) ^ (-x1) := hestX
        _ ≤ 2 * (H : ℝ) * (Real.log (X : ℝ)) ^ (-x1) :=
            mul_le_mul_of_nonneg_right h2H (le_of_lt (Real.rpow_pos_of_pos hlogX _))
        _ = 2 * (H : ℝ) / (Real.log (X : ℝ)) ^ x1 := by
            rw [Real.rpow_neg (le_of_lt hlogX), div_eq_mul_inv]
    calc ((excSetM (Finset.Icc (X - H) X)).card : ℝ)
        ≤ 2 * (H : ℝ) / (Real.log (X : ℝ)) ^ x1 := hfin
      _ ≤ (2 * C + 2) * (H : ℝ) / (Real.log (X : ℝ)) ^ x1 := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hrpow_pos)
          nlinarith
end Conjectures.Cuts.Task474580c269b155c270797611_aux

theorem Conjectures.Cuts.Task474580c269b155c270797611 :
    ∀ (x1 : ℝ), (0 : ℝ) < x1 → ∃ (x3 : ℝ) (x4 : ℝ), (0 : ℝ) < x3 ∧ (0 : ℝ) < x4 ∧ ∃ (x5 : ℕ), ∀ (x6 x7 : ℕ), x5 ≤ x6 → x7 ≤ x6 → x6 ≤ x7 ^ (2 : ℕ) → ↑x6 ^ (7 / 120 : ℝ) * Real.log ↑x6 ^ x3 ≤ ↑x7 → ↑{x12 ∈ Finset.Icc (x6 - x7) x6 | (4 : ℕ) ≤ x12 ∧ Even x12 ∧ ∀ x13 ∈ Finset.range (x12 + (1 : ℕ)), ¬(Nat.Prime x13 ∧ Nat.Prime (x12 - x13))}.card ≤ x4 * ↑x7 / Real.log ↑x6 ^ x1 :=
  Conjectures.Cuts.Task474580c269b155c270797611_aux.final_of_window_bound
    (fun m hm => Conjectures.Cuts.Task474580c269b155c270797611_aux.window_boundM m hm
      (Conjectures.Cuts.Task474580c269b155c270797611_aux.local_minorM m hm
        (Conjectures.Cuts.Task474580c269b155c270797611_aux.high_cells m hm
          (Conjectures.Cuts.Task474580c269b155c270797611_aux.all_box_cells m hm
            (Conjectures.Cuts.Task474580c269b155c270797611_aux.typeII_cells m hm)
            (Conjectures.Cuts.Task474580c269b155c270797611_aux.residual_cells m hm)))
        (Conjectures.Cuts.Task474580c269b155c270797611_aux.low_denominator_cellM m hm
          (Conjectures.Cuts.Task474580c269b155c270797611_aux.prefix_errorM m hm)
          (Conjectures.Cuts.Task474580c269b155c270797611_aux.pktRadM_bounds m))))
