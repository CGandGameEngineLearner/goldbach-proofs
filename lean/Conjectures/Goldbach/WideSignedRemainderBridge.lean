import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Continuity

noncomputable section

open MeasureTheory

-- The dyadic cutoff and Fourier continuity lemmas are adapted from
-- PEqualNP.Outside.L_goldbach_frontier_three_zone_split (same repository).
private lemma six_le_two_pow (k : ℕ) (hk : 30 ≤ k) : k ^ 6 + 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hratio : (k : ℝ) ≥ 30 := by exact_mod_cast hk
    have hkpos : (0 : ℝ) < k := by linarith
    have h1R : ((k : ℝ) + 1) ^ 6 ≤ 2 * (k : ℝ) ^ 6 := by
      have hquot : ((k : ℝ) + 1) / (k : ℝ) ≤ 11 / 10 := by
        rw [div_le_iff₀ hkpos]
        linarith
      have hpow : (((k : ℝ) + 1) / (k : ℝ)) ^ 6 ≤ ((11 : ℝ) / 10) ^ 6 :=
        pow_le_pow_left₀ (by positivity) hquot 6
      have h2 : ((11 : ℝ) / 10) ^ 6 ≤ 2 := by norm_num
      have hkey : (((k : ℝ) + 1) ^ 6) / (k : ℝ) ^ 6 ≤ 2 := by
        rw [← div_pow]
        exact hpow.trans h2
      have := mul_le_mul_of_nonneg_right hkey (pow_nonneg hkpos.le 6)
      rwa [div_mul_cancel₀ _ (pow_ne_zero 6 hkpos.ne')] at this
    have h1 : (k + 1) ^ 6 ≤ 2 * k ^ 6 := by
      have h1R' : ((k : ℝ) + 1) ^ 6 ≤ 2 * (k : ℝ) ^ 6 := h1R
      exact_mod_cast h1R'
    calc (k + 1) ^ 6 + 2 ≤ 2 * k ^ 6 + 2 := by omega
      _ ≤ 2 * (k ^ 6 + 2) := by omega
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 1) := by rw [Nat.pow_succ]; ring

private lemma cube_le_floor (n Q : ℕ) (h : Q ^ 3 ≤ n) : Q ≤ ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ := by
  have hR : ((Q : ℝ)) ^ 3 ≤ (n : ℝ) := by exact_mod_cast h
  have hpow : (((Q : ℝ)) ^ 3) ^ (1 / 3 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hR (by norm_num)
  have hQid : (((Q : ℝ)) ^ 3) ^ (1 / 3 : ℝ) = (Q : ℝ) := by
    rw [← Real.rpow_natCast (x := (Q : ℝ)) 3]
    rw [← Real.rpow_mul (by positivity)]
    norm_num
  rw [hQid] at hpow
  exact Nat.le_floor hpow

private def arcBand (K : ℕ) (K' : ℝ) (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ K ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ (K' : ℝ) / ((q : ℝ) * (n : ℝ))}

private lemma measurableSet_arcBand (K : ℕ) (K' : ℝ) (n : ℕ) : MeasurableSet (arcBand K K' n) := by
  have hEq : arcBand K K' n =
      ⋃ (p : {p : ℕ × ℕ // 1 ≤ p.1 ∧ p.1 ≤ K ∧ p.2 ≤ p.1 ∧ Nat.Coprime p.2 p.1}),
        {t : ℝ | |t - (p.1.2 : ℝ) / (p.1.1 : ℝ)| ≤ (K' : ℝ) / ((p.1.1 : ℝ) * (n : ℝ))} := by
    ext t
    simp only [arcBand, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨q, a, h1, h2, h3, h4, h5⟩
      exact ⟨⟨(q, a), h1, h2, h3, h4⟩, h5⟩
    · rintro ⟨⟨⟨q, a⟩, h1, h2, h3, h4⟩, h5⟩
      exact ⟨q, a, h1, h2, h3, h4, h5⟩
  rw [hEq]
  exact MeasurableSet.iUnion (fun p =>
    measurableSet_le (Continuous.measurable (by continuity)) measurable_const)

private def wfun (k : ℕ) : ℝ := if Nat.Prime k then Real.log (k : ℝ) else 0

private def Efun (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

private def Sfun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℂ :=
  Finset.sum (Finset.range (n + 1)) (fun k => (u k : ℂ) * Efun ((k : ℝ) * t))

private def Ffun (n : ℕ) (t : ℝ) : ℂ := (Sfun n wfun t) ^ 2 * Efun (-(n : ℝ) * t)

private lemma continuous_Efun : Continuous Efun := by
  unfold Efun
  fun_prop

private lemma continuous_Ffun (n : ℕ) : Continuous (Ffun n) := by
  unfold Ffun
  apply Continuous.mul
  · apply Continuous.pow
    unfold Sfun
    exact continuous_finsetSum _ (fun k hk =>
      Continuous.mul continuous_const (continuous_Efun.comp (by fun_prop)))
  · exact continuous_Efun.comp (by fun_prop)

private lemma cutoff (n : ℕ) (hn : 2^30 ≤ n) : (Nat.log 2 (n+2))^2 ≤ ⌊(n:ℝ)^(1/3:ℝ)⌋₊ := by
  have hk30 : 30 ≤ Nat.log 2 (n + 2) := by
    apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
    omega
  have hk6 : (Nat.log 2 (n + 2)) ^ 6 ≤ n := by
    have h1 : (Nat.log 2 (n + 2)) ^ 6 + 2 ≤ 2 ^ (Nat.log 2 (n + 2)) :=
      six_le_two_pow (Nat.log 2 (n + 2)) hk30
    have h2 : 2 ^ (Nat.log 2 (n + 2)) ≤ n + 2 :=
      Nat.pow_log_le_self 2 (by omega)
    omega
  have hcube : ((Nat.log 2 (n + 2)) ^ 2) ^ 3 ≤ n := by
    have hpow : ((Nat.log 2 (n + 2)) ^ 2) ^ 3 = (Nat.log 2 (n + 2)) ^ 6 := by ring
    rw [hpow]
    exact hk6
  exact cube_le_floor n _ hcube

private lemma integral_split (T L I : Set ℝ) (F : ℝ → ℂ) (sub : L ⊆ T)
    (ht : MeasurableSet T) (hl : MeasurableSet L) (hi : MeasurableSet I)
    (hf : Continuous F) :
    let J := fun A : Set ℝ =>
      (intervalIntegral (fun t => A.indicator F t) (0:ℝ) 1 volume).re
    J T = J L + J ((T \ L) ∩ I) + J ((T \ L) \ I) := by
  let B := (T \ L) ∩ I
  let C := (T \ L) \ I
  have ig (A : Set ℝ) (hA : MeasurableSet A) :
      IntervalIntegrable (fun t => A.indicator F t) volume (0:ℝ) 1 :=
    ⟨(hf.intervalIntegrable 0 1).1.indicator hA, (hf.intervalIntegrable 0 1).2.indicator hA⟩
  have hL := ig L hl
  have hB := ig B ((ht.diff hl).inter hi)
  have hC := ig C ((ht.diff hl).diff hi)
  have hId : (fun t => T.indicator F t) =
      (fun t => (L.indicator F t + B.indicator F t) + C.indicator F t) := by
    funext t
    by_cases h : t ∈ L
    · have h' := sub h
      simp [B,C,h,h',Set.indicator]
    · by_cases hT : t ∈ T <;> by_cases hI : t ∈ I <;> simp [B,C,h,hT,hI,Set.indicator]
  dsimp only
  rw [hId, intervalIntegral.integral_add (hL.add hB) hC,
    intervalIntegral.integral_add hL hB]
  rfl

theorem Conjectures.Goldbach.WideSignedRemainderBridge :
let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowPart := fun n : ℕ => lowWideArcs n \ arcs n; let remainder := fun n : ℕ => (wideArcs n \ arcs n) \ lowPart n; let inner := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n : ℝ) * (n : ℝ)^(1/6 : ℝ) / ((q:ℝ)*(n:ℝ))}; let J := fun (n : ℕ) (A : Set ℝ) => (intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; let floor := fun (A : ℕ → Set ℝ) => ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n:ℝ)) ≤ J n (A n); floor lowPart → (floor (fun n => remainder n ∩ inner n)) → (floor (fun n => remainder n \ inner n)) → (floor (fun n => wideArcs n \ arcs n)) := by
  intro w E S Q arcs f Q₁ H wide low lowPart remainder inner J floor hL hI hO e he
  have ep : 0 < e / 3 := by positivity
  obtain ⟨Nl, hl⟩ := hL (e/3) ep
  obtain ⟨Ni, hi⟩ := hI (e/3) ep
  obtain ⟨No, ho⟩ := hO (e/3) ep
  refine ⟨max (2^30) (max Nl (max Ni No)), ?_⟩
  intro n hn hp
  have hc : Q n ≤ Q₁ n := cutoff n (by omega)
  have hs : lowPart n ⊆ wide n \ arcs n := by
    rintro t ⟨⟨q,a,h1,h2,h3,h4,h5⟩,ha⟩
    exact ⟨⟨q,a,h1,h2.trans hc,h3,h4,h5⟩,ha⟩
  have ha : MeasurableSet (arcs n) := measurableSet_arcBand (Q n) (Q n) n
  have hw : MeasurableSet (wide n) := measurableSet_arcBand (Q₁ n) (H n) n
  have hlow : MeasurableSet (low n) := measurableSet_arcBand (Q n) (H n) n
  have hin : MeasurableSet (inner n) :=
    measurableSet_arcBand (Q₁ n) ((Q n : ℝ) * (n:ℝ)^(1/6:ℝ)) n
  have heq : J n (wide n \ arcs n) = J n (lowPart n) +
      J n (remainder n ∩ inner n) + J n (remainder n \ inner n) :=
    integral_split _ _ _ (f n) hs (hw.diff ha) (hlow.diff ha) hin (continuous_Ffun n)
  have h₁ := hl n (by omega) hp
  have h₂ := hi n (by omega) hp
  have h₃ := ho n (by omega) hp
  change -(e/3*(n:ℝ)) ≤ J n (remainder n ∩ inner n) at h₂
  change -(e/3*(n:ℝ)) ≤ J n (remainder n \ inner n) at h₃
  rw [heq]
  linarith
