import Mathlib
import Conjectures.Goldbach.ReflectedMeanSquareEulerTail

open Finset

-- The only analytic input in the combination is the verified mean-square estimate.
-- No independence of the discrepancy and the sieve event is used.
private theorem threshold_transport (F : Finset ℕ) (x z : ℕ → ℝ)
    (a b s : ℝ) (hs : 0 < s) (hab : a+s ≤ b) :
    (((F.filter (fun m => x m ≤ a)).card : ℝ)/F.card) ≤
    (((F.filter (fun m => z m ≤ b)).card : ℝ)/F.card) +
      (1/s^2)*((∑ m ∈ F, (x m-z m)^2)/(F.card:ℝ)) := by
  classical
  have h := Finset.sum_le_sum (s := F) (fun m _ => show
      (if x m ≤ a then (1:ℝ) else 0) ≤
        (if z m ≤ b then (1:ℝ) else 0) + (1/s^2)*(x m-z m)^2 by
      have hn : 0 ≤ (1/s^2)*(x m-z m)^2 := by positivity
      split_ifs with hx hz hz
      · linarith
      · have hsq := mul_self_le_mul_self hs.le (show s ≤ z m - x m by linarith)
        have hsq' : s^2 ≤ (x m-z m)^2 := by nlinarith only [hsq]
        rw [zero_add, one_div_mul_eq_div]
        exact (one_le_div (by positivity)).mpr hsq'
      · linarith
      · linarith)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole] at h
  simpa only [add_div, mul_div_assoc] using
    (div_le_div_of_nonneg_right h (Nat.cast_nonneg F.card : 0 ≤ (F.card:ℝ)))

-- child 1 zh: 奇素数 Mertens 乘积：在截点 ⌊1/δ⌋，乘积乘 log(1/δ) 的极限为 2 exp(−γ)。
-- child 1 en: Odd-prime Mertens product at cutoff floor(1/d), including the leading constant.
-- child 2 zh: 有限欧拉模型的筛比较：半宽和双宽两个阈值下的频率，从两侧夹住奇素数筛乘积，归一化误差至多 η。
-- child 2 en: Bracket the odd-prime sieve product by the half-width and double-width finite Euler-model frequencies, within normalized error eta.
theorem Conjectures.Cuts.Cut266b0f4c1d036f599cb7cf5d
  (hM : (by
    classical
    exact ∀ η : ℝ, 0 < η → ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, 0 < d → d < d₀ →
      |Real.log (1/d)*(∏ p ∈ (Finset.Icc 3 ⌊1/d⌋₊).filter Nat.Prime, (1-1/(p:ℝ))) - 2*Real.exp (-Real.eulerMascheroniConstant)| ≤ η))
  (hF : (by
    classical
    let c : ℝ := ∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1/((p : ℝ)-1)^2 else 1
    let band := fun N : ℕ => (Finset.Icc N (2*N)).filter (fun m => 4*N ≤ 3*m ∧ 2*m ≤ 3*N ∧ Even m)
    let model := fun (y m : ℕ) => 2*c * ∏ p ∈ m.primeFactors.filter (fun p => 2 < p ∧ p ≤ y), (1+1/((p:ℝ)-2))
    exact ∀ η : ℝ, 0 < η → ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, 0 < d → d < d₀ →
      ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y → ∃ T : ℕ, ∀ N : ℕ, T ≤ N →
        let F := band N
        let P := fun w : ℝ => (((F.filter (fun m => model y m ≤ 2*c+w)).card : ℝ)/F.card)
        let L := Real.log (1/d)
        let D := ∏ p ∈ (Finset.Icc 3 ⌊1/d⌋₊).filter Nat.Prime, (1-1/(p:ℝ))
        L*D-η ≤ L*P (d/2) ∧ L*P (2*d) ≤ L*D+η)) :
  (by
  classical
  let e := fun t : ℝ => Complex.exp (((2*Real.pi*t : ℝ) : ℂ)*Complex.I)
  let S := fun (N : ℕ) (t : ℝ) => ∑ p ∈ (Finset.range (N+1)).filter Nat.Prime, (Real.log (p : ℝ) : ℂ) * e ((p : ℝ)*t)
  let arcs := fun N : ℕ => let k := Nat.log 2 (N+2); {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ k ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t-(a : ℝ)/(q : ℝ)| ≤ ((k^3 : ℕ) : ℝ)/((q : ℝ)*(N : ℝ))}
  let A := fun N m : ℕ => (intervalIntegral ((arcs N).indicator (fun t : ℝ => (S N t)^2 * e (-(m : ℝ)*t))) (0 : ℝ) 1 MeasureTheory.volume).re
  let C₂ := ∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1/((p : ℝ)-1)^2 else 1
  let band := fun N m : ℕ => 4*N ≤ 3*m ∧ 2*m ≤ 3*N ∧ Even m
  let R := fun N m : ℕ => A N m / (2*(N:ℝ)-(m:ℝ))
  let B := fun N : ℕ => (Finset.Icc N (2*N)).filter (band N)
  let avg := fun (F : Finset ℕ) (f : ℕ → ℝ) => (∑ m ∈ F, f m)/(F.card:ℝ)
  exact ∀ ε : ℝ, 0 < ε → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ T : ℕ, ∀ N : ℕ, T ≤ N →
    let P := (((B N).filter (fun m => R N m ≤ 2*C₂+δ)).card:ℝ)/((B N).card:ℝ)
    |Real.log (1/δ)*P - 2*Real.exp (-Real.eulerMascheroniConstant)| ≤ ε) := by
  classical
  let c : ℝ := ∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1/((p : ℝ)-1)^2 else 1
  let band := fun N : ℕ => (Finset.Icc N (2*N)).filter (fun m => 4*N ≤ 3*m ∧ 2*m ≤ 3*N ∧ Even m)
  let model := fun (y m : ℕ) => 2*c * ∏ p ∈ m.primeFactors.filter (fun p => 2 < p ∧ p ≤ y), (1+1/((p:ℝ)-2))
  let e := fun t : ℝ => Complex.exp (((2*Real.pi*t : ℝ) : ℂ)*Complex.I)
  let S := fun (N : ℕ) (t : ℝ) => ∑ p ∈ (Finset.range (N+1)).filter Nat.Prime, (Real.log (p : ℝ) : ℂ) * e ((p : ℝ)*t)
  let arcs := fun N : ℕ => let k := Nat.log 2 (N+2); {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ k ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t-(a : ℝ)/(q : ℝ)| ≤ ((k^3 : ℕ) : ℝ)/((q : ℝ)*(N : ℝ))}
  let A := fun N m : ℕ => (intervalIntegral ((arcs N).indicator (fun t : ℝ => (S N t)^2 * e (-(m : ℝ)*t))) (0 : ℝ) 1 MeasureTheory.volume).re
  let R := fun N m : ℕ => A N m / (2*(N:ℝ)-(m:ℝ))
  let dens := fun (N : ℕ) (f : ℕ → ℝ) (a : ℝ) =>
    ((((band N).filter (fun m => f m ≤ a)).card:ℝ)/(band N).card)
  change ∀ ε : ℝ, 0 < ε → ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, 0 < d → d < d₀ →
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N →
    |Real.log (1/d)*dens N (R N) (2*c+d)-2*Real.exp (-Real.eulerMascheroniConstant)| ≤ ε
  obtain ⟨C,hC,hMS⟩ := Conjectures.Goldbach.ReflectedMeanSquareEulerTail
  intro ε hε
  let η := ε/4
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨u,hu,hm⟩ := hM η hη
  obtain ⟨v,hv,hf⟩ := hF η hη
  refine ⟨min 1 (min u v), lt_min zero_lt_one (lt_min hu hv), ?_⟩
  intro d hd hsmall
  have hd1 := lt_of_lt_of_le hsmall (min_le_left _ _)
  have hd' := lt_of_lt_of_le hsmall (min_le_right _ _)
  have hprod := hm d hd (lt_of_lt_of_le hd' (min_le_left _ _))
  obtain ⟨Y,hy⟩ := hf d hd (lt_of_lt_of_le hd' (min_le_right _ _))
  let L := Real.log (1/d)
  have hL : 0 < L := Real.log_pos ((one_lt_div hd).mpr hd1)
  let s := d/2
  have hs : 0 < s := by dsimp [s]; positivity
  let K := L*(1/s^2)*C
  obtain ⟨n,hn⟩ := exists_nat_gt (K/η)
  let y := max 3 (max Y n)
  have y3 : 3 ≤ y := le_max_left _ _
  have yY : Y ≤ y := (le_max_left _ _).trans (le_max_right _ _)
  have yn : n ≤ y := (le_max_right _ _).trans (le_max_right _ _)
  have y1 : (1:ℝ) ≤ y := by exact_mod_cast (show 1 ≤ y by omega)
  have yp : (0:ℝ)<y := by linarith
  have hK : K ≤ (y:ℝ)*η := (div_le_iff₀ hη).mp (hn.le.trans (Nat.cast_le.mpr yn))
  have hb : L*(1/s^2)*(C/(y:ℝ)^2) ≤ η := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    exact hK.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr y1) (mul_nonneg yp.le hη.le)])
  obtain ⟨T₁,h₁⟩ := hMS y y3
  obtain ⟨T₂,h₂⟩ := hy y yY
  refine ⟨max T₁ T₂, ?_⟩
  intro N hN
  let V := (∑ m ∈ band N, (R N m-model y m)^2)/((band N).card:ℝ)
  have hV : V ≤ C/(y:ℝ)^2 := h₁ N ((le_max_left _ _).trans hN)
  have herr : L*((1/s^2)*V) ≤ η := by
    rw [← mul_assoc]
    exact (mul_le_mul_of_nonneg_left hV (by positivity)).trans hb
  obtain ⟨lo,hi⟩ := h₂ N ((le_max_right _ _).trans hN)
  let D := ∏ p ∈ (Finset.Icc 3 ⌊1/d⌋₊).filter Nat.Prime, (1-1/(p:ℝ))
  change L*D-η ≤ L*dens N (model y) (2*c+d/2) at lo
  change L*dens N (model y) (2*c+2*d) ≤ L*D+η at hi
  change |L*D-2*Real.exp (-Real.eulerMascheroniConstant)| ≤ η at hprod
  have hlow := threshold_transport (band N) (model y) (R N) (2*c+d/2) (2*c+d) s hs (by dsimp [s]; linarith)
  have hupp := threshold_transport (band N) (R N) (model y) (2*c+d) (2*c+2*d) s hs (by dsimp [s]; linarith)
  have swap (m : ℕ) : (model y m-R N m)^2 = (R N m-model y m)^2 := by ring
  simp only [swap] at hlow
  change dens N (model y) (2*c+d/2) ≤ dens N (R N) (2*c+d)+(1/s^2)*V at hlow
  change dens N (R N) (2*c+d) ≤ dens N (model y) (2*c+2*d)+(1/s^2)*V at hupp
  have hlow' := mul_le_mul_of_nonneg_left hlow hL.le
  have hupp' := mul_le_mul_of_nonneg_left hupp hL.le
  rw [mul_add] at hlow' hupp'
  change |L*dens N (R N) (2*c+d)-2*Real.exp (-Real.eulerMascheroniConstant)| ≤ ε
  have he : 3*η ≤ ε := by dsimp [η]; linarith
  obtain ⟨hm₁,hm₂⟩ := abs_le.mp hprod
  exact abs_le.mpr ⟨by linarith only [hm₁,lo,hlow',herr,he], by linarith only [hm₂,hi,hupp',herr,he]⟩
