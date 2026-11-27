import Mathlib

open MeasureTheory Set

private theorem shell_integral_le {shell window : Set ℝ} {energy model : ℝ → ℝ}
    (included : shell ⊆ window) (measShell : MeasurableSet shell)
    (measWindow : MeasurableSet window) (contEnergy : Continuous energy)
    (contModel : Continuous model) :
    ∫ t in Ioc (0 : ℝ) 1, shell.indicator energy t ≤
      (∫ t in Ioc (0 : ℝ) 1, shell.indicator model t) +
      ∫ t in Ioc (0 : ℝ) 1, window.indicator (fun x => max 0 (energy x - model x)) t := by
  let excess := fun x => max 0 (energy x - model x)
  have intExcess : IntegrableOn (window.indicator excess) (Ioc 0 1) :=
    (continuous_const.max (contEnergy.sub contModel)).integrableOn_Ioc.indicator measWindow
  have intModel : IntegrableOn (shell.indicator model) (Ioc 0 1) :=
    contModel.integrableOn_Ioc.indicator measShell
  rw [← integral_add intModel intExcess]
  apply integral_mono (contEnergy.integrableOn_Ioc.indicator measShell) (intModel.add intExcess)
  intro point
  change shell.indicator energy point ≤ shell.indicator model point + window.indicator excess point
  by_cases inside : point ∈ shell
  · simp only [indicator_of_mem inside, indicator_of_mem (included inside)]
    exact sub_le_iff_le_add'.mp (le_max_right 0 (energy point - model point))
  · simp only [indicator_of_notMem inside, zero_add]
    exact indicator_nonneg (fun _ _ => le_max_left _ _) _

theorem Conjectures.Goldbach.PacketShortOrderShellFromModel :
    (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0;
      let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I);
      let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t));
      let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
      let low := fun (n k : ℕ) => if k^3≤n then w k else 0;
      let high := fun (n k : ℕ) => w k-low n k;
      let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))};
      let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2;
      let G := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2));
      let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume;
      ∃ N : ℕ, ∀ n ≥ N, Even n → m (W n (fun _ => True)) (fun t => max 0 (F n t - G n t)) ≤ (n:ℝ)/4608) →
    (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
      let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))};
      let L := fun n : ℕ => max 1 (Nat.log 2 n / 2);
      let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ);
      let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t};
      let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))};
      let o := fun n q : ℕ => Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (Q n)+1)^2 ∧ q ∣ 2^j-1;
      let G := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2));
      let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume;
      ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n ∩ (W n (fun _ => True))) ∩ W n (o n)) (G n) ≤ (n:ℝ)/4608) →
    (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0;
      let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I);
      let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t));
      let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
      let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))};
      let low := fun (n k : ℕ) => if k^3≤n then w k else 0;
      let high := fun (n k : ℕ) => w k-low n k;
      let L := fun n : ℕ => max 1 (Nat.log 2 n / 2);
      let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ);
      let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t};
      let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))};
      let o := fun n q : ℕ => Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (Q n)+1)^2 ∧ q ∣ 2^j-1;
      let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2;
      let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume;
      ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n ∩ (W n (fun _ => True))) ∩ W n (o n)) (F n) ≤ (n:ℝ)/2304) := by
  intro excessBound modelBound w E S Q arcs low high L K B W order F mass
  let model (n : ℕ) (t : ℝ) :=
    ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
      4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2))
  obtain ⟨thresholdE, estimateE⟩ := excessBound
  obtain ⟨thresholdM, estimateM⟩ := modelBound
  refine ⟨max thresholdE thresholdM, fun n hn evenN => ?_⟩
  let window := W n (fun _ => True)
  let shell := (B n ∩ window) ∩ W n (order n)
  have boundE : mass window (fun t => max 0 (F n t - model n t)) ≤ (n:ℝ)/4608 :=
    estimateE n ((le_max_left ..).trans hn) evenN
  have boundM : mass shell (model n) ≤ (n:ℝ)/4608 :=
    estimateM n ((le_max_right ..).trans hn) evenN
  have measArcs : MeasurableSet (arcs n) := by
    dsimp only [arcs]
    simp only [Set.ofPred_exists, Set.ofPred_and]
    apply MeasurableSet.iUnion; intro q
    apply MeasurableSet.iUnion; intro a
    repeat' apply MeasurableSet.inter (MeasurableSet.const _)
    exact measurableSet_le (continuous_id.sub continuous_const).abs.measurable measurable_const
  have measBand : MeasurableSet (B n) := by
    change MeasurableSet ((arcs n)ᶜ ∩ {t : ℝ | (1:ℝ)/2 < K n t})
    have continuousK : Continuous (K n) := by dsimp only [K]; fun_prop
    exact measArcs.compl.inter (isOpen_lt continuous_const continuousK).measurableSet
  have measWindows (condition : ℕ → Prop) : MeasurableSet (W n condition) := by
    dsimp only [W]
    simp only [Set.ofPred_exists, Set.ofPred_and]
    apply MeasurableSet.iUnion; intro q
    apply MeasurableSet.iUnion; intro a
    repeat' apply MeasurableSet.inter (MeasurableSet.const _)
    exact measurableSet_le (continuous_id.sub continuous_const).abs.measurable measurable_const
  have continuousModel : Continuous (model n) := by
    dsimp only [model]
    simp_rw [← div_div]
    fun_prop (disch := first | intro point; positivity | positivity)
  have continuousEnergy : Continuous (F n) := by dsimp only [F, S, E]; fun_prop
  have included : shell ⊆ window := fun _ member => member.1.2
  have comparison := shell_integral_le included ((measBand.inter (measWindows _)).inter
    (measWindows _)) (measWindows _) continuousEnergy continuousModel
  change mass shell (F n) ≤ (n:ℝ)/2304
  dsimp only [mass] at boundE boundM ⊢
  simp only [intervalIntegral.integral_of_le zero_le_one] at boundE boundM ⊢
  linarith
