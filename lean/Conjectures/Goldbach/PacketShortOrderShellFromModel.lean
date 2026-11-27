import Mathlib

open scoped Classical
set_option maxHeartbeats 3000000

theorem Conjectures.Goldbach.PacketShortOrderShellFromModel :
  (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2; let G := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)); let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m (W n (fun _ => True)) (fun t => max 0 (F n t - G n t)) ≤ (n:ℝ)/4608) → (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let o := fun n q : ℕ => Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (Q n)+1)^2 ∧ q ∣ 2^j-1; let G := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)); let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n ∩ (W n (fun _ => True))) ∩ W n (o n)) (G n) ≤ (n:ℝ)/4608) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let o := fun n q : ℕ => Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (Q n)+1)^2 ∧ q ∣ 2^j-1; let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n ∩ (W n (fun _ => True))) ∩ W n (o n)) (F n) ≤ (n:ℝ)/2304) := by
  intro h₁ h₂ w E S Q arcs low high L K B W o F m
  let G := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2))
  let region := fun n => (B n ∩ W n (fun _ => True)) ∩ W n (o n)
  change ∃ N : ℕ, ∀ n ≥ N, Even n → m (W n (fun _ => True)) (fun t => max 0 (F n t-G n t)) ≤ (n:ℝ)/4608 at h₁
  change ∃ N : ℕ, ∀ n ≥ N, Even n → m (region n) (G n) ≤ (n:ℝ)/4608 at h₂
  obtain ⟨N,hN⟩ := h₁
  obtain ⟨M,hM⟩ := h₂
  refine ⟨max N M, ?_⟩
  intro n hn he
  have hw (p : ℕ → Prop) : MeasurableSet (W n p) := by
    dsimp only [W]
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion; intro q
    apply MeasurableSet.iUnion; intro a
    by_cases h : 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ a.Coprime q ∧ p q
    · convert (measurableSet_le (f := fun t : ℝ => |t-(a:ℝ)/q|) (g := fun _ => ((Q n:ℝ)^2)/((q:ℝ)*n)) (by fun_prop) measurable_const) using 1
      ext t
      simp only [Set.mem_ofPred_eq]
      exact ⟨fun v => v.2.2.2.2.2, fun v => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, v⟩⟩
    · have emp : {t : ℝ | 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ a.Coprime q ∧ p q ∧ |t-(a:ℝ)/q| ≤ ((Q n:ℝ)^2)/((q:ℝ)*n)} = ∅ := by ext t; simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]; tauto
      rw [emp]; exact MeasurableSet.empty
  have harcs : MeasurableSet (arcs n) := by
    dsimp only [arcs]
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion; intro q
    apply MeasurableSet.iUnion; intro a
    by_cases h : 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ a.Coprime q
    · convert (measurableSet_le (f := fun t : ℝ => |t-(a:ℝ)/q|) (g := fun _ => (Q n:ℝ)/((q:ℝ)*n)) (by fun_prop) measurable_const) using 1
      ext t
      simp only [Set.mem_ofPred_eq]
      exact ⟨fun v => v.2.2.2.2, fun v => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, v⟩⟩
    · have emp : {t : ℝ | 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ a.Coprime q ∧ |t-(a:ℝ)/q| ≤ (Q n:ℝ)/((q:ℝ)*n)} = ∅ := by ext t; simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]; tauto
      rw [emp]; exact MeasurableSet.empty
  have hk : Continuous (K n) := by dsimp [K]; fun_prop
  have hb : MeasurableSet (B n) := harcs.compl.inter (measurableSet_lt (measurable_const (a := (1/2:ℝ))) hk.measurable)
  have hs : MeasurableSet (region n) := (hb.inter (hw _)).inter (hw _)
  have hf : Continuous (F n) := by dsimp [F,S,E]; fun_prop
  have hg : Continuous (G n) := by
    dsimp only [G]
    apply continuous_finsetSum; intro q hq
    apply continuous_finsetSum; intro a ha
    simp only [div_mul_eq_div_div]
    change Continuous (fun t : ℝ => (4*(n:ℝ)^2 / (q.totient:ℝ)^2) / (1+((n:ℝ)*(t-(a:ℝ)/q))^2))
    exact Continuous.div (f := fun _ : ℝ => 4*(n:ℝ)^2 / (q.totient:ℝ)^2) (g := fun t : ℝ => 1+((n:ℝ)*(t-(a:ℝ)/q))^2) continuous_const (by fun_prop) (by intro t; positivity)
  let err := fun t => max 0 (F n t-G n t)
  have hi {s : Set ℝ} (hs : MeasurableSet s) {f : ℝ → ℝ} (hc : Continuous f) :
      IntervalIntegrable (s.indicator f) MeasureTheory.volume 0 1 :=
    ⟨(hc.intervalIntegrable 0 1).1.indicator hs,(hc.intervalIntegrable 0 1).2.indicator hs⟩
  have heint := hi (s := W n (fun _ => True)) (f := err) (hw _) (continuous_const.max (hf.sub hg))
  have hcomp : m (region n) (F n) ≤ m (region n) (G n) + m (W n (fun _ => True)) err := by
    dsimp only [m]
    rw [← intervalIntegral.integral_add (hi hs hg) heint]
    apply intervalIntegral.integral_mono_on (by norm_num) (hi hs hf) ((hi hs hg).add heint)
    intro t ht
    by_cases inside : t ∈ region n
    · have inW : t ∈ W n (fun _ => True) := inside.1.2
      simp only [Set.indicator_of_mem inside, Set.indicator_of_mem inW]
      dsimp only [err]; linarith [le_max_right 0 (F n t - G n t)]
    · simp only [Set.indicator_of_notMem inside, zero_add]
      exact Set.indicator_nonneg (fun _ _ => le_max_left _ _) _
  have h1 := hN n (by omega) he
  have h2 := hM n (by omega) he
  change m (region n) (F n) ≤ _
  change m (W n (fun _ => True)) err ≤ _ at h1
  linarith
