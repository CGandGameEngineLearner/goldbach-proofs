import Mathlib

theorem Conjectures.Goldbach.PacketShortOrderPeakOverlapFromFull :
(let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let G := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)); let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, m (B n) (G n) ≤ ε*(n:ℝ)) → (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let o := fun n q : ℕ => Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (Q n)+1)^2 ∧ q ∣ 2^j-1; let G := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)); let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n ∩ (W n (fun _ => True))) ∩ W n (o n)) (G n) ≤ (n:ℝ)/4608) := by
  intro assumed Q arcs L K B W o G m
  obtain ⟨N,hN⟩ := assumed (1/4608) (by norm_num)
  refine ⟨N,?_⟩
  intro n hn _
  have hA : MeasurableSet (arcs n) := by
    dsimp only [arcs]
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion; intro q
    apply MeasurableSet.iUnion; intro a
    by_cases h : 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q
    · simp only [h.1,h.2.1,h.2.2.1,true_and,and_iff_right h.2.2.2]
      exact measurableSet_le (show Measurable (fun t : ℝ => |t-(a:ℝ)/q|) by fun_prop) measurable_const
    · have ze : {t : ℝ | 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))} = ∅ := by
        ext; simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]; tauto
      rw [ze]; exact MeasurableSet.empty
  have hK : Continuous (K n) := by dsimp [K]; fun_prop
  have hB : MeasurableSet (B n) := hA.compl.inter (measurableSet_lt (measurable_const (a:=(1/2:ℝ))) hK.measurable)
  have hG : Continuous (G n) := by
    dsimp only [G]
    apply continuous_finsetSum; intro q hq
    apply continuous_finsetSum; intro a _
    have hp := Nat.totient_pos.mpr (show 0 < q from (Finset.mem_Icc.mp hq).1)
    change Continuous (fun t : ℝ => 4*(n:ℝ)^2 / ((q.totient:ℝ)^2*(1+((n:ℝ)*(t-(a:ℝ)/q))^2)))
    fun_prop (disch := intro t; positivity)
  have hpos (t : ℝ) : 0 ≤ G n t := by dsimp only [G]; positivity
  have restrictBound (S : Set ℝ) (hs : S ⊆ B n) : m S (G n) ≤ m (B n) (G n) := by
    dsimp only [m]; rw [intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_of_le zero_le_one]
    apply MeasureTheory.integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun t => Set.indicator_nonneg (fun x _ => hpos x) _)
    · exact ((hG.intervalIntegrable 0 1).1).indicator hB
    · apply Filter.Eventually.of_forall
      intro t
      by_cases ht : t∈S
      · simp [ht,hs ht]
      · simp only [Set.indicator_of_notMem ht]; exact Set.indicator_nonneg (fun x _ => hpos x) _
  have rhs : m (B n) (G n) ≤ (1/4608)*(n:ℝ) := hN n hn
  exact (restrictBound _ (show (B n ∩ W n (fun _ => True)) ∩ W n (o n) ⊆ B n from fun _ ht => ht.1.1)).trans (by linarith only [rhs])
