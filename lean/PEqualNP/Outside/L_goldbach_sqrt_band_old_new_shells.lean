import Mathlib

open MeasureTheory Set

/-- Measurability also covers the two copies of the endpoint on the circle. -/
private theorem measurableArcFamily (Q H n : ℕ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a:ℝ)/q| ≤ (H:ℝ)/((q:ℝ)*n)} := by
  simp only [ofPred_exists]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  by_cases h : 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q
  · obtain ⟨hq,hQ,ha,hc⟩ := h
    have heq : {t : ℝ | 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a:ℝ)/q| ≤ (H:ℝ)/((q:ℝ)*n)} = {t : ℝ | |t - (a:ℝ)/q| ≤ (H:ℝ)/((q:ℝ)*n)} := by
      ext t
      exact ⟨fun h => h.2.2.2.2, fun ht => ⟨hq,hQ,ha,hc,ht⟩⟩
    rw [heq]
    exact (isClosed_le (by fun_prop) continuous_const).measurableSet
  · have emptySet : {t : ℝ | 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a:ℝ)/q| ≤ (H:ℝ)/((q:ℝ)*n)} = ∅ := by
      ext t
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨hq,hQ,ha,hc,_⟩
      exact h ⟨hq,hQ,ha,hc⟩
    rw [emptySet]
    exact MeasurableSet.empty

/-- A nested enlargement contributes two disjoint shells and its exterior. -/
private theorem threeShells {A B C : Set ℝ} (hab : A ⊆ B) (hbc : B ⊆ C)
    (ha : MeasurableSet A) (hb : MeasurableSet B) (hc : MeasurableSet C)
    (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ t in (0:ℝ)..1, Aᶜ.indicator f t) =
      (∫ t in (0:ℝ)..1, (B \ A).indicator f t) +
      (∫ t in (0:ℝ)..1, (C \ B).indicator f t) +
      (∫ t in (0:ℝ)..1, Cᶜ.indicator f t) := by
  have integrable := hf.intervalIntegrable (μ := volume) 0 1
  have addShells (t : ℝ) : Aᶜ.indicator f t = (B \ A).indicator f t +
      (C \ B).indicator f t + Cᶜ.indicator f t := by
    by_cases a : t ∈ A
    · simp [Set.indicator, a, hab a, hbc (hab a)]
    by_cases b : t ∈ B
    · simp [Set.indicator, a, b, hbc b]
    by_cases c : t ∈ C <;> simp [Set.indicator, a, b, c]
  simp_rw [addShells]
  have hi (s : Set ℝ) (hs : MeasurableSet s) : IntervalIntegrable (s.indicator f) volume 0 1 :=
    ⟨integrable.1.indicator hs, integrable.2.indicator hs⟩
  exact (intervalIntegral.integral_add ((hi _ (hb.diff ha)).add (hi _ (hc.diff hb)))
    (hi _ hc.compl)).trans (by rw [intervalIntegral.integral_add (hi _ (hb.diff ha)) (hi _ (hc.diff hb))])

theorem PEqualNP.Outside.L_goldbach_sqrt_band_old_new_shells : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let Q₂ := fun n : ℕ => ⌊Real.sqrt (n : ℝ) / ((Nat.log 2 (n + 2) : ℝ) ^ 4)⌋₊; let sqrtArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q₂ n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ ((256 * Q₂ n * Q n : ℕ) : ℝ) / ((q : ℝ) * (n : ℝ))}; ∀ n : ℕ, 0 < n → Q₁ n ≤ Q₂ n → let old := {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q₁ n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/q| ≤ ((256*Q₂ n*Q n:ℕ):ℝ)/((q:ℝ)*n)}; let J := fun A : Set ℝ => intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; J ((wideArcs n)ᶜ) = J (old \ wideArcs n) + J (sqrtArcs n \ old) + J ((sqrtArcs n)ᶜ) := by
  intro w E S Q f Q₁ H wideArcs Q₂ sqrtArcs n _hn hQ old J
  apply threeShells (A := wideArcs n) (B := old) (C := sqrtArcs n)
  · rintro t ⟨q,a,hq,hm,ha,hc,h⟩
    refine ⟨q,a,hq,hm,ha,hc,h.trans ?_⟩
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (Nat.mul_le_mul_right (Q n) (Nat.mul_le_mul_left 256 hQ))
  · rintro t ⟨q,a,hq,hm,ha,hc,h⟩
    exact ⟨q,a,hq,hm.trans hQ,ha,hc,h⟩
  · exact measurableArcFamily .. 
  · exact measurableArcFamily ..
  · exact measurableArcFamily ..
  · dsimp [f, S, E]
    fun_prop