import Mathlib

private theorem bbpArcMeas (X : ℕ) (ρ m : ℝ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤X ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ρ/((q:ℝ)*m)} := by
  have h : {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤X ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ρ/((q:ℝ)*m)}
      = ⋃ q : ℕ, ⋃ a : ℕ, ({t : ℝ | 1≤q ∧ q≤X ∧ a≤q ∧ Nat.Coprime a q} ∩ {t : ℝ | |t-(a:ℝ)/(q:ℝ)| ≤ ρ/((q:ℝ)*m)}) := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨q, a, h1, h2, h3, h4, h5⟩
      exact ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
    · rintro ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
      exact ⟨q, a, h1, h2, h3, h4, h5⟩
  rw [h]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  refine (MeasurableSet.const _).inter ?_
  exact measurableSet_le (by fun_prop) (by fun_prop)

private theorem bbpMaskInt (D : Set ℝ) (hD : MeasurableSet D) (g : ℝ → ℂ) (hg : Continuous g) :
    IntervalIntegrable (fun t => D.indicator g t) MeasureTheory.volume (0:ℝ) 1 := by
  have h := hg.intervalIntegrable (μ := MeasureTheory.volume) 0 1
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h ⊢
  exact h.indicator hD

private theorem bbpSplit (D : Set ℝ) (hD : MeasurableSet D) (g : ℝ → ℂ) (hg : Continuous g)
    (v : ℝ → ℝ) (hv : Continuous v) :
    (intervalIntegral (fun t => D.indicator g t) (0:ℝ) 1 MeasureTheory.volume).re =
      (intervalIntegral (fun t => D.indicator (fun u => ((v u:ℝ):ℂ) * g u) t) (0:ℝ) 1 MeasureTheory.volume).re
      + (intervalIntegral (fun t => D.indicator (fun u => (((1 - v u):ℝ):ℂ) * g u) t) (0:ℝ) 1 MeasureTheory.volume).re := by
  have hg1 : Continuous (fun u => ((v u:ℝ):ℂ) * g u) := by fun_prop
  have hg2 : Continuous (fun u => (((1 - v u):ℝ):ℂ) * g u) := by fun_prop
  have hfun : (fun t => D.indicator (fun u => ((v u:ℝ):ℂ) * g u) t
        + D.indicator (fun u => (((1 - v u):ℝ):ℂ) * g u) t) = fun t => D.indicator g t := by
    funext t
    by_cases ht : t ∈ D
    · simp only [Set.indicator_of_mem ht, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    · simp only [Set.indicator_of_notMem ht, add_zero]
  have hadd : (intervalIntegral (fun t => D.indicator (fun u => ((v u:ℝ):ℂ) * g u) t
        + D.indicator (fun u => (((1 - v u):ℝ):ℂ) * g u) t) (0:ℝ) 1 MeasureTheory.volume)
      = (intervalIntegral (fun t => D.indicator (fun u => ((v u:ℝ):ℂ) * g u) t) (0:ℝ) 1 MeasureTheory.volume)
        + (intervalIntegral (fun t => D.indicator (fun u => (((1 - v u):ℝ):ℂ) * g u) t) (0:ℝ) 1 MeasureTheory.volume) :=
    intervalIntegral.integral_add (a := (0:ℝ)) (b := 1) (μ := MeasureTheory.volume)
      (f := fun t => D.indicator (fun u => ((v u:ℝ):ℂ) * g u) t)
      (g := fun t => D.indicator (fun u => (((1 - v u):ℝ):ℂ) * g u) t)
      (bbpMaskInt D hD _ hg1) (bbpMaskInt D hD _ hg2)
  rw [← Complex.add_re, ← hadd, hfun]

theorem Conjectures.Goldbach.BulkBinaryPartition :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let J := fun (n : ℕ) (v : ℝ → ℝ) => (intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => (v u:ℂ)*S n (high n) u*S n (high n) u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume).re; ∀ n : ℕ, (I n (high n) (high n)).re = J n (K n) + J n (fun t => 1-K n t) := by
  intro w E S Q arcs low high I L K J n
  have hmeas : MeasurableSet ((arcs n)ᶜ) :=
    (bbpArcMeas (Q n) ((Q n : ℕ):ℝ) ((n : ℕ):ℝ)).compl
  have hG : Continuous (fun u : ℝ => S n (high n) u * S n (high n) u * E (-(n:ℝ)*u)) := by
    simp only [S, E]
    fun_prop
  have hK : Continuous (K n) := by
    simp only [K]
    fun_prop
  have key := bbpSplit (arcs n)ᶜ hmeas
    (fun u : ℝ => S n (high n) u * S n (high n) u * E (-(n:ℝ)*u)) hG (K n) hK
  simpa only [I, J, mul_assoc] using key
