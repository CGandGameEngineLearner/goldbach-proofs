import Mathlib

noncomputable section

private def boct_w (k : ℕ) : ℝ := if k.Prime then Real.log k else 0

private def boct_phase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

private def boct_spec (n : ℕ) (a : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (a k : ℂ) * boct_phase ((k : ℝ) * t)

private def boct_arcs (n : ℕ) : Set ℝ :=
  let Q := (Nat.log 2 (n + 2)) ^ 2
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ (Q : ℝ) / ((q : ℝ) * (n : ℝ))}

private def boct_low (n k : ℕ) : ℝ := if k ^ 3 ≤ n then boct_w k else 0

private def boct_high (n k : ℕ) : ℝ := boct_w k - boct_low n k

private def boct_K (n : ℕ) (t : ℝ) : ℝ :=
  let L := max 1 (Nat.log 2 n / 2)
  (∑ j ∈ Finset.range L, Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) / (L : ℝ)

private def boct_J (n : ℕ) (v : ℝ → ℝ) : ℝ :=
  (intervalIntegral (fun t => (boct_arcs n)ᶜ.indicator
    (fun u => (v u : ℂ) * boct_spec n (boct_high n) u *
      boct_spec n (boct_high n) u * boct_phase (-(n : ℝ) * u)) t)
    (0 : ℝ) 1 MeasureTheory.volume).re

private def boct_kernelIntegrand (n : ℕ) (v : ℝ → ℝ) (t : ℝ) : ℂ :=
  (boct_arcs n)ᶜ.indicator
    (fun u => (v u : ℂ) * boct_spec n (boct_high n) u *
      boct_spec n (boct_high n) u * boct_phase (-(n : ℝ) * u)) t

private theorem boct_measurableArcs (n : ℕ) : MeasurableSet (boct_arcs n) := by
  let Q := (Nat.log 2 (n + 2)) ^ 2
  let Index := {p : ℕ × ℕ //
    1 ≤ p.1 ∧ p.1 ≤ Q ∧ p.2 ≤ p.1 ∧ Nat.Coprime p.2 p.1}
  have cover : boct_arcs n = ⋃ i : Index,
      {t : ℝ | |t - (i.val.2 : ℝ) / (i.val.1 : ℝ)| ≤
        (Q : ℝ) / ((i.val.1 : ℝ) * (n : ℝ))} := by
    ext t
    constructor
    · rintro ⟨q, a, hq, hQ, ha, hc, ht⟩
      exact Set.mem_iUnion.mpr ⟨⟨(q, a), hq, hQ, ha, hc⟩, ht⟩
    · intro ht
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ht
      exact ⟨i.val.1, i.val.2, i.property.1, i.property.2.1,
        i.property.2.2.1, i.property.2.2.2, hi⟩
  rw [cover]
  exact MeasurableSet.iUnion fun _ =>
    (isClosed_le (continuous_abs.comp (continuous_id.sub continuous_const))
      continuous_const).measurableSet

private theorem boct_kernelIntegrable (n : ℕ) (v : ℝ → ℝ) (hv : Continuous v) :
    IntervalIntegrable (boct_kernelIntegrand n v) MeasureTheory.volume (0 : ℝ) 1 := by
  have cont : Continuous (fun u : ℝ =>
      (v u : ℂ) * boct_spec n (boct_high n) u *
        boct_spec n (boct_high n) u * boct_phase (-(n : ℝ) * u)) := by
    unfold boct_spec boct_phase
    fun_prop
  have h := cont.intervalIntegrable (μ := MeasureTheory.volume) 0 1
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by norm_num : (0 : ℝ) ≤ 1)] at h ⊢
  exact h.indicator (boct_measurableArcs n).compl

private def boct_cutoff (n : ℕ) : ℝ :=
  1 / (2304 * (1 + (Real.log (n : ℝ)) ^ 2))

private def boct_small (n : ℕ) (t : ℝ) : ℝ :=
  max (-(boct_cutoff n)) (min (boct_cutoff n) (1 - boct_K n t))

private def boct_rest (n : ℕ) (t : ℝ) : ℝ :=
  1 - boct_K n t - boct_small n t

private theorem boct_defectSplit (n : ℕ) :
    boct_J n (fun t => 1 - boct_K n t) =
      boct_J n (boct_small n) +
        boct_J n (fun t => 1 - boct_K n t - boct_small n t) := by
  have hk : Continuous (boct_K n) := by
    unfold boct_K
    fun_prop
  have hd : Continuous (fun t : ℝ => 1 - boct_K n t) :=
    continuous_const.sub hk
  have hs : Continuous (boct_small n) :=
    continuous_const.max (continuous_const.min hd)
  have hr : Continuous (fun t : ℝ => 1 - boct_K n t - boct_small n t) :=
    hd.sub hs
  have hsum : boct_kernelIntegrand n (fun t => 1 - boct_K n t) = fun t =>
      boct_kernelIntegrand n (boct_small n) t +
        boct_kernelIntegrand n
          (fun t => 1 - boct_K n t - boct_small n t) t := by
    funext t
    by_cases ht : t ∈ (boct_arcs n)ᶜ
    · simp only [boct_kernelIntegrand, Set.indicator_of_mem ht,
        Complex.ofReal_sub, Complex.ofReal_one]
      ring
    · simp [boct_kernelIntegrand, ht]
  change (intervalIntegral (boct_kernelIntegrand n _) 0 1
    MeasureTheory.volume).re = _
  rw [hsum, intervalIntegral.integral_add
    (boct_kernelIntegrable n _ hs) (boct_kernelIntegrable n _ hr)] <;> rfl

private theorem boct_restToDefect
    (cap : ∀ n : ℕ, 2 ≤ n →
      |boct_J n (boct_small n)| ≤ (n : ℝ) / 1152)
    (far : ∃ N : ℕ, ∀ n ≥ N, Even n →
      -(n : ℝ) / 1152 ≤ boct_J n (boct_rest n)) :
    ∃ N : ℕ, ∀ n ≥ N, Even n →
      -(n : ℝ) / 576 ≤ boct_J n (fun t => 1 - boct_K n t) := by
  obtain ⟨N, hN⟩ := far
  refine ⟨max 2 N, ?_⟩
  intro n hn he
  rw [boct_defectSplit]
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hnN : N ≤ n := le_trans (le_max_right _ _) hn
  have hs := (abs_le.mp (cap n hn2)).1
  have hr := hN n hnN he
  have hs' : -(n : ℝ) / 1152 ≤ boct_J n (boct_small n) := by
    simpa only [neg_div] using hs
  change -(n : ℝ) / 1152 ≤
    boct_J n (fun t => 1 - boct_K n t - boct_small n t) at hr
  calc
    -(n : ℝ) / 576 = -(n : ℝ) / 1152 + -(n : ℝ) / 1152 := by ring
    _ ≤ boct_J n (boct_small n) +
        boct_J n (fun t => 1 - boct_K n t - boct_small n t) :=
      by linarith only [hs', hr]

theorem Conjectures.Goldbach.BulkOffCoherenceTransfer :
    (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let J := fun (n : ℕ) (v : ℝ → ℝ) => (intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => (v u:ℂ)*S n (high n) u*S n (high n) u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume).re; let τ := fun n : ℕ => 1/(2304*(1+(Real.log (n:ℝ))^2)); let small := fun (n : ℕ) (t : ℝ) => max (-(τ n)) (min (τ n) (1-K n t)); ∀ n : ℕ, 2 ≤ n → |J n (small n)| ≤ (n:ℝ)/1152) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let J := fun (n : ℕ) (v : ℝ → ℝ) => (intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => (v u:ℂ)*S n (high n) u*S n (high n) u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume).re; let τ := fun n : ℕ => 1/(2304*(1+(Real.log (n:ℝ))^2)); let small := fun (n : ℕ) (t : ℝ) => max (-(τ n)) (min (τ n) (1-K n t)); ∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/1152 ≤ J n (fun t => 1-K n t-small n t)) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let J := fun (n : ℕ) (v : ℝ → ℝ) => (intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => (v u:ℂ)*S n (high n) u*S n (high n) u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume).re; ∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/576 ≤ J n (fun t => 1-K n t)) := by
  dsimp only
  intro hcap hfar
  change (∀ n : ℕ, 2 ≤ n →
    |boct_J n (boct_small n)| ≤ (n : ℝ) / 1152) at hcap
  change (∃ N : ℕ, ∀ n ≥ N, Even n →
    -(n : ℝ) / 1152 ≤ boct_J n (boct_rest n)) at hfar
  change ∃ N : ℕ, ∀ n ≥ N, Even n →
    -(n : ℝ) / 576 ≤ boct_J n (fun t => 1 - boct_K n t)
  exact boct_restToDefect hcap hfar
