import Mathlib

namespace GoldbachFejer

open Finset MeasureTheory
open scoped ComplexConjugate

noncomputable section

def phase (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

private theorem phase_add (x y : ℝ) : phase (x+y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem phase_conj (x : ℝ) : conj (phase x) = phase (-x) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  norm_num
  exact Or.inl (map_ofNat (starRingEnd ℂ) 2)

private theorem square_as_product (z : ℂ) : ((‖z‖^2 : ℝ):ℂ) = conj z * z := by
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]

/-- A finite sum of coefficient energies as an iterated integral. -/
private theorem gram {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℂ)
    (hg : ∀ i ∈ s, IntervalIntegrable (g i) volume 0 1) :
    (∑ i ∈ s, ((‖∫ x in (0:ℝ)..1, g i x‖^2 : ℝ):ℂ)) =
      ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, ∑ i ∈ s, g i x * conj (g i y) := by
  have hc i (hi : i ∈ s) : IntervalIntegrable (fun y => conj (g i y)) volume 0 1 :=
    ⟨Complex.conjCLE.toContinuousLinearMap.integrable_comp (hg i hi).1,
     Complex.conjCLE.toContinuousLinearMap.integrable_comp (hg i hi).2⟩
  have inner (x : ℝ) : (∫ y in (0:ℝ)..1, ∑ i ∈ s, g i x * conj (g i y)) =
      ∑ i ∈ s, g i x * conj (∫ y in (0:ℝ)..1, g i y) := by
    rw [intervalIntegral.integral_finsetSum (fun i hi => (hc i hi).const_mul (g i x))]
    simp_rw [intervalIntegral.integral_const_mul, intervalIntegral.intervalIntegral_conj]
  simp_rw [inner]
  rw [intervalIntegral.integral_finsetSum (fun i hi => (hg i hi).mul_const _)]
  apply sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_mul_const, square_as_product, mul_comm]

/-- Summing over both shifts produces the squared geometric sum. The offset H-1
keeps all frequency indices natural even when j exceeds i. -/
private theorem kernel (F : ℝ → ℂ) (m H : ℕ) (x y : ℝ) :
    ∑ i ∈ range H, ∑ j ∈ range H,
      (F x * phase (-(↑(m+2*(i+(H-1)-j)):ℝ)*x)) *
        conj (F y * phase (-(↑(m+2*(i+(H-1)-j)):ℝ)*y)) =
    F x * conj (F y) * phase (-(↑(m+2*(H-1)):ℝ)*(x-y)) *
      ((‖∑ j ∈ range H, phase (2*(j:ℝ)*(x-y))‖^2 : ℝ):ℂ) := by
  rw [square_as_product, map_sum]
  simp only [phase_conj]
  rw [← mul_assoc]
  simp_rw [mul_sum, sum_mul]
  -- Expand the product with the conjugated index first.
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  have hsub : i ≤ j+(H-1) := by have := mem_range.mp hi; omega
  simp only [map_mul, phase_conj]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hsub, Nat.cast_ofNat]
  simp only [mul_assoc]
  rw [mul_left_comm (phase _) (conj (F y))]
  simp only [← phase_add]
  congr 3
  ring

theorem masked (A : Set ℝ) (hA : MeasurableSet A) (W : ℝ → ℂ) (hW : Continuous W)
    (m H : ℕ) :
    let coeff := fun k : ℕ => ∫ x in (0:ℝ)..1,
      A.indicator (fun u => W u * phase (-(k:ℝ)*u)) x
    ((∑ i ∈ range H, ∑ j ∈ range H, ‖coeff (m+2*(i+(H-1)-j))‖^2 : ℝ):ℂ) =
      ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
        A.indicator W x * conj (A.indicator W y) * phase (-(↑(m+2*(H-1)):ℝ)*(x-y)) *
          ((‖∑ j ∈ range H, phase (2*(j:ℝ)*(x-y))‖^2 : ℝ):ℂ) := by
  intro coeff
  let idx := fun z : ℕ × ℕ => m+2*(z.1+(H-1)-z.2)
  let g := fun (z : ℕ × ℕ) => A.indicator (fun u => W u * phase (-(idx z:ℝ)*u))
  have hg (z : ℕ × ℕ) : IntervalIntegrable (g z) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    apply Integrable.indicator _ hA
    apply Continuous.integrableOn_Icc _ |>.mono_set Set.Ioc_subset_Icc_self
    unfold phase
    fun_prop
  have geq (z : ℕ × ℕ) (x : ℝ) : g z x = A.indicator W x * phase (-(idx z:ℝ)*x) := by
    by_cases hx : x ∈ A <;> simp [g,hx]
  have h := gram (range H ×ˢ range H) g (fun i _ => hg i)
  simp only [sum_product] at h
  simp only [Complex.ofReal_sum]
  change (∑ i ∈ range H, ∑ j ∈ range H, ((‖∫ x in (0:ℝ)..1, g (i,j) x‖^2:ℝ):ℂ)) = _
  apply h.trans
  apply intervalIntegral.integral_congr
  intro x _
  apply intervalIntegral.integral_congr
  intro y _
  simp only [geq, idx]
  exact kernel (A.indicator W) m H x y

end
end GoldbachFejer

theorem PEqualNP.Outside.L_goldbach_deep_even_fejer_local_energy :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let deepCoeff := fun (n m : ℕ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun u => (S n w u)^2 * E (-(m:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let F := fun (n : ℕ) => (wideArcs n)ᶜ.indicator (fun u => (S n w u)^2); ∀ (n m H : ℕ), 0 < H → Even m → n ≤ m → m+4*(H-1) ≤ 2*n → ((∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H, ‖deepCoeff n (m+2*(i+(H-1)-j))‖^2 : ℝ):ℂ) = intervalIntegral (fun u => intervalIntegral (fun v => F n u * (starRingEnd ℂ) (F n v) * E (-((m+2*(H-1):ℕ):ℝ)*(u-v)) * ((‖∑ j ∈ Finset.range H, E (2*(j:ℝ)*(u-v))‖^2:ℝ):ℂ)) (0:ℝ) 1 MeasureTheory.volume) (0:ℝ) 1 MeasureTheory.volume := by
  intro w E S Q cutoff height wide coeff F n m H _ _ _ _
  have hm : MeasurableSet (wide n) := by
    dsimp only [wide]
    simp only [Set.ofPred_exists]
    refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
    let V := {t : ℝ | |t-(a:ℝ)/q| ≤ (height n:ℝ)/((q:ℝ)*n)}
    change MeasurableSet {t | 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ a.Coprime q ∧ t ∈ V}
    by_cases h : 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ a.Coprime q
    · convert (measurableSet_le (measurable_id.sub measurable_const).abs measurable_const : MeasurableSet V) using 1
      ext t
      exact ⟨fun z => z.2.2.2.2, fun z => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,z⟩⟩
    · convert (MeasurableSet.empty : MeasurableSet (∅ : Set ℝ)) using 1
      ext t
      change (_ ∧ _ ∧ _ ∧ _ ∧ t ∈ V) ↔ False
      tauto
  apply GoldbachFejer.masked _ hm.compl (fun t => (S n w t)^2) _ m H
  dsimp only [S,E]
  fun_prop
