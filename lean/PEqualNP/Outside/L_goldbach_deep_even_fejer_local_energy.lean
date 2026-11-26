import Mathlib

open scoped BigOperators
open MeasureTheory

private theorem energy_sum {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℂ)
    (hg : ∀ i ∈ s, IntervalIntegrable (g i) volume 0 1) :
    ((∑ i ∈ s, ‖∫ t in (0:ℝ)..1, g i t‖ ^ 2 : ℝ) : ℂ) =
    ∫ u in (0:ℝ)..1, ∫ v in (0:ℝ)..1, ∑ i ∈ s, g i u * (starRingEnd ℂ) (g i v) := by
  classical
  have hstar (i : ι) (hi : i ∈ s) :
      IntervalIntegrable (fun v => (starRingEnd ℂ) (g i v)) volume 0 1 :=
    ⟨Complex.conjCLE.toContinuousLinearMap.integrable_comp (hg i hi).1,
      Complex.conjCLE.toContinuousLinearMap.integrable_comp (hg i hi).2⟩
  have hinner (u : ℝ) :
      (∫ v in (0:ℝ)..1, ∑ i ∈ s, g i u * (starRingEnd ℂ) (g i v)) =
      ∑ i ∈ s, g i u * (starRingEnd ℂ) (∫ v in (0:ℝ)..1, g i v) := by
    rw [intervalIntegral.integral_finsetSum (fun i hi => (hstar i hi).const_mul (g i u))]
    simp only [intervalIntegral.integral_const_mul, intervalIntegral.intervalIntegral_conj]
  simp_rw [hinner]
  rw [intervalIntegral.integral_finsetSum (fun i hi => (hg i hi).mul_const _)]
  simp only [intervalIntegral.integral_mul_const, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_sum]



private noncomputable def wave (x : ℝ) : ℂ :=
  Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
private def freq (m H i j : ℕ) := m + 2 * (i + (H - 1) - j)

private lemma wave_add (a b : ℝ) : wave (a+b) = wave a * wave b := by
  unfold wave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma conj_wave (a : ℝ) : (starRingEnd ℂ) (wave a) = wave (-a) := by
  unfold wave
  have two : (starRingEnd ℂ) 2 = 2 := map_ofNat _ _
  rw [← Complex.exp_conj]
  congr 1
  simp
  push_cast
  rw [two]
  simp

private theorem fejer_kernel (_n m H : ℕ) (u v : ℝ) (f : ℝ → ℂ) :
    (∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
      (f u * wave (-(freq m H i j:ℝ)*u)) *
      (starRingEnd ℂ) (f v * wave (-(freq m H i j:ℝ)*v))) =
    f u * (starRingEnd ℂ) (f v) * wave (-((m+2*(H-1):ℕ):ℝ)*(u-v)) *
      ((‖∑ j ∈ Finset.range H, wave (2*(j:ℝ)*(u-v))‖^2:ℝ):ℂ) := by
  let z := fun i : ℕ => wave (2*(i:ℝ)*(u-v))
  let c := f u * (starRingEnd ℂ) (f v) * wave (-((m+2*(H-1):ℕ):ℝ)*(u-v))
  have hterm (i : ℕ) (hi : i ∈ Finset.range H) (j : ℕ) (hj : j ∈ Finset.range H) :
      (f u * wave (-(freq m H i j:ℝ)*u)) *
        (starRingEnd ℂ) (f v * wave (-(freq m H i j:ℝ)*v)) =
        c * ((starRingEnd ℂ) (z i) * z j) := by
    have hj' := Finset.mem_range.mp hj
    have hsub : j ≤ i + (H-1) := by omega
    have hfreq : (freq m H i j:ℝ) = (m:ℝ) + 2*((i:ℝ)+(↑(H-1):ℝ)-(j:ℝ)) := by
      unfold freq
      push_cast [Nat.cast_sub hsub]
      ring
    dsimp [c,z]
    rw [map_mul, conj_wave, conj_wave]
    set a := -(freq m H i j:ℝ)*u
    set b := -(-(freq m H i j:ℝ)*v)
    calc
      _ = f u * (starRingEnd ℂ) (f v) * (wave a * wave b) := by ring
      _ = f u * (starRingEnd ℂ) (f v) *
          (wave (-((m+2*(H-1):ℕ):ℝ)*(u-v)) *
            (wave (-(2*(i:ℝ)*(u-v))) * wave (2*(j:ℝ)*(u-v)))) := by
        rw [← wave_add, ← wave_add, ← wave_add]
        congr 2
        dsimp [a,b]
        rw [hfreq]
        push_cast
        ring
      _ = _ := by ring
  have hnorm (x : ℂ) : ((‖x‖^2:ℝ):ℂ) = (starRingEnd ℂ) x * x := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  change _ = c * ((‖∑ j ∈ Finset.range H, z j‖^2:ℝ):ℂ)
  rw [hnorm, map_sum, Finset.sum_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  exact hterm i hi j hj


private theorem wide_meas (n A B : ℕ) : MeasurableSet {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤A ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (B:ℝ)/((q:ℝ)*(n:ℝ))} := by
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iUnion
  intro a
  by_cases h : 1≤q ∧ q≤A ∧ a≤q ∧ Nat.Coprime a q
  · have hs : {t : ℝ | 1≤q ∧ q≤A ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (B:ℝ)/((q:ℝ)*(n:ℝ))} =
        {t : ℝ | |t-(a:ℝ)/(q:ℝ)| ≤ (B:ℝ)/((q:ℝ)*(n:ℝ))} := by
      ext t
      exact ⟨fun hx => hx.2.2.2.2, fun hx => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,hx⟩⟩
    rw [hs]
    have hf : Continuous (fun t : ℝ => |t-(a:ℝ)/(q:ℝ)|) := (continuous_id.sub continuous_const).abs
    have hg : Continuous (fun _ : ℝ => (B:ℝ)/((q:ℝ)*(n:ℝ))) := continuous_const
    exact (isClosed_le hf hg).measurableSet
  · have : {t : ℝ | 1≤q ∧ q≤A ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (B:ℝ)/((q:ℝ)*(n:ℝ))} = ∅ := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hh => h ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩
    rw [this]
    exact MeasurableSet.empty

private theorem local_coeff_integ (n r : ℕ) (w : ℕ → ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    IntervalIntegrable (fun t => s.indicator (fun u => (∑ k ∈ Finset.range (n+1), (w k:ℂ)*wave ((k:ℝ)*u))^2) t * wave (-(r:ℝ)*t)) volume 0 1 := by
  let f := fun u : ℝ => (∑ k ∈ Finset.range (n+1), (w k:ℂ)*wave ((k:ℝ)*u))^2
  let g := fun u : ℝ => wave (-(r:ℝ)*u)
  change IntervalIntegrable (fun t => s.indicator f t * g t) volume 0 1
  have hc : Continuous (fun t => f t * g t) := by
    unfold f g wave
    fun_prop
  have hi := intervalIntegrable_iff.mp (hc.intervalIntegrable (μ:=volume) 0 1)
  apply intervalIntegrable_iff.mpr
  simpa only [← Set.indicator_mul_left] using (hi.indicator hs)


theorem PEqualNP.Outside.L_goldbach_deep_even_fejer_local_energy :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let deepCoeff := fun (n m : ℕ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun u => (S n w u)^2 * E (-(m:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let F := fun (n : ℕ) => (wideArcs n)ᶜ.indicator (fun u => (S n w u)^2); ∀ (n m H : ℕ), 0 < H → Even m → n ≤ m → m+4*(H-1) ≤ 2*n → ((∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H, ‖deepCoeff n (m+2*(i+(H-1)-j))‖^2 : ℝ):ℂ) = intervalIntegral (fun u => intervalIntegral (fun v => F n u * (starRingEnd ℂ) (F n v) * E (-((m+2*(H-1):ℕ):ℝ)*(u-v)) * ((‖∑ j ∈ Finset.range H, E (2*(j:ℝ)*(u-v))‖^2:ℝ):ℂ)) (0:ℝ) 1 MeasureTheory.volume) (0:ℝ) 1 MeasureTheory.volume := by
  intro w E S Q Q₁ width wideArcs deepCoeff F n m H hH _ _ _
  let g := fun (p : ℕ × ℕ) (t : ℝ) => F n t * wave (-(freq m H p.1 p.2 : ℝ)*t)
  have hcoeff (i j : ℕ) :
      deepCoeff n (freq m H i j) = ∫ t in (0:ℝ)..1, g (i, j) t := by
    unfold deepCoeff g F
    congr 1
    funext t
    simp only [Set.indicator_mul_left]
    rfl
  have hint : ∀ p ∈ (Finset.range H) ×ˢ (Finset.range H),
      IntervalIntegrable (g p) volume 0 1 := by
    intro p _
    exact local_coeff_integ n (freq m H p.1 p.2) w _ (wide_meas n (Q₁ n) (width n)).compl
  have he := energy_sum ((Finset.range H) ×ˢ (Finset.range H)) g hint
  simp only [Finset.sum_product] at he
  change ((∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H, ‖deepCoeff n (freq m H i j)‖^2 : ℝ):ℂ) = _
  simp_rw [hcoeff]
  apply he.trans
  apply congrArg (fun h : ℝ → ℂ => ∫ u in (0:ℝ)..1, h u)
  funext u
  apply congrArg (fun h : ℝ → ℂ => ∫ v in (0:ℝ)..1, h v)
  funext v
  exact fejer_kernel n m H u v (F n)
