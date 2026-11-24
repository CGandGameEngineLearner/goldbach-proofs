import Mathlib

open MeasureTheory
open scoped ENNReal

private def rotLM (a b : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (a * p.1 + b * p.2, -b * p.1 + a * p.2)
  map_add' p q := by
    apply Prod.ext <;> simp <;> ring
  map_smul' c p := by
    apply Prod.ext <;> simp <;> ring

private def unitBox : Set (ℝ × ℝ) := {q | |q.1| < 1 / 2 ∧ |q.2| < 1 / 2}

private def sqSet (x y a b : ℝ) : Set (ℝ × ℝ) :=
  (fun p : ℝ × ℝ => rotLM a b (p - (x, y))) ⁻¹' unitBox

private lemma abs_comb_lt (p q c d : ℝ) (hp : |p| < 1 / 2) (hq : |q| < 1 / 2)
    (hcd : c ≠ 0 ∨ d ≠ 0) : |c * p + d * q| < (|c| + |d|) / 2 := by
  have htri : |c * p + d * q| ≤ |c| * |p| + |d| * |q| := by
    calc
      |c * p + d * q| ≤ |c * p| + |d * q| := abs_add_le _ _
      _ = |c| * |p| + |d| * |q| := by rw [abs_mul, abs_mul]
  have hstep : |c| * |p| + |d| * |q| < (|c| + |d|) / 2 := by
    rcases hcd with hc | hd
    · have hcpos : 0 < |c| := abs_pos.mpr hc
      have h1 : |c| * |p| < |c| * (1 / 2) := mul_lt_mul_of_pos_left hp hcpos
      have h2 : |d| * |q| ≤ |d| * (1 / 2) := mul_le_mul_of_nonneg_left hq.le (abs_nonneg d)
      have h3 := add_lt_add_of_lt_of_le h1 h2
      have h4 : |c| * (1 / 2) + |d| * (1 / 2) = (|c| + |d|) / 2 := by ring
      linarith
    · have hdpos : 0 < |d| := abs_pos.mpr hd
      have h1 : |d| * |q| < |d| * (1 / 2) := mul_lt_mul_of_pos_left hq hdpos
      have h2 : |c| * |p| ≤ |c| * (1 / 2) := mul_le_mul_of_nonneg_left hp.le (abs_nonneg c)
      have h3 := add_lt_add_of_le_of_lt h2 h1
      have h4 : |c| * (1 / 2) + |d| * (1 / 2) = (|c| + |d|) / 2 := by ring
      linarith
  linarith

private lemma mem_sqSet {x y a b : ℝ} {p : ℝ × ℝ} :
    p ∈ sqSet x y a b ↔
      |a * (p.1 - x) + b * (p.2 - y)| < 1 / 2 ∧
        |(-b) * (p.1 - x) + a * (p.2 - y)| < 1 / 2 := by
  simp only [sqSet, Set.mem_preimage, unitBox, Set.mem_ofPred_eq]
  rfl

private lemma rotLM_det (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) : LinearMap.det (rotLM a b) = 1 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ)]
  have hmat :
      LinearMap.toMatrix (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ) (rotLM a b) =
        !![a, b; -b, a] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [rotLM, LinearMap.toMatrix_apply]
  rw [hmat, Matrix.det_fin_two_of]
  nlinarith [hab]

private lemma volume_unitBox : volume (unitBox : Set (ℝ × ℝ)) = 1 := by
  have hb : (unitBox : Set (ℝ × ℝ)) =
      Set.Ioo (-1 / 2 : ℝ) (1 / 2) ×ˢ Set.Ioo (-1 / 2 : ℝ) (1 / 2) := by
    ext q
    simp [unitBox, abs_lt]
    norm_num
  rw [hb, Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioo]
  norm_num

private lemma unitBox_measurable : MeasurableSet (unitBox : Set (ℝ × ℝ)) := by
  have hb : (unitBox : Set (ℝ × ℝ)) =
      Set.Ioo (-1 / 2 : ℝ) (1 / 2) ×ˢ Set.Ioo (-1 / 2 : ℝ) (1 / 2) := by
    ext q
    simp [unitBox, abs_lt]
    norm_num
  rw [hb]
  exact measurableSet_Ioo.prod measurableSet_Ioo

private lemma rot_continuous (x y a b : ℝ) :
    Continuous (fun p : ℝ × ℝ => rotLM a b (p - (x, y))) := by
  have heq : (fun p : ℝ × ℝ => rotLM a b (p - (x, y))) =
      fun p => (a * (p.1 - x) + b * (p.2 - y), -b * (p.1 - x) + a * (p.2 - y)) := by
    funext p
    rfl
  rw [heq]
  continuity

private lemma sqSet_measurable (x y a b : ℝ) : MeasurableSet (sqSet x y a b) := by
  exact unitBox_measurable.preimage (rot_continuous x y a b).measurable

private lemma volume_sqSet (x y a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    volume (sqSet x y a b) = 1 := by
  have hdet : LinearMap.det (rotLM a b) = 1 := rotLM_det a b hab
  have hsq : sqSet x y a b =
      (fun p : ℝ × ℝ => p - (x, y)) ⁻¹' ((rotLM a b) ⁻¹' unitBox) := rfl
  rw [hsq]
  have htrans : (fun p : ℝ × ℝ => p - (x, y)) = (fun h => (-(x, y)) + h) := by
    funext p
    exact sub_eq_neg_add p (x, y)
  rw [htrans, MeasureTheory.measure_preimage_add]
  have hpre := MeasureTheory.Measure.addHaar_preimage_linearMap (volume : Measure (ℝ × ℝ))
    (f := rotLM a b) (by rw [hdet]; norm_num) unitBox
  rw [hpre, hdet, volume_unitBox]
  norm_num

private lemma sqSet_subset (x y a b s : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (hb1 : |a| + |b| ≤ 2 * x) (hb2 : |a| + |b| ≤ 2 * (s - x))
    (hb3 : |a| + |b| ≤ 2 * y) (hb4 : |a| + |b| ≤ 2 * (s - y)) :
    sqSet x y a b ⊆ Set.Ioo (0 : ℝ) s ×ˢ Set.Ioo (0 : ℝ) s := by
  intro p hp
  rw [mem_sqSet] at hp
  obtain ⟨hp1, hp2⟩ := hp
  have hne : a ≠ 0 ∨ -b ≠ 0 := by
    by_contra h
    rw [not_or] at h
    obtain ⟨ha, hb⟩ := h
    have ha0 : a = 0 := by
      by_contra h'
      exact ha h'
    have hb0 : b = 0 := by
      by_contra h'
      exact hb (by intro hneg; exact h' (by linarith))
    nlinarith [hab]
  have hidX :
      a * (a * (p.1 - x) + b * (p.2 - y)) + (-b) * ((-b) * (p.1 - x) + a * (p.2 - y)) =
        (a ^ 2 + b ^ 2) * (p.1 - x) := by ring
  have hidY :
      b * (a * (p.1 - x) + b * (p.2 - y)) + a * ((-b) * (p.1 - x) + a * (p.2 - y)) =
        (a ^ 2 + b ^ 2) * (p.2 - y) := by ring
  have hX : |p.1 - x| < (|a| + |b|) / 2 := by
    have hbnd := abs_comb_lt (a * (p.1 - x) + b * (p.2 - y))
      ((-b) * (p.1 - x) + a * (p.2 - y)) a (-b) hp1 hp2 hne
    rw [hidX, hab, one_mul] at hbnd
    simpa [abs_neg] using hbnd
  have hY : |p.2 - y| < (|a| + |b|) / 2 := by
    have hne2 : b ≠ 0 ∨ a ≠ 0 := by
      rcases hne with h | h
      · exact Or.inr h
      · exact Or.inl (by intro hb0; exact h (by linarith))
    have hbnd := abs_comb_lt (a * (p.1 - x) + b * (p.2 - y))
      ((-b) * (p.1 - x) + a * (p.2 - y)) b a hp1 hp2 hne2
    rw [hidY, hab, one_mul] at hbnd
    simpa [add_comm] using hbnd
  have hx1 : (|a| + |b|) / 2 ≤ x := by linarith
  have hx2 : (|a| + |b|) / 2 ≤ s - x := by linarith
  have hy1 : (|a| + |b|) / 2 ≤ y := by linarith
  have hy2 : (|a| + |b|) / 2 ≤ s - y := by linarith
  have hX' := abs_lt.mp hX
  have hY' := abs_lt.mp hY
  refine ⟨⟨by linarith [hX'.1, hx1], by linarith [hX'.2, hx2]⟩,
    ⟨by linarith [hY'.1, hy1], by linarith [hY'.2, hy2]⟩⟩

private lemma area_aux :
    ∀ (n : ℕ) (s : ℝ),
      0 ≤ s ∧
        (∃ x y a b : Fin n → ℝ,
          (∀ i, a i ^ 2 + b i ^ 2 = 1 ∧ |a i| + |b i| ≤ 2 * x i ∧
              |a i| + |b i| ≤ 2 * (s - x i) ∧ |a i| + |b i| ≤ 2 * y i ∧
              |a i| + |b i| ≤ 2 * (s - y i)) ∧
          (∀ i j, i ≠ j → ∀ X Y : ℝ,
            (|a i * (X - x i) + b i * (Y - y i)| < 1 / 2 ∧
                |(-b i) * (X - x i) + a i * (Y - y i)| < 1 / 2) →
              ¬(|a j * (X - x j) + b j * (Y - y j)| < 1 / 2 ∧
                |(-b j) * (X - x j) + a j * (Y - y j)| < 1 / 2))) →
      (n : ℝ) ≤ s ^ 2 := by
  intro n s hfits
  obtain ⟨hs0, x, y, a, b, hbox, hdisj⟩ := hfits
  have hvol : ∀ i, volume (sqSet (x i) (y i) (a i) (b i)) = 1 :=
    fun i => volume_sqSet (x i) (y i) (a i) (b i) (hbox i).1
  have hpd :
      (((Finset.univ : Finset (Fin n)) : Set (Fin n))).PairwiseDisjoint
        (fun i => sqSet (x i) (y i) (a i) (b i)) := by
    intro i _ j _ hij
    show Disjoint (sqSet (x i) (y i) (a i) (b i)) (sqSet (x j) (y j) (a j) (b j))
    rw [Set.disjoint_left]
    intro p hpi hpj
    rw [mem_sqSet] at hpi hpj
    exact hdisj i j hij p.1 p.2 hpi hpj
  have hmeas : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      MeasurableSet (sqSet (x i) (y i) (a i) (b i)) :=
    fun i _ => sqSet_measurable (x i) (y i) (a i) (b i)
  have hunion :
      volume (⋃ i ∈ (Finset.univ : Finset (Fin n)), sqSet (x i) (y i) (a i) (b i)) =
        ∑ i ∈ (Finset.univ : Finset (Fin n)), volume (sqSet (x i) (y i) (a i) (b i)) :=
    measure_biUnion_finset hpd hmeas
  have hsum :
      (∑ i ∈ (Finset.univ : Finset (Fin n)), volume (sqSet (x i) (y i) (a i) (b i))) =
        (n : ℝ≥0∞) := by
    simp [hvol]
  have hsub :
      (⋃ i ∈ (Finset.univ : Finset (Fin n)), sqSet (x i) (y i) (a i) (b i)) ⊆
        Set.Ioo (0 : ℝ) s ×ˢ Set.Ioo (0 : ℝ) s := by
    intro p hp
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left] at hp
    obtain ⟨i, hpi⟩ := hp
    exact sqSet_subset (x i) (y i) (a i) (b i) s (hbox i).1 (hbox i).2.1
      (hbox i).2.2.1 (hbox i).2.2.2.1 (hbox i).2.2.2.2 hpi
  have hvolC :
      volume (Set.Ioo (0 : ℝ) s ×ˢ Set.Ioo (0 : ℝ) s) = ENNReal.ofReal (s ^ 2) := by
    rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioo]
    rw [← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ s - 0)]
    congr 1
    ring
  have hle : (n : ℝ≥0∞) ≤ ENNReal.ofReal (s ^ 2) := by
    rw [← hsum, ← hunion]
    calc
      volume (⋃ i ∈ (Finset.univ : Finset (Fin n)), sqSet (x i) (y i) (a i) (b i))
          ≤ volume (Set.Ioo (0 : ℝ) s ×ˢ Set.Ioo (0 : ℝ) s) := measure_mono hsub
      _ = ENNReal.ofReal (s ^ 2) := hvolC
  have hfin : ENNReal.ofReal (s ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_natCast, ENNReal.toReal_ofReal (sq_nonneg s)] at hreal
  exact hreal

theorem PEqualNP.Outside.L_square_packing_area_from_packing :
    let inside := fun (x y a b X Y : ℝ) => |a*(X-x)+b*(Y-y)| < 1/2 ∧ |(-b)*(X-x)+a*(Y-y)| < 1/2; let fits := fun (n : ℕ) (s : ℝ) => 0 ≤ s ∧ ∃ x y a b : Fin n → ℝ, (∀ i, a i ^ 2 + b i ^ 2 = 1 ∧ |a i| + |b i| ≤ 2*x i ∧ |a i| + |b i| ≤ 2*(s-x i) ∧ |a i| + |b i| ≤ 2*y i ∧ |a i| + |b i| ≤ 2*(s-y i)) ∧ (∀ i j, i ≠ j → ∀ X Y : ℝ, inside (x i) (y i) (a i) (b i) X Y → ¬ inside (x j) (y j) (a j) (b j) X Y); ∀ (n : ℕ) (s : ℝ), fits n s → (n : ℝ) ≤ s^2 := by
  exact area_aux
