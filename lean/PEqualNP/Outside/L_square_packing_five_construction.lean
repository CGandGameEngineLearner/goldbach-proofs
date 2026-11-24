import Mathlib

private abbrev ins (x y a b X Y : ℝ) : Prop :=
  |a * (X - x) + b * (Y - y)| < 1 / 2 ∧ |(-b) * (X - x) + a * (Y - y)| < 1 / 2

noncomputable def px : Fin 5 → ℝ :=
  ![1 / 2, 3 / 2 + Real.sqrt 2 / 2, 1 / 2, 3 / 2 + Real.sqrt 2 / 2,
    1 + Real.sqrt 2 / 4]

noncomputable def py : Fin 5 → ℝ :=
  ![1 / 2, 1 / 2, 3 / 2 + Real.sqrt 2 / 2, 3 / 2 + Real.sqrt 2 / 2,
    1 + Real.sqrt 2 / 4]

noncomputable def pa : Fin 5 → ℝ := ![1, 1, 1, 1, Real.sqrt 2 / 2]

noncomputable def pb : Fin 5 → ℝ := ![0, 0, 0, 0, Real.sqrt 2 / 2]

private lemma hr0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2

private lemma hr2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)

private lemma hr_le : Real.sqrt 2 ≤ 2 := by
  nlinarith [hr0, hr2]

private lemma center_sq : (Real.sqrt 2 / 2) ^ 2 + (Real.sqrt 2 / 2) ^ 2 = 1 := by
  nlinarith [hr2]

private lemma center_ab : |Real.sqrt 2 / 2| + |Real.sqrt 2 / 2| = Real.sqrt 2 := by
  have h : (0 : ℝ) ≤ Real.sqrt 2 / 2 := by linarith [hr0]
  rw [abs_of_nonneg h]
  ring

private lemma sep_01 (X Y : ℝ) :
    ins (px 0) (py 0) (pa 0) (pb 0) X Y →
      ins (px 1) (py 1) (pa 1) (pb 1) X Y → False := by
  intro hX hY
  obtain ⟨hX1, hX2⟩ := hX
  obtain ⟨hY1, hY2⟩ := hY
  simp [px, py, pa, pb] at hX1 hX2 hY1 hY2
  obtain ⟨a1, a2⟩ := abs_lt.mp hX1
  obtain ⟨a3, a4⟩ := abs_lt.mp hX2
  obtain ⟨b1, b2⟩ := abs_lt.mp hY1
  obtain ⟨b3, b4⟩ := abs_lt.mp hY2
  nlinarith [hr0, hr2, a1, a2, a3, a4, b1, b2, b3, b4]

private lemma sep_02 (X Y : ℝ) :
    ins (px 0) (py 0) (pa 0) (pb 0) X Y →
      ins (px 2) (py 2) (pa 2) (pb 2) X Y → False := by
  intro hX hY
  obtain ⟨hX1, hX2⟩ := hX
  obtain ⟨hY1, hY2⟩ := hY
  simp [px, py, pa, pb] at hX1 hX2 hY1 hY2
  obtain ⟨a1, a2⟩ := abs_lt.mp hX1
  obtain ⟨a3, a4⟩ := abs_lt.mp hX2
  obtain ⟨b1, b2⟩ := abs_lt.mp hY1
  obtain ⟨b3, b4⟩ := abs_lt.mp hY2
  nlinarith [hr0, hr2, a1, a2, a3, a4, b1, b2, b3, b4]

private lemma sep_03 (X Y : ℝ) :
    ins (px 0) (py 0) (pa 0) (pb 0) X Y →
      ins (px 3) (py 3) (pa 3) (pb 3) X Y → False := by
  intro hX hY
  obtain ⟨hX1, hX2⟩ := hX
  obtain ⟨hY1, hY2⟩ := hY
  simp [px, py, pa, pb] at hX1 hX2 hY1 hY2
  obtain ⟨a1, a2⟩ := abs_lt.mp hX1
  obtain ⟨a3, a4⟩ := abs_lt.mp hX2
  obtain ⟨b1, b2⟩ := abs_lt.mp hY1
  obtain ⟨b3, b4⟩ := abs_lt.mp hY2
  nlinarith [hr0, hr2, a1, a2, a3, a4, b1, b2, b3, b4]

private lemma sep_04 (X Y : ℝ) :
    ins (px 0) (py 0) (pa 0) (pb 0) X Y →
      ins (px 4) (py 4) (pa 4) (pb 4) X Y → False := by
  intro hX hY
  obtain ⟨hX1, hX2⟩ := hX
  obtain ⟨hY1, hY2⟩ := hY
  simp [px, py, pa, pb] at hX1 hX2 hY1 hY2
  obtain ⟨a1, a2⟩ := abs_lt.mp hX1
  obtain ⟨a3, a4⟩ := abs_lt.mp hX2
  obtain ⟨b1, b2⟩ := abs_lt.mp hY1
  obtain ⟨b3, b4⟩ := abs_lt.mp hY2
  nlinarith [hr0, hr2, a1, a2, a3, a4, b1, b2, b3, b4]

private lemma sep_12 (X Y : ℝ) :
    ins (px 1) (py 1) (pa 1) (pb 1) X Y →
      ins (px 2) (py 2) (pa 2) (pb 2) X Y → False := by
  intro hX hY
  obtain ⟨hX1, hX2⟩ := hX
  obtain ⟨hY1, hY2⟩ := hY
  simp [px, py, pa, pb] at hX1 hX2 hY1 hY2
  obtain ⟨a1, a2⟩ := abs_lt.mp hX1
  obtain ⟨a3, a4⟩ := abs_lt.mp hX2
  obtain ⟨b1, b2⟩ := abs_lt.mp hY1
  obtain ⟨b3, b4⟩ := abs_lt.mp hY2
  nlinarith [hr0, hr2, a1, a2, a3, a4, b1, b2, b3, b4]

private lemma sep_13 (X Y : ℝ) :
    ins (px 1) (py 1) (pa 1) (pb 1) X Y →
      ins (px 3) (py 3) (pa 3) (pb 3) X Y → False := by
  intro hX hY
  obtain ⟨hX1, hX2⟩ := hX
  obtain ⟨hY1, hY2⟩ := hY
  simp [px, py, pa, pb] at hX1 hX2 hY1 hY2
  obtain ⟨a1, a2⟩ := abs_lt.mp hX1
  obtain ⟨a3, a4⟩ := abs_lt.mp hX2
  obtain ⟨b1, b2⟩ := abs_lt.mp hY1
  obtain ⟨b3, b4⟩ := abs_lt.mp hY2
  nlinarith [hr0, hr2, a1, a2, a3, a4, b1, b2, b3, b4]

private lemma sep_14 (X Y : ℝ) :
    ins (px 1) (py 1) (pa 1) (pb 1) X Y →
      ins (px 4) (py 4) (pa 4) (pb 4) X Y → False := by
  intro hX hY
  obtain ⟨hX1, hX2⟩ := hX
  obtain ⟨hY1, hY2⟩ := hY
  simp [px, py, pa, pb] at hX1 hX2 hY1 hY2
  obtain ⟨a1, a2⟩ := abs_lt.mp hX1
  obtain ⟨a3, a4⟩ := abs_lt.mp hX2
  obtain ⟨b1, b2⟩ := abs_lt.mp hY1
  obtain ⟨b3, b4⟩ := abs_lt.mp hY2
  nlinarith [hr0, hr2, a1, a2, a3, a4, b1, b2, b3, b4]

private lemma sep_23 (X Y : ℝ) :
    ins (px 2) (py 2) (pa 2) (pb 2) X Y →
      ins (px 3) (py 3) (pa 3) (pb 3) X Y → False := by
  intro hX hY
  obtain ⟨hX1, hX2⟩ := hX
  obtain ⟨hY1, hY2⟩ := hY
  simp [px, py, pa, pb] at hX1 hX2 hY1 hY2
  obtain ⟨a1, a2⟩ := abs_lt.mp hX1
  obtain ⟨a3, a4⟩ := abs_lt.mp hX2
  obtain ⟨b1, b2⟩ := abs_lt.mp hY1
  obtain ⟨b3, b4⟩ := abs_lt.mp hY2
  nlinarith [hr0, hr2, a1, a2, a3, a4, b1, b2, b3, b4]

private lemma sep_24 (X Y : ℝ) :
    ins (px 2) (py 2) (pa 2) (pb 2) X Y →
      ins (px 4) (py 4) (pa 4) (pb 4) X Y → False := by
  intro hX hY
  obtain ⟨hX1, hX2⟩ := hX
  obtain ⟨hY1, hY2⟩ := hY
  simp [px, py, pa, pb] at hX1 hX2 hY1 hY2
  obtain ⟨a1, a2⟩ := abs_lt.mp hX1
  obtain ⟨a3, a4⟩ := abs_lt.mp hX2
  obtain ⟨b1, b2⟩ := abs_lt.mp hY1
  obtain ⟨b3, b4⟩ := abs_lt.mp hY2
  nlinarith [hr0, hr2, a1, a2, a3, a4, b1, b2, b3, b4]

private lemma sep_34 (X Y : ℝ) :
    ins (px 3) (py 3) (pa 3) (pb 3) X Y →
      ins (px 4) (py 4) (pa 4) (pb 4) X Y → False := by
  intro hX hY
  obtain ⟨hX1, hX2⟩ := hX
  obtain ⟨hY1, hY2⟩ := hY
  simp [px, py, pa, pb] at hX1 hX2 hY1 hY2
  obtain ⟨a1, a2⟩ := abs_lt.mp hX1
  obtain ⟨a3, a4⟩ := abs_lt.mp hX2
  obtain ⟨b1, b2⟩ := abs_lt.mp hY1
  obtain ⟨b3, b4⟩ := abs_lt.mp hY2
  nlinarith [hr0, hr2, a1, a2, a3, a4, b1, b2, b3, b4]

theorem PEqualNP.Outside.L_square_packing_five_construction :
    let inside := fun (x y a b X Y : ℝ) => |a*(X-x)+b*(Y-y)| < 1/2 ∧ |(-b)*(X-x)+a*(Y-y)| < 1/2; let fits := fun (n : ℕ) (s : ℝ) => 0 ≤ s ∧ ∃ x y a b : Fin n → ℝ, (∀ i, a i ^ 2 + b i ^ 2 = 1 ∧ |a i| + |b i| ≤ 2*x i ∧ |a i| + |b i| ≤ 2*(s-x i) ∧ |a i| + |b i| ≤ 2*y i ∧ |a i| + |b i| ≤ 2*(s-y i)) ∧ (∀ i j, i ≠ j → ∀ X Y : ℝ, inside (x i) (y i) (a i) (b i) X Y → ¬ inside (x j) (y j) (a j) (b j) X Y); fits 5 (2 + Real.sqrt 2 / 2) := by
  dsimp only
  constructor
  · linarith [hr0]
  · refine ⟨px, py, pa, pb, ?_, ?_⟩
    · intro i
      fin_cases i <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [px, py, pa, pb, center_sq, center_ab] <;>
        linarith [hr0, hr_le]
    · intro i j hij X Y hX hY
      fin_cases i <;> fin_cases j
      all_goals
        first
          | exact absurd rfl hij
          | exact sep_01 X Y hX hY
          | exact sep_01 X Y hY hX
          | exact sep_02 X Y hX hY
          | exact sep_02 X Y hY hX
          | exact sep_03 X Y hX hY
          | exact sep_03 X Y hY hX
          | exact sep_04 X Y hX hY
          | exact sep_04 X Y hY hX
          | exact sep_12 X Y hX hY
          | exact sep_12 X Y hY hX
          | exact sep_13 X Y hX hY
          | exact sep_13 X Y hY hX
          | exact sep_14 X Y hX hY
          | exact sep_14 X Y hY hX
          | exact sep_23 X Y hX hY
          | exact sep_23 X Y hY hX
          | exact sep_24 X Y hX hY
          | exact sep_24 X Y hY hX
          | exact sep_34 X Y hX hY
          | exact sep_34 X Y hY hX
