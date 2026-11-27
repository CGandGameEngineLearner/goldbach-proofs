import Mathlib

open Finset

namespace GoldbachNormalized

private noncomputable def profile (c : ℕ → ℝ) (m t : ℝ) (i : ℕ) : ℝ :=
  max (1 - t * (c i - m)) 0

private noncomputable def total (I : Finset ℕ) (c : ℕ → ℝ) (m t : ℝ) : ℝ :=
  ∑ i ∈ I, profile c m t i

private noncomputable def weight (I : Finset ℕ) (c : ℕ → ℝ) (m t : ℝ) (i : ℕ) : ℝ :=
  profile c m t i / total I c m t

private noncomputable def energy (I : Finset ℕ) (u : ℕ → ℝ) : ℝ :=
  ∑ i ∈ I, (u i)^2

private theorem total_pos {I : Finset ℕ} {c : ℕ → ℝ} {m : ℝ}
    (hm : ∃ i ∈ I, c i = m) (t : ℝ) : 0 < total I c m t := by
  obtain ⟨j,hj,he⟩ := hm
  apply sum_pos' (fun i _ => le_max_right _ _) ⟨j, hj, ?_⟩
  simp [he]

private theorem weight_mass {I : Finset ℕ} {c : ℕ → ℝ} {m : ℝ}
    (hm : ∃ i ∈ I, c i = m) (t : ℝ) : ∑ i ∈ I, weight I c m t i = 1 := by
  simp only [weight, ← sum_div]
  exact div_self (total_pos hm t).ne'

private theorem energy_continuous {I : Finset ℕ} {c : ℕ → ℝ} {m : ℝ}
    (hm : ∃ i ∈ I, c i = m) : Continuous (fun t => energy I (weight I c m t)) := by
  have hp (i : ℕ) : Continuous (fun t => profile c m t i) := by unfold profile; fun_prop
  have hs : Continuous (total I c m) := continuous_finsetSum _ (fun i _ => hp i)
  exact continuous_finsetSum _ (fun i _ => ((hp i).div hs (fun t => (total_pos hm t).ne')).pow 2)

private theorem affine_sum {I : Finset ℕ} {u : ℕ → ℝ} (hu : ∑ i ∈ I, u i = 1)
    (c : ℕ → ℝ) (m t : ℝ) :
    (∑ i ∈ I, u i * (1 - t*(c i-m))) = 1 - t*((∑ i ∈ I, u i*c i)-m) := by
  calc
    _ = ∑ i ∈ I, (u i - t*(u i*c i) + (t*m)*u i) := by
      refine sum_congr rfl fun i _ => ?_
      ring
    _ = _ := by rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, hu]; ring

private theorem dot_le_energy {I : Finset ℕ} {u v : ℕ → ℝ} (h : energy I u ≤ energy I v) :
    (∑ i ∈ I, u i*v i) ≤ energy I v := by
  have hb : (∑ i ∈ I, 2*(u i*v i)) ≤ ∑ i ∈ I, ((u i)^2+(v i)^2) :=
    sum_le_sum fun i _ => by nlinarith only [sq_nonneg (u i-v i)]
  rw [← mul_sum, sum_add_distrib] at hb
  unfold energy at *
  linarith

/-- At a positive clipping parameter an equal-energy profile minimizes the linear cost. -/
private theorem clipped_min {I : Finset ℕ} {c u : ℕ → ℝ} {m t : ℝ}
    (hm : ∃ i ∈ I, c i = m) (ht : 0 < t) (hu : ∀ i ∈ I, 0 ≤ u i)
    (hs : ∑ i ∈ I, u i = 1) (he : energy I u ≤ energy I (weight I c m t)) :
    (∑ i ∈ I, weight I c m t i*c i) ≤ ∑ i ∈ I, u i*c i := by
  let v := weight I c m t
  let A := total I c m t
  have ha : 0 < A := total_pos hm t
  have hv (i : ℕ) : profile c m t i = A * v i := by
    dsimp [A, v, weight]
    field_simp [(total_pos hm t).ne']
  have active (i : ℕ) : v i * profile c m t i = v i * (1-t*(c i-m)) := by
    by_cases h : 0 ≤ 1-t*(c i-m)
    · rw [profile, max_eq_left h]
    · simp [v, weight, profile, max_eq_right (le_of_not_ge h)]
  have hdot := dot_le_energy he
  have hcost : (∑ i ∈ I, u i * (1-t*(c i-m))) ≤ ∑ i ∈ I, v i * (1-t*(c i-m)) := by
    calc
      _ ≤ ∑ i ∈ I, u i * profile c m t i :=
        sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (le_max_left ..) (hu i hi)
      _ = A * ∑ i ∈ I, u i*v i := by rw [mul_sum]; exact sum_congr rfl fun i _ => by rw [hv]; ring
      _ ≤ A * energy I v := mul_le_mul_of_nonneg_left hdot ha.le
      _ = ∑ i ∈ I, v i * (1-t*(c i-m)) := by
        rw [energy, mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [← active, hv]
        ring
  rw [affine_sum hs, affine_sum (weight_mass hm t)] at hcost
  by_contra! h
  have hd := mul_pos ht (sub_pos.mpr h)
  nlinarith only [hcost, hd]


private theorem zero_weight (I : Finset ℕ) (c : ℕ → ℝ) (m : ℝ) (i : ℕ) :
    weight I c m 0 i = 1 / (I.card:ℝ) := by simp [weight, profile, total]

private theorem zero_energy {I : Finset ℕ} (hn : 0 < (I.card:ℝ)) (c : ℕ → ℝ) (m : ℝ) :
    energy I (weight I c m 0) = 1 / (I.card:ℝ) := by
  simp only [energy, zero_weight, sum_const, nsmul_eq_mul]
  field_simp [hn.ne']

private theorem uniform_only {I : Finset ℕ} {u : ℕ → ℝ} (hn : 0 < (I.card:ℝ))
    (hs : ∑ i ∈ I, u i = 1) (he : energy I u ≤ 1/(I.card:ℝ)) :
    ∀ i ∈ I, u i = 1/(I.card:ℝ) := by
  let a := 1 / (I.card:ℝ)
  have ha : (I.card:ℝ) * a = 1 := by dsimp [a]; field_simp [hn.ne']
  have hv : (∑ i ∈ I, (u i-a)^2) = energy I u - a := by
    calc
      _ = ∑ i ∈ I, ((u i)^2 - (2*a)*u i + a^2) := sum_congr rfl fun i _ => by ring
      _ = _ := by
        rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, hs, sum_const, nsmul_eq_mul]
        change energy I u - (2*a)*1 + (I.card:ℝ)*a^2 = _
        nlinarith only [congrArg (fun x : ℝ => x*a) ha]
  have hz : ∑ i ∈ I, (u i-a)^2 = 0 :=
    le_antisymm (hv.trans_le (sub_nonpos.mpr he)) (sum_nonneg fun _ _ => sq_nonneg _)
  intro i hi
  have hi := (sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (u j-a)).mp hz i hi
  nlinarith only [hi, sq_nonneg (u i-a)]

private theorem support_min {I : Finset ℕ} {c v u : ℕ → ℝ} {m : ℝ}
    (hc : ∀ i ∈ I, m ≤ c i) (hs : ∀ i ∈ I, c i ≠ m → v i = 0)
    (hv : ∑ i ∈ I, v i = 1) (hu : ∀ i ∈ I, 0 ≤ u i) (hn : ∑ i ∈ I, u i = 1) :
    (∑ i ∈ I, v i*c i) ≤ ∑ i ∈ I, u i*c i := by
  calc
    _ = ∑ i ∈ I, v i*m := sum_congr rfl fun i hi => by
      by_cases h : c i = m
      · rw [h]
      · rw [hs i hi h, zero_mul, zero_mul]
    _ = ∑ i ∈ I, u i*m := by rw [← sum_mul, ← sum_mul, hv, hn]
    _ ≤ _ := sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hc i hi) (hu i hi)

/-- The minimum over normalized nonnegative windows with a prescribed upper bound on
squared mass. The family includes the uniform window and all tied minimum-cost shifts. -/
private theorem exists_clipped :
    ∀ (I : Finset ℕ) (c : ℕ → ℝ) (m B : ℝ),
      (∃ j ∈ I, c j = m) → (∀ j ∈ I, m ≤ c j) → 1 ≤ B * (I.card:ℝ) →
      let v := fun (t : ℝ) (j : ℕ) => max (1 - t*(c j-m)) 0
      let w := fun (t : ℝ) (j : ℕ) => v t j / (∑ k ∈ I, v t k)
      ∃ t : ℝ, 0 ≤ t ∧ (∀ j ∈ I, 0 ≤ w t j) ∧ (∑ j ∈ I, w t j) = 1 ∧
        (∑ j ∈ I, (w t j)^2) ≤ B ∧
        ((∑ j ∈ I, (w t j)^2) = B ∨ ∀ j ∈ I, c j ≠ m → w t j = 0) ∧
        ∀ u : ℕ → ℝ, (∀ j ∈ I, 0 ≤ u j) → (∑ j ∈ I, u j) = 1 →
          (∑ j ∈ I, (u j)^2) ≤ B → (∑ j ∈ I, w t j * c j) ≤ ∑ j ∈ I, u j * c j := by
  intro I c m B hm hc hB v w
  have hn : 0 < (I.card:ℝ) := by
    obtain ⟨j,hj,_⟩ := hm
    exact_mod_cast card_pos.mpr ⟨j,hj⟩
  let e := fun t => energy I (weight I c m t)
  have hzero : e 0 = 1/(I.card:ℝ) := zero_energy hn c m
  have feasible : e 0 ≤ B := hzero.trans_le ((div_le_iff₀ hn).mpr hB)
  have nonneg (t : ℝ) (i : ℕ) : 0 ≤ w t i := div_nonneg (le_max_right ..) (total_pos hm t).le
  by_cases uniform : e 0 = B
  · refine ⟨0, le_rfl, fun i _ => nonneg 0 i, weight_mass hm 0, uniform.le, Or.inl uniform, ?_⟩
    intro u _ hs he
    have hu := uniform_only hn hs (he.trans_eq (uniform.symm.trans hzero))
    apply le_of_eq
    exact sum_congr rfl fun i hi => by rw [hu i hi]; exact congrArg (· * c i) (zero_weight I c m i)
  let T := ∑ i ∈ I, (c i-m)⁻¹
  have ht : 0 ≤ T := sum_nonneg fun i hi => inv_nonneg.mpr (sub_nonneg.mpr (hc i hi))
  have terminal (i : ℕ) (hi : i ∈ I) (hne : c i ≠ m) : w T i = 0 := by
    have hd : 0 < c i-m := sub_pos.mpr (lt_of_le_of_ne (hc i hi) (Ne.symm hne))
    have hb : (c i-m)⁻¹ ≤ T := single_le_sum (fun k hk => inv_nonneg.mpr (sub_nonneg.mpr (hc k hk))) hi
    have h1 : 1 ≤ T*(c i-m) := by
      simpa only [inv_mul_cancel₀ hd.ne'] using mul_le_mul_of_nonneg_right hb hd.le
    change max (1-T*(c i-m)) 0 / _ = 0
    rw [max_eq_right (by linarith), zero_div]
  by_cases saturated : e T ≤ B
  · refine ⟨T, ht, fun i _ => nonneg T i, weight_mass hm T, saturated, Or.inr terminal, ?_⟩
    intro u hu hs _
    exact support_min hc terminal (weight_mass hm T) hu hs
  · have hb : B ∈ Set.Icc (e 0) (e T) := ⟨feasible, le_of_not_ge saturated⟩
    obtain ⟨t, hmem, he⟩ := intermediate_value_Icc ht (energy_continuous hm).continuousOn hb
    have hpos : 0 < t := lt_of_le_of_ne hmem.1 (fun ht => uniform (ht ▸ he))
    refine ⟨t, hpos.le, fun i _ => nonneg t i, weight_mass hm t, he.le, Or.inl he, ?_⟩
    intro u hu hs hbudget
    exact clipped_min hm hpos hu hs (hbudget.trans_eq he.symm)

/-- On one active face, the affine weights give the cost and squared mass from
the same centered second moment. -/
private theorem face_moments {P : Finset ℕ} (hn : P.Nonempty) (c u : ℕ → ℝ) (d α : ℝ)
    (hmass : ∑ i ∈ P, u i = 1) (hu : ∀ i ∈ P, u i = d - α*c i) :
    let μ := (∑ i ∈ P, c i)/(P.card:ℝ)
    let V := ∑ i ∈ P, (c i-μ)^2
    (∑ i ∈ P, u i*c i) = μ - α*V ∧
      (∑ i ∈ P, (u i)^2) = 1/(P.card:ℝ) + α^2*V := by
  intro μ V
  let K := (P.card:ℝ)
  have hK : 0 < K := by dsimp [K]; exact_mod_cast card_pos.mpr hn
  have hμ : (∑ i ∈ P, c i) = K*μ := by dsimp [K, μ]; field_simp [hK.ne']
  let x := fun i => c i-μ
  have hx : ∑ i ∈ P, x i = 0 := by
    simp only [x, sum_sub_distrib, sum_const, nsmul_eq_mul]
    exact sub_eq_zero.mpr hμ
  have haff : (∑ i ∈ P, u i) = K * (d - α*μ) := by
    calc
      _ = ∑ i ∈ P, (d-α*c i) := sum_congr rfl hu
      _ = _ := by rw [sum_sub_distrib, sum_const, nsmul_eq_mul, ← mul_sum, hμ]; dsimp [K]; ring
  have hc : d-α*μ = 1/K := (eq_div_iff hK.ne').mpr (by rw [mul_comm, ← haff, hmass])
  have hcenter (i : ℕ) (hi : i ∈ P) : u i = 1/K - α*x i := by
    rw [hu i hi, ← hc]
    dsimp [x]
    ring
  constructor
  · calc
      _ = ∑ i ∈ P, (μ * u i + (1/K)*x i - α*(x i)^2) := by
        refine sum_congr rfl fun i hi => ?_
        rw [hcenter i hi]
        dsimp [x]
        ring
      _ = _ := by rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum, hx, hmass]; ring
  · calc
      _ = ∑ i ∈ P, ((1/K)^2 - (2*α/K)*x i + α^2*(x i)^2) := by
        exact sum_congr rfl fun i hi => by rw [hcenter i hi]; ring
      _ = _ := by
        rw [sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, ← mul_sum, ← mul_sum, hx]
        change K*(1/K)^2 - (2*α/K)*0 + α^2*V = 1/K + α^2*V
        field_simp [hK.ne']
        ring

/-- The positive support is an initial segment in increasing cost. On this finite
set the optimum has an explicit value, including when the energy constraint is slack. -/
private theorem face_value {I : Finset ℕ} {c : ℕ → ℝ} {m t B : ℝ}
    (hm : ∃ i ∈ I, c i = m) (ht : 0 ≤ t)
    (sat : energy I (weight I c m t) = B ∨ ∀ i ∈ I, c i ≠ m → weight I c m t i = 0) :
    let u := weight I c m t
    let P := I.filter (fun i => 0 < u i)
    let μ := (∑ i ∈ P, c i)/(P.card:ℝ)
    P.Nonempty ∧ (∀ i ∈ P, ∀ j ∈ I, c j ≤ c i → j ∈ P) ∧
      (∑ i ∈ I, u i*c i) = μ - Real.sqrt ((B - 1/(P.card:ℝ))*(∑ i ∈ P, (c i-μ)^2)) := by
  intro u P μ
  let A := total I c m t
  have hA : 0 < A := total_pos hm t
  have hP : P.Nonempty := by
    obtain ⟨j,hj,hjmin⟩ := hm
    refine ⟨j,mem_filter.mpr ⟨hj, div_pos ?_ hA⟩⟩
    simp [profile,hjmin]
  refine ⟨hP, ?_, ?_⟩
  · intro i hi j hj hji
    refine mem_filter.mpr ⟨hj, (mem_filter.mp hi).2.trans_le ?_⟩
    apply div_le_div_of_nonneg_right _ hA.le
    apply max_le_max_right
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left (sub_le_sub_right hji m) ht) 1
  have off (i : ℕ) (hi : i ∈ I) (hn : i ∉ P) : u i = 0 := by
    exact le_antisymm (le_of_not_gt (fun h => hn (mem_filter.mpr ⟨hi,h⟩)))
      (div_nonneg (le_max_right ..) hA.le)
  have restrictSum (f : ℕ → ℝ) (hf : ∀ i ∈ I, i ∉ P → f i = 0) :
      ∑ i ∈ I, f i = ∑ i ∈ P, f i := (sum_subset (filter_subset ..) hf).symm
  have hPM : ∑ i ∈ P, u i = 1 := (restrictSum u off).symm.trans (weight_mass hm t)
  have cost := restrictSum (fun i => u i*c i) (fun i hi hn => by rw [off i hi hn, zero_mul])
  rw [cost]
  let V := ∑ i ∈ P, (c i-μ)^2
  have hV : 0 ≤ V := sum_nonneg fun i _ => sq_nonneg _
  have hK : 0 < (P.card:ℝ) := by exact_mod_cast card_pos.mpr hP
  have haff (i : ℕ) (hi : i ∈ P) : u i = (1+t*m)/A - (t/A)*c i := by
    have hp : 0 < profile c m t i := (div_pos_iff_of_pos_right hA).mp (mem_filter.mp hi).2
    have hraw : 0 < 1-t*(c i-m) := (lt_max_iff.mp hp).resolve_right (lt_irrefl _)
    change max (1-t*(c i-m)) 0 / A = _
    rw [max_eq_left hraw.le]
    ring
  obtain ⟨hcost,henergy⟩ := face_moments hP c u ((1+t*m)/A) (t/A) hPM haff
  change (∑ i ∈ P, u i*c i) = μ - (t/A)*V at hcost
  change (∑ i ∈ P, (u i)^2) = 1/(P.card:ℝ) + (t/A)^2*V at henergy
  rw [hcost]
  rcases sat with he | hmin
  · have hb : B = 1/(P.card:ℝ) + (t/A)^2*V :=
      he.symm.trans ((restrictSum (fun i => (u i)^2) (fun i hi hn => by simp [off i hi hn])).trans henergy)
    rw [hb]
    change _ = μ - Real.sqrt ((1/(P.card:ℝ)+(t/A)^2*V-1/(P.card:ℝ))*V)
    rw [show (1/(P.card:ℝ)+(t/A)^2*V-1/(P.card:ℝ))*V = ((t/A)*V)^2 by ring,
      Real.sqrt_sq (mul_nonneg (div_nonneg ht hA.le) hV)]
  · have hcm (i : ℕ) (hi : i ∈ P) : c i = m := by
      by_contra h
      exact (mem_filter.mp hi).2.ne' (hmin i (mem_filter.mp hi).1 h)
    have hmean : μ = m := by
      dsimp [μ]
      rw [sum_congr rfl hcm, sum_const, nsmul_eq_mul]
      field_simp [hK.ne']
    have hv : V = 0 := sum_eq_zero fun i hi => by simp [hcm i hi,hmean]
    change μ - (t/A)*V = μ - Real.sqrt ((B-1/(P.card:ℝ))*V)
    simp [hv]

end GoldbachNormalized

open GoldbachNormalized

/-- Exact minimum of the weighted average on a finite shift window with mass one
and an upper bound on squared mass. The formula uses only the mean and centered
second moment on an initial segment of the shifts ordered by coefficient. -/
theorem Conjectures.Goldbach.NormalizedShiftOptimalWindow :
    ∀ (I : Finset ℕ) (c : ℕ → ℝ) (m B : ℝ),
      (∃ j ∈ I, c j = m) → (∀ j ∈ I, m ≤ c j) → 1 ≤ B * (I.card:ℝ) →
      let v := fun (t : ℝ) (j : ℕ) => max (1 - t*(c j-m)) 0
      let w := fun (t : ℝ) (j : ℕ) => v t j / (∑ k ∈ I, v t k)
      ∃ t : ℝ, 0 ≤ t ∧ (∀ j ∈ I, 0 ≤ w t j) ∧ (∑ j ∈ I, w t j) = 1 ∧
        (∑ j ∈ I, (w t j)^2) ≤ B ∧
        ((∑ j ∈ I, (w t j)^2) = B ∨ ∀ j ∈ I, c j ≠ m → w t j = 0) ∧
        (let P := I.filter (fun j => 0 < w t j)
         let μ := (∑ j ∈ P, c j)/(P.card:ℝ)
         P.Nonempty ∧ (∀ i ∈ P, ∀ j ∈ I, c j ≤ c i → j ∈ P) ∧
           (∑ j ∈ I, w t j * c j) =
             μ - Real.sqrt ((B - 1/(P.card:ℝ)) * (∑ j ∈ P, (c j-μ)^2))) ∧
        ∀ u : ℕ → ℝ, (∀ j ∈ I, 0 ≤ u j) → (∑ j ∈ I, u j) = 1 →
          (∑ j ∈ I, (u j)^2) ≤ B → (∑ j ∈ I, w t j * c j) ≤ ∑ j ∈ I, u j * c j := by
  intro I c m B hm hc hB v w
  obtain ⟨t,ht,hpos,hmass,hbudget,hsat,hopt⟩ := exists_clipped I c m B hm hc hB
  exact ⟨t, ht, hpos, hmass, hbudget, hsat, face_value hm ht hsat, hopt⟩
