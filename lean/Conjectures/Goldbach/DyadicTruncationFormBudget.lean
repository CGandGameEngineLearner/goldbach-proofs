import Mathlib

private lemma complex_mul_star_self (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  have h := Complex.mul_conj z
  rw [Complex.normSq_eq_norm_sq] at h
  exact h

private lemma norm_sq_eq_re_mul_star (z : ℂ) : ‖z‖ ^ 2 = (z * star z).re := by
  rw [complex_mul_star_self, Complex.ofReal_re]

private lemma norm_unit_char_eq_one {m : ℕ} [NeZero m]
    (χ : DirichletCharacter ℂ m) (u : (ZMod m)ˣ) :
    ‖χ (u : ZMod m)‖ = 1 := by
  have hc : 0 < Fintype.card (ZMod m)ˣ := Fintype.card_pos
  have hupow : u ^ Fintype.card (ZMod m)ˣ = 1 := pow_card_eq_one
  have hcpow : χ (u : ZMod m) ^ Fintype.card (ZMod m)ˣ = 1 := by
    calc
      χ (u : ZMod m) ^ Fintype.card (ZMod m)ˣ
          = χ (((u ^ Fintype.card (ZMod m)ˣ : (ZMod m)ˣ) : ZMod m)) := by
            rw [Units.val_pow_eq_pow_val, map_pow]
      _ = χ ((1 : (ZMod m)ˣ) : ZMod m) := by rw [hupow]
      _ = 1 := by simp
  have hnpow : ‖χ (u : ZMod m)‖ ^ Fintype.card (ZMod m)ˣ = 1 := by
    rw [← norm_pow, hcpow, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hc.ne').mp hnpow

private lemma star_char_unit_eq_inv {m : ℕ} [NeZero m]
    (χ : DirichletCharacter ℂ m) (u : (ZMod m)ˣ) :
    star (χ (u : ZMod m)) = χ ((u⁻¹ : (ZMod m)ˣ) : ZMod m) := by
  have h1 : χ (u : ZMod m) * star (χ (u : ZMod m)) = 1 := by
    rw [complex_mul_star_self, norm_unit_char_eq_one χ u]
    norm_num
  have h2 : χ (u : ZMod m) * χ ((u⁻¹ : (ZMod m)ˣ) : ZMod m) = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hne : χ (u : ZMod m) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h1
    exact zero_ne_one h1
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

private lemma unit_sum_char_mul_star {m : ℕ} [NeZero m]
    (χ ψ : DirichletCharacter ℂ m) :
    (∑ x : (ZMod m)ˣ, χ (x : ZMod m) * star (ψ (x : ZMod m))) =
      if χ = ψ then (m.totient : ℂ) else 0 := by
  by_cases h : χ = ψ
  · subst h
    have ht : ∀ x : (ZMod m)ˣ, χ (x : ZMod m) * star (χ (x : ZMod m)) = 1 := by
      intro x
      rw [complex_mul_star_self, norm_unit_char_eq_one χ x]
      norm_num
    rw [if_pos rfl]
    calc
      (∑ x : (ZMod m)ˣ, χ (x : ZMod m) * star (χ (x : ZMod m)))
          = ∑ _x : (ZMod m)ˣ, (1 : ℂ) := Finset.sum_congr rfl (fun x _ => ht x)
      _ = (Fintype.card (ZMod m)ˣ : ℂ) := by simp
      _ = (m.totient : ℂ) := by rw [ZMod.card_units_eq_totient]
  · rw [if_neg h]
    have hex : ∃ u : (ZMod m)ˣ, χ (u : ZMod m) ≠ ψ (u : ZMod m) := by
      by_contra hcon
      push Not at hcon
      apply h
      exact MulChar.ext hcon
    obtain ⟨u, hu⟩ := hex
    let c : ℂ := χ (u : ZMod m) * star (ψ (u : ZMod m))
    have hc : c ≠ 1 := by
      intro hceq
      apply hu
      have hψ : ψ (u : ZMod m) * star (ψ (u : ZMod m)) = 1 := by
        rw [complex_mul_star_self, norm_unit_char_eq_one ψ u]
        norm_num
      have hne : star (ψ (u : ZMod m)) ≠ 0 := by
        intro hz
        rw [hz, mul_zero] at hψ
        exact zero_ne_one hψ
      exact mul_right_cancel₀ hne (hceq.trans hψ.symm)
    let S : ℂ := ∑ x : (ZMod m)ˣ, χ (x : ZMod m) * star (ψ (x : ZMod m))
    have hmul : c * S = S := by
      calc
        c * S = ∑ x : (ZMod m)ˣ, c * (χ (x : ZMod m) * star (ψ (x : ZMod m))) := by
              rw [Finset.mul_sum]
        _ = ∑ x : (ZMod m)ˣ, χ ((u * x : (ZMod m)ˣ) : ZMod m) *
              star (ψ ((u * x : (ZMod m)ˣ) : ZMod m)) := by
              apply Finset.sum_congr rfl
              intro x _
              simp only [c, Units.val_mul, map_mul, star_mul']
              ring
        _ = S := by
              exact Fintype.sum_bijective (u * ·) (Group.mulLeft_bijective u) _ _ (fun _ => rfl)
    exact eq_zero_of_mul_eq_self_left hc hmul

private lemma sum_units_char_sq {m : ℕ} [NeZero m]
    (s : Finset (DirichletCharacter ℂ m)) (a : DirichletCharacter ℂ m → ℂ) :
    (∑ x : (ZMod m)ˣ, ‖∑ χ ∈ s, a χ * χ (x : ZMod m)‖ ^ 2) =
      (m.totient : ℝ) * ∑ χ ∈ s, ‖a χ‖ ^ 2 := by
  have hC :
      (∑ x : (ZMod m)ˣ, (∑ χ ∈ s, a χ * χ (x : ZMod m)) * star (∑ ψ ∈ s, a ψ * ψ (x : ZMod m))) =
        (m.totient : ℂ) * ∑ χ ∈ s, a χ * star (a χ) := by
    calc
      _ = ∑ x : (ZMod m)ˣ, ∑ χ ∈ s, ∑ ψ ∈ s,
            (a χ * star (a ψ)) * (χ (x : ZMod m) * star (ψ (x : ZMod m))) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [star_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro χ _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ψ _
            rw [star_mul']
            ring
      _ = ∑ χ ∈ s, ∑ ψ ∈ s, (a χ * star (a ψ)) *
            ∑ x : (ZMod m)ˣ, χ (x : ZMod m) * star (ψ (x : ZMod m)) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro χ _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro ψ _
            rw [← Finset.mul_sum]
      _ = ∑ χ ∈ s, ∑ ψ ∈ s,
            if χ = ψ then (m.totient : ℂ) * (a χ * star (a χ)) else 0 := by
            apply Finset.sum_congr rfl
            intro χ _
            apply Finset.sum_congr rfl
            intro ψ _
            rw [unit_sum_char_mul_star χ ψ]
            split_ifs with h
            · subst h; ring
            · simp
      _ = (m.totient : ℂ) * ∑ χ ∈ s, a χ * star (a χ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro χ hχ
            simp [hχ]
  have hR := congrArg Complex.re hC
  simp only [Complex.re_sum] at hR
  have hLHS :
      (∑ x : (ZMod m)ˣ, ‖∑ χ ∈ s, a χ * χ (x : ZMod m)‖ ^ 2) =
        ∑ x : (ZMod m)ˣ, ((∑ χ ∈ s, a χ * χ (x : ZMod m)) * star (∑ ψ ∈ s, a ψ * ψ (x : ZMod m))).re := by
    apply Finset.sum_congr rfl
    intro x _
    exact norm_sq_eq_re_mul_star _
  have hRHS : ((m.totient : ℂ) * ∑ χ ∈ s, a χ * star (a χ)).re =
      (m.totient : ℝ) * ∑ χ ∈ s, ‖a χ‖ ^ 2 := by
    have hs : ∑ χ ∈ s, a χ * star (a χ) = ((∑ χ ∈ s, ‖a χ‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro χ _
      rw [complex_mul_star_self (a χ), Complex.ofReal_pow]
    rw [hs, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact hLHS.trans (hR.trans hRHS)

private lemma norm_form_le {m : ℕ} [NeZero m] (N : ZMod m)
    (s : Finset (DirichletCharacter ℂ m)) (a b : DirichletCharacter ℂ m → ℂ) :
    ‖∑ χ ∈ s, ∑ ψ ∈ s, star (a χ) *
        ((∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m))) / (m.totient : ℂ)) * b ψ‖ ≤
      Real.sqrt (∑ χ ∈ s, ‖a χ‖ ^ 2) * Real.sqrt (∑ ψ ∈ s, ‖b ψ‖ ^ 2) := by
  classical
  have htotPos : (0 : ℝ) < (m.totient : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos m))
  have hrew :
      (∑ χ ∈ s, ∑ ψ ∈ s, star (a χ) *
        ((∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m))) / (m.totient : ℂ)) * b ψ) =
      ((m.totient : ℂ)⁻¹) * ∑ x : (ZMod m)ˣ,
        (star (∑ χ ∈ s, a χ * χ (x : ZMod m))) * (∑ ψ ∈ s, b ψ * ψ (N - (x : ZMod m))) := by
    calc
      _ = ∑ χ ∈ s, ∑ ψ ∈ s, ∑ x : (ZMod m)ˣ,
            (m.totient : ℂ)⁻¹ * ((star (a χ) * star (χ (x : ZMod m))) * (b ψ * ψ (N - (x : ZMod m)))) := by
            apply Finset.sum_congr rfl
            intro χ _
            apply Finset.sum_congr rfl
            intro ψ _
            rw [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro x _
            ring
      _ = ∑ χ ∈ s, ∑ x : (ZMod m)ˣ, ∑ ψ ∈ s,
            (m.totient : ℂ)⁻¹ * ((star (a χ) * star (χ (x : ZMod m))) * (b ψ * ψ (N - (x : ZMod m)))) := by
            apply Finset.sum_congr rfl
            intro χ _
            exact Finset.sum_comm
      _ = ∑ x : (ZMod m)ˣ, ∑ χ ∈ s, ∑ ψ ∈ s,
            (m.totient : ℂ)⁻¹ * ((star (a χ) * star (χ (x : ZMod m))) * (b ψ * ψ (N - (x : ZMod m)))) :=
            Finset.sum_comm
      _ = ((m.totient : ℂ)⁻¹) * ∑ x : (ZMod m)ˣ,
            (star (∑ χ ∈ s, a χ * χ (x : ZMod m))) * (∑ ψ ∈ s, b ψ * ψ (N - (x : ZMod m))) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            rw [star_sum, Finset.sum_mul, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro χ _
            rw [star_mul', Finset.mul_sum, Finset.mul_sum]
  rw [hrew, norm_mul, norm_inv, Complex.norm_natCast]
  have hsum :
      ‖∑ x : (ZMod m)ˣ,
          (star (∑ χ ∈ s, a χ * χ (x : ZMod m))) * (∑ ψ ∈ s, b ψ * ψ (N - (x : ZMod m)))‖ ≤
        ∑ x : (ZMod m)ˣ, ‖∑ χ ∈ s, a χ * χ (x : ZMod m)‖ * ‖∑ ψ ∈ s, b ψ * ψ (N - (x : ZMod m))‖ := by
    calc
      _ ≤ ∑ x : (ZMod m)ˣ,
            ‖(star (∑ χ ∈ s, a χ * χ (x : ZMod m))) * (∑ ψ ∈ s, b ψ * ψ (N - (x : ZMod m)))‖ :=
          norm_sum_le _ _
      _ = _ := by
          apply Finset.sum_congr rfl
          intro x _
          rw [norm_mul, norm_star]
  have hcs :
      (∑ x : (ZMod m)ˣ, ‖∑ χ ∈ s, a χ * χ (x : ZMod m)‖ * ‖∑ ψ ∈ s, b ψ * ψ (N - (x : ZMod m))‖) ≤
        Real.sqrt (∑ x : (ZMod m)ˣ, ‖∑ χ ∈ s, a χ * χ (x : ZMod m)‖ ^ 2) *
          Real.sqrt (∑ x : (ZMod m)ˣ, ‖∑ ψ ∈ s, b ψ * ψ (N - (x : ZMod m))‖ ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
  have hshift :
      (∑ x : (ZMod m)ˣ, ‖∑ ψ ∈ s, b ψ * ψ (N - (x : ZMod m))‖ ^ 2) ≤
        ∑ u : (ZMod m)ˣ, ‖∑ ψ ∈ s, b ψ * ψ (u : ZMod m)‖ ^ 2 := by
    let g : (ZMod m)ˣ → ℝ := fun u => ‖∑ ψ ∈ s, b ψ * ψ (u : ZMod m)‖ ^ 2
    let U : Finset (ZMod m)ˣ := Finset.univ.filter (fun x => IsUnit (N - (x : ZMod m)))
    have hU : (∑ x : (ZMod m)ˣ, ‖∑ ψ ∈ s, b ψ * ψ (N - (x : ZMod m))‖ ^ 2) =
        ∑ x ∈ U, ‖∑ ψ ∈ s, b ψ * ψ (N - (x : ZMod m))‖ ^ 2 := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : (ZMod m)ˣ => IsUnit (N - (x : ZMod m)))]
      have hzero : (∑ x ∈ Finset.univ.filter (fun x : (ZMod m)ˣ => ¬IsUnit (N - (x : ZMod m))),
          ‖∑ ψ ∈ s, b ψ * ψ (N - (x : ZMod m))‖ ^ 2) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        have hnu : ¬IsUnit (N - (x : ZMod m)) := (Finset.mem_filter.mp hx).2
        simp [MulChar.map_nonunit _ hnu]
      rw [hzero, add_zero]
    rw [hU]
    let emb : {x : (ZMod m)ˣ // x ∈ U} → (ZMod m)ˣ :=
      fun x => ((Finset.mem_filter.mp x.2).2).unit
    have hemb_inj : Function.Injective emb := by
      intro x y hxy
      have hval : ((emb x : (ZMod m)ˣ) : ZMod m) = ((emb y : (ZMod m)ˣ) : ZMod m) :=
        congrArg Units.val hxy
      have hxval : ((emb x : (ZMod m)ˣ) : ZMod m) = N - (x.1 : ZMod m) :=
        ((Finset.mem_filter.mp x.2).2).unit_spec
      have hyval : ((emb y : (ZMod m)ˣ) : ZMod m) = N - (y.1 : ZMod m) :=
        ((Finset.mem_filter.mp y.2).2).unit_spec
      rw [hxval, hyval] at hval
      exact Subtype.ext (Units.ext (sub_right_inj.mp hval))
    have hstep1 :
        (∑ x ∈ U, ‖∑ ψ ∈ s, b ψ * ψ (N - (x : ZMod m))‖ ^ 2) =
          ∑ x ∈ U.attach, g (emb x) := by
      rw [← Finset.sum_attach (s := U)]
      apply Finset.sum_congr rfl
      intro x _
      have hxval : ((emb x : (ZMod m)ˣ) : ZMod m) = N - (x.1 : ZMod m) :=
        ((Finset.mem_filter.mp x.2).2).unit_spec
      simp only [g, hxval]
    rw [hstep1]
    have hstep2 : (∑ x ∈ U.attach, g (emb x)) = ∑ u ∈ U.attach.image emb, g u := by
      symm
      exact Finset.sum_image (fun x _ y _ hxy => hemb_inj hxy)
    rw [hstep2]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  have hle1 :
      (m.totient : ℝ)⁻¹ * (∑ x : (ZMod m)ˣ,
          ‖∑ χ ∈ s, a χ * χ (x : ZMod m)‖ * ‖∑ ψ ∈ s, b ψ * ψ (N - (x : ZMod m))‖) ≤
        (m.totient : ℝ)⁻¹ * (Real.sqrt ((m.totient : ℝ) * ∑ χ ∈ s, ‖a χ‖ ^ 2) *
          Real.sqrt ((m.totient : ℝ) * ∑ ψ ∈ s, ‖b ψ‖ ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr htotPos.le)
    refine hcs.trans ?_
    rw [sum_units_char_sq s a]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    apply Real.sqrt_le_sqrt
    exact hshift.trans_eq (sum_units_char_sq s b)
  have hcalc :
      (m.totient : ℝ)⁻¹ * (Real.sqrt ((m.totient : ℝ) * ∑ χ ∈ s, ‖a χ‖ ^ 2) *
          Real.sqrt ((m.totient : ℝ) * ∑ ψ ∈ s, ‖b ψ‖ ^ 2)) =
        Real.sqrt (∑ χ ∈ s, ‖a χ‖ ^ 2) * Real.sqrt (∑ ψ ∈ s, ‖b ψ‖ ^ 2) := by
    rw [Real.sqrt_mul htotPos.le, Real.sqrt_mul htotPos.le]
    have hsq : Real.sqrt (m.totient : ℝ) * Real.sqrt (m.totient : ℝ) = (m.totient : ℝ) :=
      Real.mul_self_sqrt htotPos.le
    calc
      (m.totient : ℝ)⁻¹ *
          ((Real.sqrt (m.totient : ℝ) * Real.sqrt (∑ χ ∈ s, ‖a χ‖ ^ 2)) *
            (Real.sqrt (m.totient : ℝ) * Real.sqrt (∑ ψ ∈ s, ‖b ψ‖ ^ 2)))
          = ((m.totient : ℝ)⁻¹ * (Real.sqrt (m.totient : ℝ) * Real.sqrt (m.totient : ℝ))) *
              (Real.sqrt (∑ χ ∈ s, ‖a χ‖ ^ 2) * Real.sqrt (∑ ψ ∈ s, ‖b ψ‖ ^ 2)) := by ring
      _ = ((m.totient : ℝ)⁻¹ * (m.totient : ℝ)) *
            (Real.sqrt (∑ χ ∈ s, ‖a χ‖ ^ 2) * Real.sqrt (∑ ψ ∈ s, ‖b ψ‖ ^ 2)) := by rw [hsq]
      _ = _ := by rw [inv_mul_cancel₀ htotPos.ne', one_mul]
  exact (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr htotPos.le)).trans (hle1.trans_eq hcalc)

private lemma sum_v_sq_le (m N : ℕ) [NeZero m] (w : ℕ → ℝ)
    (s : Finset (DirichletCharacter ℂ m)) :
    (∑ χ ∈ s, ‖(∑ n ∈ Finset.range (N + 1), (w n : ℂ) * star (χ (n : ZMod m))) /
        (Real.sqrt (m.totient : ℝ) : ℂ)‖ ^ 2) ≤
      (1 + (N : ℝ) / (m : ℝ)) * ∑ n ∈ Finset.range (N + 1), (w n) ^ 2 := by
  classical
  have hmPos : (0 : ℕ) < m := NeZero.pos m
  have htotPos : (0 : ℝ) < (m.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hmPos)
  have hsub :
      (∑ χ ∈ s, ‖(∑ n ∈ Finset.range (N + 1), (w n : ℂ) * star (χ (n : ZMod m))) /
          (Real.sqrt (m.totient : ℝ) : ℂ)‖ ^ 2) ≤
        ∑ χ : DirichletCharacter ℂ m,
          ‖(∑ n ∈ Finset.range (N + 1), (w n : ℂ) * star (χ (n : ZMod m))) /
            (Real.sqrt (m.totient : ℝ) : ℂ)‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  have hnormDen : ‖(Real.sqrt (m.totient : ℝ) : ℂ)‖ ^ 2 = (m.totient : ℝ) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt htotPos.le]
  have hrew :
      (∑ χ : DirichletCharacter ℂ m,
        ‖(∑ n ∈ Finset.range (N + 1), (w n : ℂ) * star (χ (n : ZMod m))) /
          (Real.sqrt (m.totient : ℝ) : ℂ)‖ ^ 2) =
      (m.totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ m,
          ((∑ n ∈ Finset.range (N + 1), (w n : ℂ) * star (χ (n : ZMod m))) *
            star (∑ n ∈ Finset.range (N + 1), (w n : ℂ) * star (χ (n : ZMod m)))).re := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ _
    rw [norm_div, div_pow, hnormDen, norm_sq_eq_re_mul_star, div_eq_inv_mul]
  have horth :
      ∀ n₁ n₂ : ℕ,
        (∑ χ : DirichletCharacter ℂ m, star (χ (n₁ : ZMod m)) * χ (n₂ : ZMod m)) =
          if IsUnit (n₁ : ZMod m) ∧ (n₁ : ZMod m) = (n₂ : ZMod m) then (m.totient : ℂ) else 0 := by
    intro n₁ n₂
    by_cases hu : IsUnit (n₁ : ZMod m)
    · obtain ⟨u, huEq⟩ := hu
      have hu1 : IsUnit (n₁ : ZMod m) := by rw [← huEq]; exact u.isUnit
      have hstar : ∀ χ : DirichletCharacter ℂ m,
          star (χ (n₁ : ZMod m)) = χ ((u⁻¹ : (ZMod m)ˣ) : ZMod m) := by
        intro χ
        rw [← huEq]
        exact star_char_unit_eq_inv χ u
      have hinvEq : ((u⁻¹ : (ZMod m)ˣ) : ZMod m) = (n₁ : ZMod m)⁻¹ := by
        rw [← huEq, ZMod.inv_coe_unit]
      calc
        _ = ∑ χ : DirichletCharacter ℂ m, χ (n₁ : ZMod m)⁻¹ * χ (n₂ : ZMod m) := by
            apply Finset.sum_congr rfl
            intro χ _
            rw [hstar χ, hinvEq]
        _ = if (n₁ : ZMod m) = (n₂ : ZMod m) then (m.totient : ℂ) else 0 :=
            DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu1 (n₂ : ZMod m)
        _ = if IsUnit (n₁ : ZMod m) ∧ (n₁ : ZMod m) = (n₂ : ZMod m) then (m.totient : ℂ) else 0 := by
            simp [hu1]
    · have hz : ∀ χ : DirichletCharacter ℂ m, χ (n₁ : ZMod m) = 0 :=
        fun χ => MulChar.map_nonunit χ hu
      simp [hz, hu]
  let F : (ZMod m)ˣ → Finset ℕ :=
    fun u => (Finset.range (N + 1)).filter (fun n : ℕ => (n : ZMod m) = (u : ZMod m))
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (ZMod m)ˣ) F := by
    intro u _ v _ huv
    rw [Function.onFun, Finset.disjoint_left]
    intro n hnu hnv
    apply huv
    apply Units.ext
    exact ((Finset.mem_filter.mp hnu).2.symm.trans (Finset.mem_filter.mp hnv).2)
  have hpart :
      (Finset.range (N + 1)).filter (fun n : ℕ => IsUnit (n : ZMod m)) =
        Finset.univ.biUnion F := by
    ext n
    simp only [F, Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hn, ⟨u, hu⟩⟩
      exact ⟨u, ⟨hn, hu.symm⟩⟩
    · rintro ⟨u, hn, hu⟩
      exact ⟨hn, by rw [hu]; exact u.isUnit⟩
  have hC :
      (∑ χ : DirichletCharacter ℂ m,
        (∑ n ∈ Finset.range (N + 1), (w n : ℂ) * star (χ (n : ZMod m))) *
          star (∑ n ∈ Finset.range (N + 1), (w n : ℂ) * star (χ (n : ZMod m)))) =
      (m.totient : ℂ) * ∑ u : (ZMod m)ˣ, (((∑ n ∈ F u, w n) ^ 2 : ℝ) : ℂ) := by
    calc
      _ = ∑ χ : DirichletCharacter ℂ m, ∑ n₁ ∈ Finset.range (N + 1), ∑ n₂ ∈ Finset.range (N + 1),
            ((w n₁ * w n₂ : ℝ) : ℂ) * (star (χ (n₁ : ZMod m)) * χ (n₂ : ZMod m)) := by
            apply Finset.sum_congr rfl
            intro χ _
            rw [star_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro n₁ _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n₂ _
            have hconjR : star ((w n₂ : ℝ) : ℂ) = (w n₂ : ℂ) := by simp
            rw [star_mul', star_star, hconjR]
            push_cast
            ring
      _ = ∑ n₁ ∈ Finset.range (N + 1), ∑ χ : DirichletCharacter ℂ m, ∑ n₂ ∈ Finset.range (N + 1),
            ((w n₁ * w n₂ : ℝ) : ℂ) * (star (χ (n₁ : ZMod m)) * χ (n₂ : ZMod m)) :=
            Finset.sum_comm
      _ = ∑ n₁ ∈ Finset.range (N + 1), ∑ n₂ ∈ Finset.range (N + 1),
            ((w n₁ * w n₂ : ℝ) : ℂ) *
              ∑ χ : DirichletCharacter ℂ m, star (χ (n₁ : ZMod m)) * χ (n₂ : ZMod m) := by
            apply Finset.sum_congr rfl
            intro n₁ _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro n₂ _
            rw [← Finset.mul_sum]
      _ = (m.totient : ℂ) * ∑ n₁ ∈ (Finset.range (N + 1)).filter (fun n : ℕ => IsUnit (n : ZMod m)),
            ∑ n₂ ∈ (Finset.range (N + 1)).filter (fun n : ℕ => (n : ZMod m) = (n₁ : ZMod m)),
              ((w n₁ * w n₂ : ℝ) : ℂ) := by
            rw [Finset.mul_sum]
            rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (N + 1)) (fun n : ℕ => IsUnit (n : ZMod m))]
            have hz :
                (∑ n₁ ∈ (Finset.range (N + 1)).filter (fun n : ℕ => ¬IsUnit (n : ZMod m)),
                  ∑ n₂ ∈ Finset.range (N + 1), ((w n₁ * w n₂ : ℝ) : ℂ) *
                    ∑ χ : DirichletCharacter ℂ m, star (χ (n₁ : ZMod m)) * χ (n₂ : ZMod m)) = 0 := by
              apply Finset.sum_eq_zero
              intro n₁ hn₁
              apply Finset.sum_eq_zero
              intro n₂ _
              rw [horth n₁ n₂]
              have hnu : ¬IsUnit (n₁ : ZMod m) := (Finset.mem_filter.mp hn₁).2
              simp [hnu]
            rw [hz, add_zero]
            apply Finset.sum_congr rfl
            intro n₁ hn₁
            have h1 : IsUnit (n₁ : ZMod m) := (Finset.mem_filter.mp hn₁).2
            rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not (Finset.range (N + 1))
              (fun n : ℕ => (n : ZMod m) = (n₁ : ZMod m))]
            have hz2 :
                (∑ n₂ ∈ (Finset.range (N + 1)).filter (fun n : ℕ => ¬(n : ZMod m) = (n₁ : ZMod m)),
                  ((w n₁ * w n₂ : ℝ) : ℂ) *
                    ∑ χ : DirichletCharacter ℂ m, star (χ (n₁ : ZMod m)) * χ (n₂ : ZMod m)) = 0 := by
              apply Finset.sum_eq_zero
              intro n₂ hn₂
              have hne : (n₁ : ZMod m) ≠ (n₂ : ZMod m) := fun heq => (Finset.mem_filter.mp hn₂).2 heq.symm
              rw [horth n₁ n₂, if_neg (fun hp => hne hp.2), mul_zero]
            rw [hz2, add_zero]
            apply Finset.sum_congr rfl
            intro n₂ hn₂
            have heq : (n₁ : ZMod m) = (n₂ : ZMod m) := (Finset.mem_filter.mp hn₂).2.symm
            rw [horth n₁ n₂, if_pos ⟨h1, heq⟩]
            ring
      _ = _ := by
            congr 1
            rw [hpart, Finset.sum_biUnion hdisj]
            apply Finset.sum_congr rfl
            intro u _
            have hinner :
                (∑ n₁ ∈ F u, ∑ n₂ ∈ (Finset.range (N + 1)).filter (fun n : ℕ => (n : ZMod m) = (n₁ : ZMod m)),
                  ((w n₁ * w n₂ : ℝ) : ℂ)) =
                ∑ n₁ ∈ F u, ∑ n₂ ∈ F u, ((w n₁ * w n₂ : ℝ) : ℂ) := by
              apply Finset.sum_congr rfl
              intro n₁ hn₁
              have hn₁u : (n₁ : ZMod m) = (u : ZMod m) := (Finset.mem_filter.mp hn₁).2
              congr 1
              ext n₂
              simp [F, hn₁u]
            rw [hinner, sq]
            push_cast
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro n₁ _
            rw [Finset.mul_sum]
  have hRe := congrArg Complex.re hC
  simp only [Complex.re_sum] at hRe
  have hRHSre :
      ((m.totient : ℂ) * ∑ u : (ZMod m)ˣ, (((∑ n ∈ F u, w n) ^ 2 : ℝ) : ℂ)).re =
        (m.totient : ℝ) * ∑ u : (ZMod m)ˣ, (∑ n ∈ F u, w n) ^ 2 := by
    have hcast :
        (m.totient : ℂ) * ∑ u : (ZMod m)ˣ, (((∑ n ∈ F u, w n) ^ 2 : ℝ) : ℂ) =
        (((m.totient : ℝ) * ∑ u : (ZMod m)ˣ, (∑ n ∈ F u, w n) ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hcast, Complex.ofReal_re]
  have hEq :
      (∑ χ : DirichletCharacter ℂ m,
        ‖(∑ n ∈ Finset.range (N + 1), (w n : ℂ) * star (χ (n : ZMod m))) /
          (Real.sqrt (m.totient : ℝ) : ℂ)‖ ^ 2) =
      ∑ u : (ZMod m)ˣ, (∑ n ∈ F u, w n) ^ 2 := by
    rw [hrew, hRe, hRHSre, ← mul_assoc, inv_mul_cancel₀ htotPos.ne', one_mul]
  refine hsub.trans (hEq ▸ ?_)
  have hcard : ∀ u : (ZMod m)ˣ, ((F u).card : ℝ) ≤ 1 + (N : ℝ) / (m : ℝ) := by
    intro u
    let r : ℕ := ((u : ZMod m)).val
    have hsubF : F u ⊆ (Finset.range (N / m + 1)).image (fun q => r + m * q) := by
      intro n hn
      rcases Finset.mem_filter.mp hn with ⟨hnR, hnMod⟩
      have hnle : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hnR)
      have hmod : n % m = r := by
        rw [← ZMod.val_natCast (n := m) n, hnMod]
      refine Finset.mem_image.mpr ⟨n / m, Finset.mem_range.mpr ?_, ?_⟩
      · exact Nat.lt_succ_of_le (Nat.div_le_div_right hnle)
      · rw [← hmod, Nat.mod_add_div n m]
    have hcardNat : (F u).card ≤ N / m + 1 := by
      calc
        (F u).card ≤ ((Finset.range (N / m + 1)).image (fun q => r + m * q)).card :=
            Finset.card_le_card hsubF
        _ ≤ (Finset.range (N / m + 1)).card := Finset.card_image_le
        _ = N / m + 1 := Finset.card_range _
    have hdivR : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / (m : ℝ) := by
      have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hmPos
      rw [le_div_iff₀ hmR]
      exact_mod_cast Nat.div_mul_le_self N m
    have h1 : ((F u).card : ℝ) ≤ ((N / m + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hcardNat
    have h2 : ((N / m + 1 : ℕ) : ℝ) = ((N / m : ℕ) : ℝ) + 1 := by push_cast; rfl
    linarith
  have hterm : ∀ u : (ZMod m)ˣ,
      (∑ n ∈ F u, w n) ^ 2 ≤ (1 + (N : ℝ) / (m : ℝ)) * ∑ n ∈ F u, (w n) ^ 2 := by
    intro u
    have hcs := sq_sum_le_card_mul_sum_sq (s := F u) (f := w)
    have hsum_nn : 0 ≤ ∑ n ∈ F u, (w n) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    exact hcs.trans (mul_le_mul_of_nonneg_right (hcard u) hsum_nn)
  calc
    (∑ u : (ZMod m)ˣ, (∑ n ∈ F u, w n) ^ 2)
        ≤ ∑ u : (ZMod m)ˣ, (1 + (N : ℝ) / (m : ℝ)) * ∑ n ∈ F u, (w n) ^ 2 :=
          Finset.sum_le_sum (fun u _ => hterm u)
    _ = (1 + (N : ℝ) / (m : ℝ)) * ∑ u : (ZMod m)ˣ, ∑ n ∈ F u, (w n) ^ 2 := by
          rw [← Finset.mul_sum]
    _ ≤ (1 + (N : ℝ) / (m : ℝ)) * ∑ n ∈ Finset.range (N + 1), (w n) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← Finset.sum_biUnion hdisj]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            rcases Finset.mem_biUnion.mp hn with ⟨u, _, hnu⟩
            exact (Finset.mem_filter.mp hnu).1
          · intro n _ _
            exact sq_nonneg _

private lemma dyadic_sqrt_sum_le (K : ℕ) (S : Finset ℕ)
    (hS : ∀ k ∈ S, 1 ≤ k ∧ k < K) :
    (∑ k ∈ S, Real.sqrt (((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ))) ≤ 2 + Real.sqrt 2 := by
  let r : ℝ := 1 / Real.sqrt 2
  have hr_pos : 0 < r := by positivity
  have hr_lt : r < 1 := by
    have hs : 1 < Real.sqrt 2 := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    exact (div_lt_one (by positivity)).mpr hs
  have hterm : ∀ k ∈ S,
      Real.sqrt (((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)) = r ^ (K - 1 - k) := by
    intro k hk
    have hklt : k < K := (hS k hk).2
    have hpow : K - 1 - k + (k + 1) = K := by omega
    have hrpow : (r ^ (K - 1 - k)) ^ 2 = ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ) := by
      have hsq2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have h2K : ((2 ^ K : ℕ) : ℝ) = ((2 ^ (k + 1) : ℕ) : ℝ) * ((2 ^ (K - 1 - k) : ℕ) : ℝ) := by
        rw [← Nat.cast_mul, ← pow_add, add_comm, hpow]
      rw [h2K]
      push_cast
      rw [← pow_mul, mul_comm (K - 1 - k) 2, pow_mul, div_pow, one_pow, hsq2, one_div]
      have hne1 : (2 : ℝ) ^ (k + 1) ≠ 0 := by positivity
      have hne2 : (2 : ℝ) ^ (K - 1 - k) ≠ 0 := by positivity
      field_simp [hne1, hne2]
      rw [← mul_pow]
      norm_num
    rw [← hrpow, Real.sqrt_sq (pow_nonneg hr_pos.le _)]
  have hinj : ∀ a ∈ S, ∀ b ∈ S, K - 1 - a = K - 1 - b → a = b := by
    intro a ha b hb hab
    have haK : a < K := (hS a ha).2
    have hbK : b < K := (hS b hb).2
    omega
  have hsub :
      (∑ k ∈ S, r ^ (K - 1 - k)) ≤ ∑ j ∈ Finset.range K, r ^ j := by
    have himg : (∑ k ∈ S, r ^ (K - 1 - k)) = ∑ j ∈ S.image (fun k => K - 1 - k), r ^ j := by
      symm
      exact Finset.sum_image (fun a ha b hb hab => hinj a ha b hb hab)
    rw [himg]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      rcases Finset.mem_image.mp hj with ⟨k, hk, rfl⟩
      have hk1 : 1 ≤ k := (hS k hk).1
      have hkK : k < K := (hS k hk).2
      exact Finset.mem_range.mpr (by omega)
    · intro j _ _
      exact pow_nonneg hr_pos.le _
  have hgeom : (∑ j ∈ Finset.range K, r ^ j) * (1 - r) ≤ 1 := by
    have hflip : (∑ j ∈ Finset.range K, r ^ j) * (1 - r) = -((∑ j ∈ Finset.range K, r ^ j) * (r - 1)) := by
      ring
    rw [hflip, geom_sum_mul]
    have hpow_nn : 0 ≤ r ^ K := pow_nonneg hr_pos.le K
    linarith
  have hgeom2 : ∑ j ∈ Finset.range K, r ^ j ≤ 1 / (1 - r) :=
    (le_div_iff₀ (sub_pos.mpr hr_lt)).mpr hgeom
  have hid : 1 / (1 - r) = 2 + Real.sqrt 2 := by
    have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hne1 : Real.sqrt 2 ≠ 0 := by positivity
    have hne2 : 1 - r ≠ 0 := (sub_pos.mpr hr_lt).ne'
    symm
    rw [eq_div_iff hne2]
    dsimp only [r]
    field_simp [hne1]
    nlinarith [hsq2]
  calc
    (∑ k ∈ S, Real.sqrt (((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)))
        = ∑ k ∈ S, r ^ (K - 1 - k) := Finset.sum_congr rfl hterm
    _ ≤ ∑ j ∈ Finset.range K, r ^ j := hsub
    _ ≤ 1 / (1 - r) := hgeom2
    _ = 2 + Real.sqrt 2 := hid

private lemma dyadic_lin_sum_le (K : ℕ) (S : Finset ℕ)
    (hS : ∀ k ∈ S, 1 ≤ k ∧ k < K) :
    (∑ k ∈ S, ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)) ≤ 2 := by
  have hterm : ∀ k ∈ S,
      ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ) = (1 / 2 : ℝ) ^ (K - 1 - k) := by
    intro k hk
    have hkK : k < K := (hS k hk).2
    have hpow : K - 1 - k + (k + 1) = K := by omega
    have h2K : ((2 ^ K : ℕ) : ℝ) = ((2 ^ (k + 1) : ℕ) : ℝ) * ((2 ^ (K - 1 - k) : ℕ) : ℝ) := by
      rw [← Nat.cast_mul, ← pow_add, add_comm, hpow]
    rw [h2K]
    push_cast
    rw [one_div, inv_pow]
    have hne1 : (2 : ℝ) ^ (k + 1) ≠ 0 := by positivity
    have hne2 : (2 : ℝ) ^ (K - 1 - k) ≠ 0 := by positivity
    field_simp [hne1, hne2]
  have hinj : ∀ a ∈ S, ∀ b ∈ S, K - 1 - a = K - 1 - b → a = b := by
    intro a ha b hb hab
    have haK : a < K := (hS a ha).2
    have hbK : b < K := (hS b hb).2
    omega
  have hsub :
      (∑ k ∈ S, (1 / 2 : ℝ) ^ (K - 1 - k)) ≤ ∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ j := by
    have himg : (∑ k ∈ S, (1 / 2 : ℝ) ^ (K - 1 - k)) =
        ∑ j ∈ S.image (fun k => K - 1 - k), (1 / 2 : ℝ) ^ j := by
      symm
      exact Finset.sum_image (fun a ha b hb hab => hinj a ha b hb hab)
    rw [himg]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      rcases Finset.mem_image.mp hj with ⟨k, hk, rfl⟩
      exact Finset.mem_range.mpr (by have := (hS k hk).2; omega)
    · intro j _ _
      positivity
  have hgeom : (∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ j) * (1 - (1 / 2 : ℝ)) ≤ 1 := by
    have hflip : (∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ j) * (1 - (1 / 2 : ℝ)) =
        -((∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ j) * ((1 / 2 : ℝ) - 1)) := by ring
    rw [hflip, geom_sum_mul]
    have hpow_nn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ K := by positivity
    linarith
  calc
    (∑ k ∈ S, ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ))
        = ∑ k ∈ S, (1 / 2 : ℝ) ^ (K - 1 - k) := Finset.sum_congr rfl hterm
    _ ≤ ∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ j := hsub
    _ ≤ 2 := by linarith

theorem Conjectures.Goldbach.DyadicTruncationFormBudget :
    ∀ (N K : ℕ) (S : Finset ℕ) (w : ℕ → ℝ)
        (z : (k : ℕ) → DirichletCharacter ℂ (2^(k+1)) → ℂ) (E : ℝ),
      N < 2^K → 0 ≤ E → (∀ k ∈ S, 1 ≤ k ∧ k < K) →
      let s := fun k : ℕ => (Finset.univ : Finset (DirichletCharacter ℂ (2^(k+1)))).filter (fun χ => χ.conductor = 2^(k+1))
      let v := fun (k : ℕ) (χ : DirichletCharacter ℂ (2^(k+1))) =>
        (∑ n ∈ Finset.range (N+1), (w n : ℂ) * star (χ (n : ZMod (2^(k+1))))) /
          (Real.sqrt (((2^(k+1) : ℕ).totient) : ℝ) : ℂ)
      let R := fun (k : ℕ) (a : DirichletCharacter ℂ (2^(k+1)) → ℂ) =>
        (∑ χ ∈ s k, ∑ ψ ∈ s k, star (a χ) *
          ((∑ x : (ZMod (2^(k+1)))ˣ, star (χ (x : ZMod (2^(k+1)))) * ψ ((N : ZMod (2^(k+1))) - (x : ZMod (2^(k+1))))) /
            (((2^(k+1) : ℕ).totient) : ℂ)) * a ψ).re
      (∀ k ∈ S, (∑ χ ∈ s k, ‖v k χ-z k χ‖^2) ≤ E^2) →
        |∑ k ∈ S, ((2^(k+1) : ℕ) : ℝ) / ((2^K : ℕ) : ℝ) * (R k (v k) - R k (z k))| ≤
          10 * E * Real.sqrt (∑ n ∈ Finset.range (N+1), (w n)^2) + 2*E^2 := by
  intro N K S w z E hNK hE hS s v R hdiff
  dsimp only [s, v, R] at *
  let W : ℝ := ∑ n ∈ Finset.range (N + 1), (w n) ^ 2
  have hW_nn : 0 ≤ W := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hterm : ∀ k ∈ S,
      |((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ) * (R k (v k) - R k (z k))| ≤
        2 * Real.sqrt 2 * E * Real.sqrt W *
          Real.sqrt (((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)) +
          (((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)) * E ^ 2 := by
    intro k hk
    have hkK : k < K := (hS k hk).2
    have hmNe : NeZero (2 ^ (k + 1)) := ⟨by positivity⟩
    let Q (a b : DirichletCharacter ℂ (2 ^ (k + 1)) → ℂ) : ℂ :=
      ∑ χ ∈ s k, ∑ ψ ∈ s k, star (a χ) *
        ((∑ x : (ZMod (2 ^ (k + 1)))ˣ,
          star (χ (x : ZMod (2 ^ (k + 1)))) * ψ ((N : ZMod (2 ^ (k + 1))) - (x : ZMod (2 ^ (k + 1))))) /
            (((2 ^ (k + 1) : ℕ).totient) : ℂ)) * b ψ
    let d : DirichletCharacter ℂ (2 ^ (k + 1)) → ℂ := fun χ => v k χ - z k χ
    have hsplit : Q (v k) (v k) - Q (z k) (z k) = Q (v k) d + Q d (v k) - Q d d := by
      simp only [Q, d]
      calc
        _ = ∑ χ ∈ s k, ∑ ψ ∈ s k,
              (star (v k χ) * ((∑ x : (ZMod (2 ^ (k + 1)))ˣ,
                star (χ (x : ZMod (2 ^ (k + 1)))) * ψ ((N : ZMod (2 ^ (k + 1))) - (x : ZMod (2 ^ (k + 1))))) /
                  (((2 ^ (k + 1) : ℕ).totient) : ℂ)) * v k ψ -
               star (z k χ) * ((∑ x : (ZMod (2 ^ (k + 1)))ˣ,
                star (χ (x : ZMod (2 ^ (k + 1)))) * ψ ((N : ZMod (2 ^ (k + 1))) - (x : ZMod (2 ^ (k + 1))))) /
                  (((2 ^ (k + 1) : ℕ).totient) : ℂ)) * z k ψ) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro χ _
              rw [← Finset.sum_sub_distrib]
        _ = ∑ χ ∈ s k, ∑ ψ ∈ s k,
              (star (v k χ) * ((∑ x : (ZMod (2 ^ (k + 1)))ˣ,
                star (χ (x : ZMod (2 ^ (k + 1)))) * ψ ((N : ZMod (2 ^ (k + 1))) - (x : ZMod (2 ^ (k + 1))))) /
                  (((2 ^ (k + 1) : ℕ).totient) : ℂ)) * (v k ψ - z k ψ) +
               star (v k χ - z k χ) * ((∑ x : (ZMod (2 ^ (k + 1)))ˣ,
                star (χ (x : ZMod (2 ^ (k + 1)))) * ψ ((N : ZMod (2 ^ (k + 1))) - (x : ZMod (2 ^ (k + 1))))) /
                  (((2 ^ (k + 1) : ℕ).totient) : ℂ)) * v k ψ -
               star (v k χ - z k χ) * ((∑ x : (ZMod (2 ^ (k + 1)))ˣ,
                star (χ (x : ZMod (2 ^ (k + 1)))) * ψ ((N : ZMod (2 ^ (k + 1))) - (x : ZMod (2 ^ (k + 1))))) /
                  (((2 ^ (k + 1) : ℕ).totient) : ℂ)) * (v k ψ - z k ψ)) := by
              apply Finset.sum_congr rfl
              intro χ _
              apply Finset.sum_congr rfl
              intro ψ _
              rw [star_sub]
              ring
        _ = _ := by
              simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hRdiff : |R k (v k) - R k (z k)| ≤ ‖Q (v k) (v k) - Q (z k) (z k)‖ := by
      have hre : R k (v k) - R k (z k) = (Q (v k) (v k) - Q (z k) (z k)).re := by
        simp [R, Q]
      rw [hre]
      exact Complex.abs_re_le_norm _
    have hdnorm : Real.sqrt (∑ χ ∈ s k, ‖d χ‖ ^ 2) ≤ E := by
      rw [← Real.sqrt_sq hE]
      exact Real.sqrt_le_sqrt (hdiff k hk)
    have hvnorm :
        Real.sqrt (∑ χ ∈ s k, ‖v k χ‖ ^ 2) ≤
          Real.sqrt (1 + (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ)) * Real.sqrt W := by
      rw [← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt (sum_v_sq_le (2 ^ (k + 1)) N w (s k))
    have hQ1 : ‖Q (v k) d‖ ≤ Real.sqrt (1 + (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ)) * Real.sqrt W * E := by
      refine (norm_form_le (N : ZMod (2 ^ (k + 1))) (s k) (v k) d).trans ?_
      exact mul_le_mul hvnorm hdnorm (Real.sqrt_nonneg _) (by positivity)
    have hQ2 : ‖Q d (v k)‖ ≤ E * (Real.sqrt (1 + (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ)) * Real.sqrt W) := by
      refine (norm_form_le (N : ZMod (2 ^ (k + 1))) (s k) d (v k)).trans ?_
      exact mul_le_mul hdnorm hvnorm (Real.sqrt_nonneg _) hE
    have hQ3 : ‖Q d d‖ ≤ E ^ 2 := by
      refine (norm_form_le (N : ZMod (2 ^ (k + 1))) (s k) d d).trans ?_
      rw [sq]
      exact mul_le_mul hdnorm hdnorm (Real.sqrt_nonneg _) hE
    have hRbound :
        |R k (v k) - R k (z k)| ≤
          2 * E * Real.sqrt W * Real.sqrt (1 + (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ)) + E ^ 2 := by
      have htri : ‖Q (v k) d + Q d (v k) - Q d d‖ ≤ ‖Q (v k) d‖ + ‖Q d (v k)‖ + ‖Q d d‖ := by
        calc
          ‖Q (v k) d + Q d (v k) - Q d d‖
              ≤ ‖Q (v k) d + Q d (v k)‖ + ‖Q d d‖ := norm_sub_le _ _
          _ ≤ ‖Q (v k) d‖ + ‖Q d (v k)‖ + ‖Q d d‖ := by gcongr; exact norm_add_le _ _
      rw [hsplit] at hRdiff
      linarith [hRdiff, htri, hQ1, hQ2, hQ3]
    have hwt : 0 ≤ ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ) := by positivity
    have hratio :
        (((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)) *
            Real.sqrt (1 + (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ)) ≤
          Real.sqrt 2 * Real.sqrt (((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)) := by
      have hmPos : (0 : ℝ) < ((2 ^ (k + 1) : ℕ) : ℝ) := by positivity
      have hKPos : (0 : ℝ) < ((2 ^ K : ℕ) : ℝ) := by positivity
      have hmleK : ((2 ^ (k + 1) : ℕ) : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_of_lt hkK)
      have hNltK : (N : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast hNK.le
      have hbound :
          1 + (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ) ≤
            2 * (((2 ^ K : ℕ) : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ)) := by
        have h1 : (1 : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ) :=
          (one_le_div hmPos).mpr hmleK
        have h2 : (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ) ≤
            ((2 ^ K : ℕ) : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right hNltK hmPos.le
        linarith
      calc
        (((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)) *
            Real.sqrt (1 + (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ))
            ≤ (((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)) *
                Real.sqrt (2 * (((2 ^ K : ℕ) : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ))) := by
              gcongr
        _ = Real.sqrt 2 *
              ((((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)) *
                Real.sqrt (((2 ^ K : ℕ) : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ))) := by
              rw [Real.sqrt_mul (by norm_num)]
              ring
        _ = Real.sqrt 2 * Real.sqrt (((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)) := by
              congr 1
              let a : ℝ := ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)
              have ha : 0 < a := by positivity
              have hinv : ((2 ^ K : ℕ) : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ) = a⁻¹ := by
                simp only [a, inv_div]
              rw [hinv, Real.sqrt_inv]
              calc
                a * (Real.sqrt a)⁻¹ = (Real.sqrt a * Real.sqrt a) * (Real.sqrt a)⁻¹ := by
                      rw [Real.mul_self_sqrt ha.le]
                _ = Real.sqrt a := by
                      rw [mul_assoc, mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr ha), mul_one]
    rw [abs_mul, abs_of_nonneg hwt]
    calc
      (((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)) * |R k (v k) - R k (z k)|
          ≤ (((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)) *
              (2 * E * Real.sqrt W * Real.sqrt (1 + (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ)) + E ^ 2) :=
            mul_le_mul_of_nonneg_left hRbound hwt
      _ = 2 * E * Real.sqrt W *
              ((((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)) *
                Real.sqrt (1 + (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ))) +
            (((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)) * E ^ 2 := by ring
      _ ≤ 2 * E * Real.sqrt W *
              (Real.sqrt 2 * Real.sqrt (((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ))) +
            (((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)) * E ^ 2 := by
            gcongr
      _ = _ := by ring
  have hsum1 :
      |∑ k ∈ S, ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ) * (R k (v k) - R k (z k))| ≤
        ∑ k ∈ S, |((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ) * (R k (v k) - R k (z k))| :=
    Finset.abs_sum_le_sum_abs _ _
  have hsum2 :
      (∑ k ∈ S, |((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ) * (R k (v k) - R k (z k))|) ≤
        2 * Real.sqrt 2 * E * Real.sqrt W *
            (∑ k ∈ S, Real.sqrt (((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ))) +
          (∑ k ∈ S, ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)) * E ^ 2 := by
    calc
      _ ≤ ∑ k ∈ S, (2 * Real.sqrt 2 * E * Real.sqrt W *
            Real.sqrt (((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)) +
            (((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)) * E ^ 2) :=
          Finset.sum_le_sum hterm
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have hconst : 2 * Real.sqrt 2 * (2 + Real.sqrt 2) ≤ 10 := by
    have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hlt : Real.sqrt 2 < 3 / 2 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    nlinarith [hsq2, hlt]
  have hsqrt_bound :
      2 * Real.sqrt 2 * E * Real.sqrt W *
          (∑ k ∈ S, Real.sqrt (((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ))) ≤
        10 * E * Real.sqrt W := by
    have hEW : 0 ≤ E * Real.sqrt W := mul_nonneg hE (Real.sqrt_nonneg _)
    calc
      2 * Real.sqrt 2 * E * Real.sqrt W *
          (∑ k ∈ S, Real.sqrt (((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)))
          ≤ 2 * Real.sqrt 2 * E * Real.sqrt W * (2 + Real.sqrt 2) := by
            gcongr
            exact dyadic_sqrt_sum_le K S hS
      _ = (2 * Real.sqrt 2 * (2 + Real.sqrt 2)) * (E * Real.sqrt W) := by ring
      _ ≤ 10 * (E * Real.sqrt W) := mul_le_mul_of_nonneg_right hconst hEW
      _ = 10 * E * Real.sqrt W := by ring
  have hlin_bound :
      (∑ k ∈ S, ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)) * E ^ 2 ≤ 2 * E ^ 2 := by
    exact mul_le_mul_of_nonneg_right (dyadic_lin_sum_le K S hS) (sq_nonneg E)
  exact hsum1.trans (hsum2.trans (add_le_add hsqrt_bound hlin_bound))
