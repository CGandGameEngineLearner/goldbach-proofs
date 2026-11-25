import Mathlib

open Filter
open scoped Topology

theorem PEqualNP.Outside.L_goldbach_pp_uniform_removal : let A := fun k : ℕ => if 0 < ((Finset.Icc 2 (Nat.log 2 k)).filter (fun a => k.minFac ^ a=k)).card then Real.log (k:ℝ) else 0; ∀ ε : ℝ, 0<ε → ∃ X : ℕ, ∀ n≥X, ∀ v : ℕ → ℝ, (∀ k, |v k|≤1) → |(∑ k ∈ Finset.range (n+1), A k*v k*Real.log ((n+1:ℕ):ℝ))/(n:ℝ)| < ε := by
  dsimp only
  intro ε hε
  have hsmall : Tendsto (fun x : ℝ => 12 * (Real.log x ^ 3 / x ^ (1/2:ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ (1/6:ℝ)) atTop (𝓝 0) :=
      (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/6)).tendsto_div_nhds_zero
    have h3 : Tendsto (fun x : ℝ => Real.log x ^ 3 / x ^ (1/2:ℝ)) atTop (𝓝 0) := by
      have h2 : Tendsto (fun x : ℝ => (Real.log x / x ^ (1/6:ℝ))^3) atTop (𝓝 0) := by
        simpa using h1.pow 3
      refine h2.congr' ?_
      filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
      have hx' : 0 ≤ x := le_of_lt hx
      have hpow : (x ^ (1/6:ℝ))^3 = x ^ (1/2:ℝ) := by
        rw [← Real.rpow_natCast (x ^ (1/6:ℝ)) 3, ← Real.rpow_mul hx']
        norm_num
      rw [div_pow, hpow]
    simpa using h3.const_mul 12
  have hcomp : Tendsto (fun n : ℕ => 12 * (Real.log (n:ℝ) ^ 3 / (n:ℝ) ^ (1/2:ℝ))) atTop (𝓝 0) := by
    have h := hsmall.comp tendsto_natCast_atTop_atTop
    refine h.congr' ?_
    filter_upwards with m
    simp
  have hev : ∀ᶠ n : ℕ in atTop, 12 * (Real.log (n:ℝ) ^ 3 / (n:ℝ) ^ (1/2:ℝ)) < ε :=
    hcomp.eventually (Iio_mem_nhds hε)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hev
  refine ⟨max X₀ 4, ?_⟩
  intro n hn v hv
  have hn4 : 4 ≤ n := le_trans (le_max_right _ _) hn
  have hnX : X₀ ≤ n := le_trans (le_max_left _ _) hn
  have hεn := hX₀ n hnX
  have hnpos : (0:ℝ) < (n:ℝ) := by
    have h : (0:ℕ) < n := by omega
    exact_mod_cast h
  have hlogn1 : 1 ≤ Real.log (n:ℝ) := by
    have h4 : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn4
    have h1 : Real.log 4 ≤ Real.log (n:ℝ) := Real.log_le_log (by norm_num) h4
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    linarith [Real.log_two_gt_d9]
  have hlognn : 0 ≤ Real.log (n:ℝ) := by linarith
  have hLpos : 0 < Real.log (((n+1:ℕ)):ℝ) := by
    apply Real.log_pos
    push_cast
    have h : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  have hLone : 1 ≤ Real.log (((n+1:ℕ)):ℝ) := by
    have h5 : (4:ℝ) ≤ (((n+1:ℕ)):ℝ) := by
      push_cast
      have h : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn4
      linarith
    have h1 : Real.log 4 ≤ Real.log (((n+1:ℕ)):ℝ) := Real.log_le_log (by norm_num) h5
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    linarith [Real.log_two_gt_d9]
  set A : ℕ → ℝ := fun k => if 0 < ((Finset.Icc 2 (Nat.log 2 k)).filter (fun a => k.minFac ^ a=k)).card then Real.log (k:ℝ) else 0 with hA
  have hAeval : ∀ k, A k = if 0 < ((Finset.Icc 2 (Nat.log 2 k)).filter (fun a => k.minFac ^ a = k)).card then Real.log (k:ℝ) else 0 := by
    intro k
    rw [hA]
  have hA0 : A 0 = 0 := by
    rw [hAeval 0]
    have hempty : ((Finset.Icc 2 (Nat.log 2 0)).filter (fun a => (0:ℕ).minFac ^ a = 0)).card = 0 := by
      rw [Nat.log_zero_right]
      simp
    rw [hempty]
    simp
  have hAle : ∀ k, A k = 0 ∨ A k = Real.log (k:ℝ) := by
    intro k
    rw [hAeval k]
    split_ifs with h
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hAnn : ∀ k, 0 ≤ A k := by
    intro k
    rcases hAle k with h | h
    · rw [h]
    · rw [h]
      by_cases hk : k = 0
      · subst hk; simp
      · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk)
  set S := (Finset.range (n+1)).filter (fun k => A k ≠ 0) with hS
  have hsub : S ⊆ Finset.range (n+1) := Finset.filter_subset _ _
  have hsumA : (∑ k ∈ Finset.range (n+1), A k) = ∑ k ∈ S, A k := by
    refine (Finset.sum_subset hsub ?_).symm
    intro k hk hkS
    by_contra hne
    exact hkS (Finset.mem_filter.mpr ⟨hk, hne⟩)
  have hTa : ∀ a ∈ Finset.Icc 2 (Nat.log 2 n),
      ((Finset.range (n+1)).filter (fun k => k.minFac ^ a = k)).card ≤ Nat.sqrt n + 2 := by
    intro a ha
    have ha2 : 2 ≤ a := (Finset.mem_Icc.mp ha).1
    have hinj : Set.InjOn (fun k : ℕ => k.minFac)
        ↑((Finset.range (n+1)).filter (fun k => k.minFac ^ a = k)) := by
      intro k1 hk1 k2 hk2 heq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk1 hk2
      have heq' : k1.minFac = k2.minFac := heq
      calc k1 = k1.minFac ^ a := hk1.2.symm
        _ = k2.minFac ^ a := by rw [heq']
        _ = k2 := hk2.2
    have hmaps : Set.MapsTo (fun k : ℕ => k.minFac)
        ↑((Finset.range (n+1)).filter (fun k => k.minFac ^ a = k))
        ↑(Finset.range (Nat.sqrt n + 2)) := by
      intro k hk
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk
      simp only [Finset.coe_range, Set.mem_Iio]
      have hk1 : k ≤ n := by omega
      have h2 : k.minFac ^ 2 ≤ n := by
        calc k.minFac ^ 2 ≤ k.minFac ^ a := Nat.pow_le_pow_right (Nat.minFac_pos k) ha2
          _ = k := hk.2
          _ ≤ n := hk1
      have h3 : k.minFac ≤ Nat.sqrt n := Nat.le_sqrt'.mpr h2
      omega
    calc ((Finset.range (n+1)).filter (fun k => k.minFac ^ a = k)).card
        ≤ (Finset.range (Nat.sqrt n + 2)).card := Finset.card_le_card_of_injOn _ hmaps hinj
      _ = Nat.sqrt n + 2 := Finset.card_range _
  have hSsub : S ⊆ (Finset.Icc 2 (Nat.log 2 n)).biUnion
      (fun a => (Finset.range (n+1)).filter (fun k => k.minFac ^ a = k)) := by
    intro k hk
    rw [hS, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkr, hkA⟩ := hk
    have hcardpos : 0 < ((Finset.Icc 2 (Nat.log 2 k)).filter (fun a => k.minFac ^ a = k)).card := by
      rw [hAeval k] at hkA
      split_ifs at hkA with h
      · exact h
      · exact absurd rfl hkA
    obtain ⟨a, hmem⟩ := Finset.card_pos.mp hcardpos
    rw [Finset.mem_filter, Finset.mem_Icc] at hmem
    obtain ⟨⟨ha2, halog⟩, hmin⟩ := hmem
    refine Finset.mem_biUnion.mpr ⟨a, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨ha2, le_trans halog (Nat.log_mono_right (by omega))⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hkr, hmin⟩
  have hScard : S.card ≤ (Nat.log 2 n + 1) * (Nat.sqrt n + 2) := by
    have h1 : S.card ≤ ((Finset.Icc 2 (Nat.log 2 n)).biUnion
        (fun a => (Finset.range (n+1)).filter (fun k => k.minFac ^ a = k))).card :=
      Finset.card_le_card hSsub
    have h2 : ((Finset.Icc 2 (Nat.log 2 n)).biUnion
        (fun a => (Finset.range (n+1)).filter (fun k => k.minFac ^ a = k))).card
        ≤ ∑ a ∈ Finset.Icc 2 (Nat.log 2 n),
            ((Finset.range (n+1)).filter (fun k => k.minFac ^ a = k)).card :=
      Finset.card_biUnion_le
    have h3 : ∑ a ∈ Finset.Icc 2 (Nat.log 2 n),
        ((Finset.range (n+1)).filter (fun k => k.minFac ^ a = k)).card
        ≤ ∑ a ∈ Finset.Icc 2 (Nat.log 2 n), (Nat.sqrt n + 2) := Finset.sum_le_sum hTa
    have h4 : ∑ a ∈ Finset.Icc 2 (Nat.log 2 n), (Nat.sqrt n + 2)
        = (Finset.Icc 2 (Nat.log 2 n)).card * (Nat.sqrt n + 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp
    have h5 : (Finset.Icc 2 (Nat.log 2 n)).card ≤ Nat.log 2 n + 1 := by
      have hss : Finset.Icc 2 (Nat.log 2 n) ⊆ Finset.range (Nat.log 2 n + 1) := by
        intro a ha
        rw [Finset.mem_Icc] at ha
        rw [Finset.mem_range]
        omega
      calc (Finset.Icc 2 (Nat.log 2 n)).card ≤ (Finset.range (Nat.log 2 n + 1)).card :=
            Finset.card_le_card hss
        _ = Nat.log 2 n + 1 := Finset.card_range _
    calc S.card ≤ ((Finset.Icc 2 (Nat.log 2 n)).biUnion
            (fun a => (Finset.range (n+1)).filter (fun k => k.minFac ^ a = k))).card := h1
      _ ≤ ∑ a ∈ Finset.Icc 2 (Nat.log 2 n),
            ((Finset.range (n+1)).filter (fun k => k.minFac ^ a = k)).card := h2
      _ ≤ ∑ a ∈ Finset.Icc 2 (Nat.log 2 n), (Nat.sqrt n + 2) := h3
      _ = (Finset.Icc 2 (Nat.log 2 n)).card * (Nat.sqrt n + 2) := h4
      _ ≤ (Nat.log 2 n + 1) * (Nat.sqrt n + 2) := Nat.mul_le_mul_right _ h5
  have hsumS : ∑ k ∈ S, A k ≤ (S.card : ℝ) * Real.log (n:ℝ) := by
    have h1 : ∀ k ∈ S, A k = Real.log (k:ℝ) := by
      intro k hk
      rw [hS, Finset.mem_filter] at hk
      obtain ⟨-, hkne⟩ := hk
      rcases hAle k with h | h
      · exact absurd h hkne
      · exact h
    have h2 : ∀ k ∈ S, Real.log (k:ℝ) ≤ Real.log (n:ℝ) := by
      intro k hk
      rw [hS, Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨hkr, hkne⟩ := hk
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hkne hA0
      have hk1 : (1:ℝ) ≤ (k:ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
      have hkn : (k:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : k ≤ n)
      exact Real.log_le_log (by linarith) hkn
    calc ∑ k ∈ S, A k = ∑ k ∈ S, Real.log (k:ℝ) := Finset.sum_congr rfl h1
      _ ≤ ∑ k ∈ S, Real.log (n:ℝ) := Finset.sum_le_sum h2
      _ = (S.card : ℝ) * Real.log (n:ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcardR : (S.card : ℝ) ≤ ((Nat.log 2 n : ℝ) + 1) * ((Nat.sqrt n : ℝ) + 2) := by
    have h : (S.card : ℝ) ≤ (((Nat.log 2 n + 1) * (Nat.sqrt n + 2) : ℕ) : ℝ) := by
      exact_mod_cast hScard
    push_cast at h
    exact h
  have hLa : (Nat.log 2 n : ℝ) + 1 ≤ 3 * Real.log (n:ℝ) := by
    have hn0 : n ≠ 0 := by omega
    have h2pow : (2:ℝ) ^ (Nat.log 2 n) ≤ (n:ℝ) := by
      have h := Nat.pow_log_le_self 2 hn0
      exact_mod_cast h
    have hlog : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log (n:ℝ) := by
      have h := Real.log_le_log (by positivity : (0:ℝ) < 2 ^ Nat.log 2 n) h2pow
      rwa [Real.log_pow] at h
    have h2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have h3 : (Nat.log 2 n : ℝ) * (1/2) ≤ (Nat.log 2 n : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  have hSb : (Nat.sqrt n : ℝ) + 2 ≤ 2 * Real.sqrt (n:ℝ) := by
    have hnat : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n:ℝ) := by
      apply Real.le_sqrt_of_sq_le
      have h := Nat.sqrt_le' n
      have h' : ((Nat.sqrt n : ℕ) : ℝ) ^ 2 ≤ (n:ℝ) := by exact_mod_cast h
      exact h'
    have h4 : (2:ℝ) ≤ Real.sqrt (n:ℝ) := by
      apply Real.le_sqrt_of_sq_le
      have h : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn4
      nlinarith
    linarith
  have hLc : Real.log (((n+1:ℕ)):ℝ) ≤ 2 * Real.log (n:ℝ) := by
    have hcast : (((n+1:ℕ)):ℝ) = (n:ℝ) + 1 := by push_cast; ring
    have h1 : (n:ℝ) + 1 ≤ 2 * (n:ℝ) := by
      have h0 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      linarith
    have h2 : Real.log (((n+1:ℕ)):ℝ) ≤ Real.log (2*(n:ℝ)) := by
      rw [hcast]
      exact Real.log_le_log (by linarith) h1
    have h3 : Real.log (2*(n:ℝ)) = Real.log 2 + Real.log (n:ℝ) :=
      Real.log_mul (by norm_num) (ne_of_gt hnpos)
    have h4 : Real.log 2 ≤ Real.log (n:ℝ) := by
      apply Real.log_le_log (by norm_num)
      have h : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn4
      linarith
    linarith
  have hX : (S.card : ℝ) * Real.log (n:ℝ) * Real.log (((n+1:ℕ)):ℝ)
      ≤ 12 * Real.sqrt (n:ℝ) * (Real.log (n:ℝ))^3 := by
    have hstep1 : (S.card : ℝ) * Real.log (n:ℝ)
        ≤ (3 * Real.log (n:ℝ) * (2 * Real.sqrt (n:ℝ))) * Real.log (n:ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hlognn
      calc (S.card : ℝ) ≤ ((Nat.log 2 n : ℝ) + 1) * ((Nat.sqrt n : ℝ) + 2) := hcardR
        _ ≤ (3 * Real.log (n:ℝ)) * (2 * Real.sqrt (n:ℝ)) := by
            apply mul_le_mul hLa hSb (by positivity) (by positivity)
    have hstep2 : (S.card : ℝ) * Real.log (n:ℝ) * Real.log (((n+1:ℕ)):ℝ)
        ≤ (3 * Real.log (n:ℝ) * (2 * Real.sqrt (n:ℝ))) * Real.log (n:ℝ)
          * Real.log (((n+1:ℕ)):ℝ) :=
      mul_le_mul_of_nonneg_right hstep1 (le_of_lt hLpos)
    have hstep3 : (3 * Real.log (n:ℝ) * (2 * Real.sqrt (n:ℝ))) * Real.log (n:ℝ)
        * Real.log (((n+1:ℕ)):ℝ)
        ≤ (3 * Real.log (n:ℝ) * (2 * Real.sqrt (n:ℝ))) * Real.log (n:ℝ)
          * (2 * Real.log (n:ℝ)) := by
      apply mul_le_mul_of_nonneg_left hLc
      positivity
    refine le_trans hstep2 (le_trans hstep3 ?_)
    have heq : (3 * Real.log (n:ℝ) * (2 * Real.sqrt (n:ℝ))) * Real.log (n:ℝ)
        * (2 * Real.log (n:ℝ)) = 12 * Real.sqrt (n:ℝ) * (Real.log (n:ℝ))^3 := by ring
    rw [heq]
  have hsumX : (∑ k ∈ Finset.range (n+1), A k) * Real.log (((n+1:ℕ)):ℝ)
      ≤ 12 * Real.sqrt (n:ℝ) * (Real.log (n:ℝ))^3 := by
    rw [hsumA]
    calc (∑ k ∈ S, A k) * Real.log (((n+1:ℕ)):ℝ)
        ≤ ((S.card : ℝ) * Real.log (n:ℝ)) * Real.log (((n+1:ℕ)):ℝ) :=
          mul_le_mul_of_nonneg_right hsumS (le_of_lt hLpos)
      _ = (S.card : ℝ) * Real.log (n:ℝ) * Real.log (((n+1:ℕ)):ℝ) := by ring
      _ ≤ _ := hX
  have h1 : |∑ k ∈ Finset.range (n+1), A k * v k * Real.log (((n+1:ℕ)):ℝ)|
      ≤ ∑ k ∈ Finset.range (n+1), A k * Real.log (((n+1:ℕ)):ℝ) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
    intro k hk
    have hA' : 0 ≤ A k := hAnn k
    have hL' : 0 ≤ Real.log (((n+1:ℕ)):ℝ) := le_of_lt hLpos
    have hv' : |v k| ≤ 1 := hv k
    rw [abs_mul, abs_mul, abs_of_nonneg hA', abs_of_nonneg hL']
    nlinarith [mul_nonneg hA' hL', abs_nonneg (v k)]
  have h2 : ∑ k ∈ Finset.range (n+1), A k * Real.log (((n+1:ℕ)):ℝ)
      = (∑ k ∈ Finset.range (n+1), A k) * Real.log (((n+1:ℕ)):ℝ) := (Finset.sum_mul _ _ _).symm
  have hdiv1 : |∑ k ∈ Finset.range (n+1), A k * v k * Real.log (((n+1:ℕ)):ℝ)| / (n:ℝ)
      ≤ (12 * Real.sqrt (n:ℝ) * (Real.log (n:ℝ))^3) / (n:ℝ) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hnpos)
    calc |∑ k ∈ Finset.range (n+1), A k * v k * Real.log (((n+1:ℕ)):ℝ)|
        ≤ ∑ k ∈ Finset.range (n+1), A k * Real.log (((n+1:ℕ)):ℝ) := h1
      _ = (∑ k ∈ Finset.range (n+1), A k) * Real.log (((n+1:ℕ)):ℝ) := h2
      _ ≤ 12 * Real.sqrt (n:ℝ) * (Real.log (n:ℝ))^3 := hsumX
  have hdiv2 : (12 * Real.sqrt (n:ℝ) * (Real.log (n:ℝ))^3) / (n:ℝ)
      = 12 * ((Real.log (n:ℝ))^3 / Real.sqrt (n:ℝ)) := by
    have hsq : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = (n:ℝ) := Real.mul_self_sqrt (le_of_lt hnpos)
    have hsp : Real.sqrt (n:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnpos)
    rw [← hsq]
    field_simp
    rw [Real.sqrt_sq (Real.sqrt_nonneg (n:ℝ))]
  have hεn' : 12 * ((Real.log (n:ℝ))^3 / Real.sqrt (n:ℝ)) < ε := by
    rw [Real.sqrt_eq_rpow]
    exact hεn
  have hgoaleq : |(∑ k ∈ Finset.range (n+1), A k*v k*Real.log ((n+1:ℕ):ℝ))/(n:ℝ)|
      = |∑ k ∈ Finset.range (n+1), A k*v k*Real.log ((n+1:ℕ):ℝ)| / (n:ℝ) := by
    rw [abs_div, abs_of_pos hnpos]
  rw [hgoaleq]
  calc |∑ k ∈ Finset.range (n+1), A k*v k*Real.log ((n+1:ℕ):ℝ)| / (n:ℝ)
      ≤ (12 * Real.sqrt (n:ℝ) * (Real.log (n:ℝ))^3) / (n:ℝ) := hdiv1
    _ = 12 * ((Real.log (n:ℝ))^3 / Real.sqrt (n:ℝ)) := hdiv2
    _ < ε := hεn'