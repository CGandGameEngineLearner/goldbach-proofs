import Mathlib

theorem PEqualNP.Outside.L_goldbach_small_small_saving :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0;
    let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I);
    let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n + 1)) (fun k => (w k : ℂ) * E ((k : ℝ) * t));
    let Q := fun n : ℕ => (Nat.log 2 (n + 2)) ^ 2;
    let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))};
    let low := fun (n k : ℕ) => if k ^ 3 ≤ n then w k else 0;
    let high := fun (n k : ℕ) => w k - low n k;
    let I := fun (n : ℕ) (a b : ℕ → ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u * S n b u * E (-(n : ℝ) * u)) t) (0 : ℝ) 1 MeasureTheory.volume;
    ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n ≥ N, ‖I n (low n) (low n)‖ ≤ e * (n : ℝ) := by
  intro w E S _Q arcs low _high I e he
  have hnorm_E : ∀ x : ℝ, ‖E x‖ = 1 := fun x => Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
  have hcap : ∀ (n : ℕ) (t : ℝ), 2 ≤ n → ‖S n (low n) t‖ ≤ ((n : ℝ) ^ (1 / 3 : ℝ) + 1) * Real.log (n : ℝ) := by
    intro n t hn
    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have hlow_nonneg : ∀ k : ℕ, 0 ≤ low n k := by
      intro k
      dsimp only [low, w]
      split_ifs with h1 hp
      · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
      · exact le_rfl
      · exact le_rfl
    have hlow_le_log : ∀ k ∈ Finset.range (n + 1), low n k ≤ Real.log (n : ℝ) := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      dsimp only [low, w]
      split_ifs with h1 hp
      · exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hkn)
      · exact hlog_nonneg
      · exact hlog_nonneg
    have hstep1 : ‖S n (low n) t‖ ≤ ∑ k ∈ Finset.range (n + 1), low n k := by
      dsimp only [S]
      calc
        ‖∑ k ∈ Finset.range (n + 1), (low n k : ℂ) * E ((k : ℝ) * t)‖
          ≤ ∑ k ∈ Finset.range (n + 1), ‖(low n k : ℂ) * E ((k : ℝ) * t)‖ := norm_sum_le _ _
        _ = ∑ k ∈ Finset.range (n + 1), low n k := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hlow_nonneg k), hnorm_E, mul_one]
    set s : Finset ℕ := (Finset.range (n + 1)).filter (fun k => k ^ 3 ≤ n)
    have hstep2 : ∑ k ∈ Finset.range (n + 1), low n k = ∑ k ∈ s, low n k := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun k hk hks => ?_
      have hnot : ¬ (k ^ 3 ≤ n) := fun hle => hks (Finset.mem_filter.mpr ⟨hk, hle⟩)
      simp [low, hnot]
    set m : ℕ := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
    have hs_sub : s ⊆ Finset.range (m + 1) := by
      intro k hk
      have hk3 : k ^ 3 ≤ n := (Finset.mem_filter.mp hk).2
      have hk3_real : ((k : ℝ) ^ (3 : ℝ)) ≤ (n : ℝ) := by
        have hcast : ((k ^ 3 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk3
        simpa [Real.rpow_natCast] using hcast
      have hk_le_rpow : (k : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
        have hpow := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg k) (3 : ℝ)) hk3_real (by norm_num : (0 : ℝ) ≤ 1 / 3)
        rw [← Real.rpow_mul (Nat.cast_nonneg k)] at hpow
        have h3 : (3 : ℝ) * (1 / 3 : ℝ) = 1 := by norm_num
        rw [h3, Real.rpow_one] at hpow
        exact hpow
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hk_le_rpow))
    have hcard : (s.card : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) + 1 := by
      have h1 : s.card ≤ m + 1 := by simpa [Finset.card_range] using Finset.card_le_card hs_sub
      have h1r : (s.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast h1
      have h2 : (m : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Nat.floor_le (Real.rpow_nonneg hn_nonneg (1 / 3 : ℝ))
      linarith
    calc
      ‖S n (low n) t‖ ≤ ∑ k ∈ Finset.range (n + 1), low n k := hstep1
      _ = ∑ k ∈ s, low n k := hstep2
      _ ≤ ∑ _k ∈ s, Real.log (n : ℝ) := Finset.sum_le_sum fun k hk => hlow_le_log k (Finset.mem_filter.mp hk).1
      _ = (s.card : ℝ) * Real.log (n : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((n : ℝ) ^ (1 / 3 : ℝ) + 1) * Real.log (n : ℝ) := mul_le_mul_of_nonneg_right hcard hlog_nonneg
  refine ⟨Nat.ceil ((576 / e) ^ (6 : ℕ)) + 2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn_ge1
  have hlog_bound : Real.log (n : ℝ) ≤ 12 * (n : ℝ) ^ (1 / 12 : ℝ) := by
    have hpos_p : 0 < (n : ℝ) ^ (1 / 12 : ℝ) := Real.rpow_pos_of_pos hn_pos _
    have h1 := Real.log_le_sub_one_of_pos hpos_p
    rw [Real.log_rpow hn_pos] at h1
    linarith
  have h1_le_rpow : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow hn_ge1 (by norm_num)
  have hM : ((n : ℝ) ^ (1 / 3 : ℝ) + 1) * Real.log (n : ℝ) ≤ 24 * (n : ℝ) ^ (5 / 12 : ℝ) := by
    have h1 : (n : ℝ) ^ (1 / 3 : ℝ) + 1 ≤ 2 * (n : ℝ) ^ (1 / 3 : ℝ) := by linarith
    calc
      ((n : ℝ) ^ (1 / 3 : ℝ) + 1) * Real.log (n : ℝ)
        ≤ (2 * (n : ℝ) ^ (1 / 3 : ℝ)) * (12 * (n : ℝ) ^ (1 / 12 : ℝ)) :=
          mul_le_mul h1 hlog_bound hlog_nonneg (by positivity)
      _ = 24 * ((n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ)) := by ring
      _ = 24 * (n : ℝ) ^ (5 / 12 : ℝ) := by
          rw [← Real.rpow_add hn_pos]
          norm_num
  have hsq : (((n : ℝ) ^ (1 / 3 : ℝ) + 1) * Real.log (n : ℝ)) ^ 2 ≤ 576 * (n : ℝ) ^ (5 / 6 : ℝ) := by
    have h0 : 0 ≤ ((n : ℝ) ^ (1 / 3 : ℝ) + 1) * Real.log (n : ℝ) := by positivity
    calc
      (((n : ℝ) ^ (1 / 3 : ℝ) + 1) * Real.log (n : ℝ)) ^ 2
        ≤ (24 * (n : ℝ) ^ (5 / 12 : ℝ)) ^ 2 := pow_le_pow_left₀ h0 hM 2
      _ = 576 * ((n : ℝ) ^ (5 / 12 : ℝ)) ^ 2 := by ring
      _ = 576 * (n : ℝ) ^ (5 / 6 : ℝ) := by
          rw [← Real.rpow_natCast ((n : ℝ) ^ (5 / 12 : ℝ)) 2, ← Real.rpow_mul hn_pos.le]
          norm_num
  have hpt : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖(arcs n)ᶜ.indicator (fun u => S n (low n) u * S n (low n) u * E (-(n : ℝ) * u)) t‖ ≤
        576 * (n : ℝ) ^ (5 / 6 : ℝ) := by
    intro t _
    have hnonneg : 0 ≤ 576 * (n : ℝ) ^ (5 / 6 : ℝ) := by positivity
    by_cases ht : t ∈ (arcs n)ᶜ
    · rw [Set.indicator_of_mem ht, norm_mul, norm_mul, hnorm_E, mul_one, ← sq]
      exact (pow_le_pow_left₀ (norm_nonneg _) (hcap n t hn2) 2).trans hsq
    · rw [Set.indicator_of_notMem ht, norm_zero]
      exact hnonneg
  have hint_le : ‖I n (low n) (low n)‖ ≤ 576 * (n : ℝ) ^ (5 / 6 : ℝ) := by
    dsimp only [I]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    simpa using h
  have htail : 576 * (n : ℝ) ^ (5 / 6 : ℝ) ≤ e * (n : ℝ) := by
    have hn_big : (576 / e) ^ (6 : ℕ) ≤ (n : ℝ) := by
      have hceil : (576 / e) ^ (6 : ℕ) ≤ (Nat.ceil ((576 / e) ^ (6 : ℕ)) : ℝ) := Nat.le_ceil _
      have hle : (Nat.ceil ((576 / e) ^ (6 : ℕ)) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : Nat.ceil ((576 / e) ^ (6 : ℕ)) ≤ n)
      exact hceil.trans hle
    have hroot : 576 / e ≤ (n : ℝ) ^ (1 / 6 : ℝ) := by
      have hnonneg : 0 ≤ (576 / e : ℝ) := by positivity
      have hpow := Real.rpow_le_rpow (pow_nonneg hnonneg 6) hn_big (by norm_num : (0 : ℝ) ≤ 1 / 6)
      rw [← Real.rpow_natCast (576 / e) 6, ← Real.rpow_mul hnonneg] at hpow
      have h6 : ((6 : ℕ) : ℝ) * (1 / 6 : ℝ) = 1 := by norm_num
      rw [h6, Real.rpow_one] at hpow
      exact hpow
    have h576 : 576 ≤ e * (n : ℝ) ^ (1 / 6 : ℝ) := by
      rwa [div_le_iff₀ he, mul_comm] at hroot
    calc
      576 * (n : ℝ) ^ (5 / 6 : ℝ)
        ≤ (e * (n : ℝ) ^ (1 / 6 : ℝ)) * (n : ℝ) ^ (5 / 6 : ℝ) :=
          mul_le_mul_of_nonneg_right h576 (by positivity)
      _ = e * ((n : ℝ) ^ (1 / 6 : ℝ) * (n : ℝ) ^ (5 / 6 : ℝ)) := by ring
      _ = e * (n : ℝ) := by
          rw [← Real.rpow_add hn_pos]
          norm_num
  exact hint_le.trans htail
