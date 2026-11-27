import Mathlib

private theorem finite_cosine_average_lipschitz
    (m : ℕ) (hm : 0 < m) (a : ℕ → ℝ)
    (ha : ∀ j, j < m → 0 ≤ a j)
    (A : ℝ) (haA : ∀ j, j < m → a j ≤ A)
    (x y : ℝ) :
    (∑ j ∈ Finset.range m, Real.cos (a j * x)) / (m : ℝ) ≤
      (∑ j ∈ Finset.range m, Real.cos (a j * y)) / (m : ℝ) + A * |x - y| := by
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hterm (j : ℕ) (hj : j < m) :
      Real.cos (a j * x) ≤ Real.cos (a j * y) + a j * |x - y| := by
    have hcos := Real.abs_cos_sub_cos_le (a j * x) (a j * y)
    have hangle : |a j * x - a j * y| = a j * |x - y| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (ha j hj)]
    have hdiff : Real.cos (a j * x) - Real.cos (a j * y) ≤
        |Real.cos (a j * x) - Real.cos (a j * y)| := le_abs_self _
    linarith
  have hsum :
      (∑ j ∈ Finset.range m, Real.cos (a j * x)) ≤
        (∑ j ∈ Finset.range m, Real.cos (a j * y)) + (m : ℝ) * (A * |x - y|) := by
    calc
      (∑ j ∈ Finset.range m, Real.cos (a j * x)) ≤
          ∑ j ∈ Finset.range m, (Real.cos (a j * y) + a j * |x - y|) := by
            exact Finset.sum_le_sum fun j hj => hterm j (Finset.mem_range.mp hj)
      _ = (∑ j ∈ Finset.range m, Real.cos (a j * y)) +
          |x - y| * (∑ j ∈ Finset.range m, a j) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            exact mul_comm _ _
      _ ≤ (∑ j ∈ Finset.range m, Real.cos (a j * y)) +
          |x - y| * ((m : ℝ) * A) := by
            have hsumA : (∑ j ∈ Finset.range m, a j) ≤ (m : ℝ) * A := by
              calc
                (∑ j ∈ Finset.range m, a j) ≤ ∑ _j ∈ Finset.range m, A := by
                  exact Finset.sum_le_sum fun j hj => haA j (Finset.mem_range.mp hj)
                _ = (m : ℝ) * A := by simp
            have hmul := mul_le_mul_of_nonneg_left hsumA (abs_nonneg (x - y))
            simpa [add_comm] using add_le_add_right hmul
              (∑ j ∈ Finset.range m, Real.cos (a j * y))
      _ = (∑ j ∈ Finset.range m, Real.cos (a j * y)) +
          (m : ℝ) * (A * |x - y|) := by ring
  calc
    (∑ j ∈ Finset.range m, Real.cos (a j * x)) / (m : ℝ) ≤
        ((∑ j ∈ Finset.range m, Real.cos (a j * y)) + (m : ℝ) * (A * |x - y|)) /
          (m : ℝ) := by
            exact div_le_div_of_nonneg_right hsum hmreal.le
    _ = (∑ j ∈ Finset.range m, Real.cos (a j * y)) / (m : ℝ) + A * |x - y| := by
      rw [add_div, mul_div_cancel_left₀ _ hmreal.ne']

private lemma log_fourth_small {n : ℕ} (hn : 2 ^ 256 ≤ n) :
    ((Nat.log 2 (n + 2) : ℕ) : ℝ) ^ 4 ≤ Real.sqrt (n : ℝ) / 128 := by
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hnreal : 0 ≤ (n : ℝ) := by positivity
  let r : ℝ := ((n + 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 16)
  have hrnonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  have hq :
      ((Nat.log 2 (n + 2) : ℕ) : ℝ) ≤ 32 * r := by
    have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by
      have h := Real.log_two_gt_d9
      norm_num at h ⊢
      linarith
    have hmone : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ n + 2 by omega)
    have hlog_nonneg : 0 ≤ Real.log ((n + 2 : ℕ) : ℝ) := Real.log_nonneg hmone
    have hlogb : Real.logb 2 ((n + 2 : ℕ) : ℝ) ≤
        2 * Real.log ((n + 2 : ℕ) : ℝ) := by
      rw [Real.logb]
      apply (div_le_iff₀ (lt_trans (by norm_num) hlog2)).2
      nlinarith
    have hln := Real.log_natCast_le_rpow_div (n + 2) (ε := (1 : ℝ) / 16) (by norm_num)
    calc
      ((Nat.log 2 (n + 2) : ℕ) : ℝ) ≤
          Real.logb 2 ((n + 2 : ℕ) : ℝ) := by
            exact_mod_cast Real.natLog_le_logb (n + 2) 2
      _ ≤ 2 * Real.log ((n + 2 : ℕ) : ℝ) := hlogb
      _ ≤ 2 * (16 * ((n + 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 16)) := by
        apply mul_le_mul_of_nonneg_left
        · convert hln using 1 <;> norm_num <;> ring
        · norm_num
      _ = 32 * r := by
        norm_num [r, Nat.cast_add, Nat.cast_ofNat] <;> ring
  have hq8 :
      ((Nat.log 2 (n + 2) : ℕ) : ℝ) ^ 8 ≤ (32 * r) ^ 8 :=
    pow_le_pow_left₀ (by positivity) hq 8
  have hr8 : r ^ 8 = Real.sqrt ((n + 2 : ℕ) : ℝ) := by
    dsimp [r]
    calc
      (((n + 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 16)) ^ 8 =
          ((n + 2 : ℕ) : ℝ) ^ (((1 : ℝ) / 16) * 8) := by
            exact (Real.rpow_mul_natCast
              (show 0 ≤ ((n + 2 : ℕ) : ℝ) by positivity) ((1 : ℝ) / 16) 8).symm
      _ = Real.sqrt ((n + 2 : ℕ) : ℝ) := by
        norm_num [Real.sqrt_eq_rpow]
  have hsqrt : Real.sqrt ((n + 2 : ℕ) : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    have hsq1 := Real.sq_sqrt (show 0 ≤ ((n + 2 : ℕ) : ℝ) by positivity)
    have hsq2 := Real.sq_sqrt hnreal
    rw [hsq1, mul_pow, hsq2]
    norm_num
    exact_mod_cast (show n + 2 ≤ 4 * n by omega)
  have hq8sqrt :
      ((Nat.log 2 (n + 2) : ℕ) : ℝ) ^ 8 ≤
        (2 : ℝ) ^ 41 * Real.sqrt (n : ℝ) := by
    calc
      ((Nat.log 2 (n + 2) : ℕ) : ℝ) ^ 8 ≤ (32 * r) ^ 8 := hq8
      _ = (32 : ℝ) ^ 8 * Real.sqrt ((n + 2 : ℕ) : ℝ) := by
        rw [mul_pow, hr8]
      _ ≤ (2 : ℝ) ^ 41 * Real.sqrt (n : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hsqrt
          (show 0 ≤ (2 : ℝ) ^ 40 by positivity)
        convert hmul using 1 <;> norm_num <;> ring
  have hsqrtlarge : (2 : ℝ) ^ 128 ≤ Real.sqrt (n : ℝ) := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    have hncast : ((2 ^ 256 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    calc
      ((2 : ℝ) ^ 128) ^ 2 = ((2 ^ 256 : ℕ) : ℝ) := by
        rw [← pow_mul]
        norm_num [Nat.cast_pow]
      _ ≤ (n : ℝ) := hncast
      _ = (Real.sqrt (n : ℝ)) ^ 2 := (Real.sq_sqrt hnreal).symm
  have hscaled :
      (2 : ℝ) ^ 55 * Real.sqrt (n : ℝ) ≤
        (Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ) := by
    apply mul_le_mul_of_nonneg_right
    · exact le_trans (pow_le_pow_right₀ (by norm_num) (by norm_num)) hsqrtlarge
    · exact Real.sqrt_nonneg _
  have hq4sq :
      (((Nat.log 2 (n + 2) : ℕ) : ℝ) ^ 4) ^ 2 ≤
        (Real.sqrt (n : ℝ) / 128) ^ 2 := by
    calc
      (((Nat.log 2 (n + 2) : ℕ) : ℝ) ^ 4) ^ 2 =
          ((Nat.log 2 (n + 2) : ℕ) : ℝ) ^ 8 := by ring
      _ ≤ (2 : ℝ) ^ 41 * Real.sqrt (n : ℝ) := hq8sqrt
      _ ≤ (Real.sqrt (n : ℝ) / 128) ^ 2 := by
        rw [div_pow]
        apply (le_div_iff₀ (by positivity : 0 < (128 : ℝ) ^ 2)).2
        rw [show (128 : ℝ) ^ 2 = (2 : ℝ) ^ 14 by norm_num]
        calc
          ((2 : ℝ) ^ 41 * Real.sqrt (n : ℝ)) * (2 : ℝ) ^ 14 =
              ((2 : ℝ) ^ 41 * (2 : ℝ) ^ 14) * Real.sqrt (n : ℝ) := by ring
          _ = (2 : ℝ) ^ (41 + 14) * Real.sqrt (n : ℝ) := by
                rw [← pow_add]
          _ = (2 : ℝ) ^ 55 * Real.sqrt (n : ℝ) := by norm_num
          _ ≤ (Real.sqrt (n : ℝ)) ^ 2 := by simpa [pow_two] using hscaled
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hq4sq

private lemma top_frequency_small {n : ℕ} (hn : 2 ^ 256 ≤ n) :
    (2 : ℝ) ^ (max 1 (Nat.log 2 n / 2)) ≤ 2 * Real.sqrt (n : ℝ) := by
  let m : ℕ := max 1 (Nat.log 2 n / 2)
  let k : ℕ := Nat.log 2 n
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hm : 2 * m ≤ k + 2 := by
    dsimp [m, k]
    omega
  have hpow : 2 ^ (2 * m) ≤ 4 * n := by
    calc
      2 ^ (2 * m) ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) hm
      _ = 4 * 2 ^ k := by ring
      _ ≤ 4 * n := by
        exact Nat.mul_le_mul_left 4 (Nat.pow_log_le_self 2 (Nat.ne_of_gt hnpos))
  have hsquare : ((2 : ℝ) ^ m) ^ 2 ≤ (2 * Real.sqrt (n : ℝ)) ^ 2 := by
    have hpowcast : ((2 ^ (2 * m) : ℕ) : ℝ) ≤ ((4 * n : ℕ) : ℝ) := by
      exact_mod_cast hpow
    have hpowreal : ((2 : ℝ) ^ m) ^ 2 ≤ 4 * (n : ℝ) := by
      calc
        ((2 : ℝ) ^ m) ^ 2 = ((2 ^ (2 * m) : ℕ) : ℝ) := by
          norm_num [Nat.cast_pow, ← pow_mul, mul_comm]
        _ ≤ 4 * (n : ℝ) := by exact_mod_cast hpowcast
    nlinarith [Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)]
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsquare

theorem Conjectures.Goldbach.PacketRationalCenterStability :
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); ∃ N : ℕ, ∀ n ≥ N, ∀ x y : ℝ, |x-y| ≤ (Q n:ℝ)^2/(n:ℝ) → (1:ℝ)/2 < K n x → (1:ℝ)/3 < K n y := by
  dsimp only
  refine ⟨2 ^ 256, ?_⟩
  intro n hn x y hxy hKx
  let m : ℕ := max 1 (Nat.log 2 n / 2)
  let q : ℕ := Nat.log 2 (n + 2)
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hmpos : 0 < m := by
    dsimp [m]
    omega
  have hq4 : (q : ℝ) ^ 4 ≤ Real.sqrt (n : ℝ) / 128 := by
    exact log_fourth_small hn
  have htop : (2 : ℝ) ^ m ≤ 2 * Real.sqrt (n : ℝ) := by
    exact top_frequency_small hn
  have hterm_top (j : ℕ) (hj : j < m) :
      2 * Real.pi * (2 : ℝ) ^ (j + 1) ≤ 2 * Real.pi * (2 : ℝ) ^ m := by
    apply mul_le_mul_of_nonneg_left
    · exact pow_le_pow_right₀ (by norm_num) (by omega)
    · positivity
  have hKlip :
      (∑ j ∈ Finset.range m, Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * x)) /
          (m : ℝ) ≤
        (∑ j ∈ Finset.range m, Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * y)) /
          (m : ℝ) + (2 * Real.pi * (2 : ℝ) ^ m) * |x - y| := by
    exact finite_cosine_average_lipschitz m hmpos
      (fun j => 2 * Real.pi * (2 : ℝ) ^ (j + 1))
      (by intro j hj; positivity) (2 * Real.pi * (2 : ℝ) ^ m) hterm_top x y
  have hgap : |x - y| ≤ (q : ℝ) ^ 4 / (n : ℝ) := by
    dsimp [q] at *
    push_cast at hxy
    convert hxy using 1
    ring
  have hfreq : 2 * Real.pi * (2 : ℝ) ^ m ≤ 16 * Real.sqrt (n : ℝ) := by
    calc
      2 * Real.pi * (2 : ℝ) ^ m ≤ 2 * Real.pi * (2 * Real.sqrt (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_left htop (by positivity)
      _ ≤ 2 * 4 * (2 * Real.sqrt (n : ℝ)) := by
        gcongr
        exact Real.pi_le_four
      _ = 16 * Real.sqrt (n : ℝ) := by ring
  have hvariation :
      (2 * Real.pi * (2 : ℝ) ^ m) * |x - y| ≤ (1 : ℝ) / 8 := by
    calc
      (2 * Real.pi * (2 : ℝ) ^ m) * |x - y| ≤
          (2 * Real.pi * (2 : ℝ) ^ m) * ((q : ℝ) ^ 4 / (n : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hgap (by positivity)
      _ ≤ (16 * Real.sqrt (n : ℝ)) *
          ((Real.sqrt (n : ℝ) / 128) / (n : ℝ)) := by
        gcongr
      _ = (1 : ℝ) / 8 := by
        have hsqrt_sq := Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)
        field_simp
        nlinarith
  dsimp [m] at hKlip ⊢
  dsimp [q] at hgap
  linarith
