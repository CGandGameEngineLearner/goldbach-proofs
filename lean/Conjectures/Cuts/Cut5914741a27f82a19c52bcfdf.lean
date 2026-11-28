import Mathlib

-- child 1 zh: 一致解析输入：对充分大的 X，低指数带中每个 a 与高指数带中每个 b，在二进移位 2^a、2^b 处 [X,2X) 内同时使 m-2^a 与 m-2^b 为素数的 m 至少有 c·X/(log X)² 个。
-- child 1 en: Uniform analytic input: for all large X, every low-band exponent a and high-band exponent b have at least c·X/(log X)² targets m in [X,2X) with both m-2^a and m-2^b prime.
-- child 2 zh: 有限重数计数：对任意 X 与带参数 L，乘积 J(1,L/2)·J(L/2+1,L) 在 [X,2X) 上的和等于对所有指数对 (a,b) 的同时素数计数之和。
-- child 2 en: Finite multiplicity count: for every X and band parameter L, the sum over [X,2X) of J(1,L/2)·J(L/2+1,L) equals the sum over all exponent pairs (a,b) of the simultaneous prime counts.

/-- Reduce the cross-band mixed prime-translate mass to a uniform per-shift prime-pair floor
and a finite double-counting identity. The band sizes grow like `(log X)²`, which absorbs the
`log²X` denominator. -/
theorem Conjectures.Cuts.Cut5914741a27f82a19c52bcfdf
    (h₁ : ∃ c : ℝ, 0 < c ∧ ∃ T : ℕ, ∀ X ≥ T, ∀ a ∈ Finset.Icc 1 (Nat.log 2 X / 2 / 2),
      ∀ b ∈ Finset.Icc (Nat.log 2 X / 2 / 2 + 1) (Nat.log 2 X / 2),
        c * (X:ℝ) / (Real.log (X:ℝ))^2 ≤
          (((Finset.Ico X (2*X)).filter (fun m => Nat.Prime (m - 2^a) ∧ Nat.Prime (m - 2^b))).card : ℝ))
    (h₂ : ∀ (X L : ℕ), (∑ m ∈ Finset.Ico X (2*X),
        (((Finset.Icc 1 (L/2)).filter (fun e => Nat.Prime (m - 2^e))).card) *
        (((Finset.Icc (L/2+1) L).filter (fun e => Nat.Prime (m - 2^e))).card)) =
      ∑ a ∈ Finset.Icc 1 (L/2), ∑ b ∈ Finset.Icc (L/2+1) L,
        ((Finset.Ico X (2*X)).filter (fun m => Nat.Prime (m - 2^a) ∧ Nat.Prime (m - 2^b))).card)
    : (let J := fun (a b m : ℕ) => ((Finset.Icc a b).filter (fun e => Nat.Prime (m-2^e))).card; ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, let L := Nat.log 2 X / 2; c*(X:ℝ) ≤ ∑ m ∈ Finset.Ico X (2*X), (J 1 (L/2) m:ℝ)*(J (L/2+1) L m:ℝ)) := by
  classical
  intro J
  obtain ⟨c₁, hc₁, T, hT⟩ := h₁
  refine ⟨c₁ / (64 * (Real.log 2)^2), by positivity, max T 256, ?_⟩
  intro X hX L
  dsimp only [J, L]
  have hX256 : 256 ≤ X := (le_max_right _ _).trans hX
  have hX0 : (0 : ℝ) < (X:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hX256
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog256 : Real.log (256:ℝ) = 8 * Real.log 2 := by
    rw [show (256:ℝ) = (2:ℝ)^8 by norm_num, Real.log_pow]
    norm_num
  have hlogX : 8 * Real.log 2 ≤ Real.log (X:ℝ) := by
    have := Real.log_le_log (x := (256:ℝ)) (y := (X:ℝ)) (by norm_num) (by exact_mod_cast hX256)
    rw [hlog256] at this
    exact this
  -- name the binary logarithm
  obtain ⟨k, hk⟩ : ∃ k, Nat.log 2 X = k := ⟨_, rfl⟩
  rw [hk]
  set A := Finset.Icc 1 (k / 2 / 2) with hA
  set B := Finset.Icc (k / 2 / 2 + 1) (k / 2) with hB
  -- 4 ≤ k
  have hk4 : 4 ≤ k := by
    by_contra hcon
    have h4 : k < 4 := by omega
    have hlt : Nat.log 2 X < 4 := by rw [hk]; exact h4
    have hiff : Nat.log 2 X < 4 ↔ X < 2 ^ 4 := Nat.log_lt_iff_lt_pow (by norm_num) (by omega)
    have hlt2 : X < 2 ^ 4 := hiff.mp hlt
    have h2 : (2 ^ 4 : ℕ) = 16 := by norm_num
    rw [h2] at hlt2
    omega
  -- cardinalities of the bands
  have hcardA : A.card = k / 2 / 2 := by
    rw [hA, Nat.card_Icc]
    have : 1 ≤ k / 2 / 2 := by omega
    omega
  have hcardB : B.card = k / 2 - k / 2 / 2 := by
    rw [hB, Nat.card_Icc]
    have : k / 2 / 2 + 1 ≤ k / 2 + 1 := by omega
    omega
  -- Real.log X < (k+1) log 2
  have hkl : Real.log (X:ℝ) < ((k:ℕ):ℝ) * Real.log 2 + Real.log 2 := by
    have hlt : Nat.log 2 X < k + 1 := by rw [hk]; exact Nat.lt_succ_self k
    have hiff : Nat.log 2 X < k + 1 ↔ X < 2 ^ (k + 1) := Nat.log_lt_iff_lt_pow (by norm_num) (by omega)
    have h1 : X < 2 ^ (k + 1) := hiff.mp hlt
    have h2 : ((X:ℕ) : ℝ) < (((2 ^ (k + 1) : ℕ) : ℝ)) := by exact_mod_cast h1
    have h3 : Real.log (X:ℝ) < Real.log (((2 ^ (k + 1) : ℕ) : ℝ)) := Real.log_lt_log hX0 h2
    rw [Nat.cast_pow, Real.log_pow] at h3
    push_cast at h3
    linarith
  -- divisibility bookkeeping in ℝ
  have hs1 : ((k:ℕ):ℝ) + 1 ≤ 2 * ((k / 2 : ℕ) : ℝ) + 2 := by
    have hd := Nat.div_add_mod k 2
    have hm : k % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have : k + 1 ≤ 2 * (k / 2) + 2 := by omega
    exact_mod_cast this
  have hs2 : ((k / 2 : ℕ) : ℝ) + 1 ≤ 2 * ((k / 2 / 2 : ℕ) : ℝ) + 2 := by
    have hd := Nat.div_add_mod (k / 2) 2
    have hm : k / 2 % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have : k / 2 + 1 ≤ 2 * (k / 2 / 2) + 2 := by omega
    exact_mod_cast this
  have hs1' : Real.log (X:ℝ) < (2 * ((k / 2 : ℕ) : ℝ) + 2) * Real.log 2 := by
    have := mul_le_mul_of_nonneg_right hs1 hlog2.le
    linarith
  have hs2' : (2 * ((k / 2 : ℕ) : ℝ) + 2) * Real.log 2 ≤ (4 * ((k / 2 / 2 : ℕ) : ℝ) + 4) * Real.log 2 := by
    apply mul_le_mul_of_nonneg_right _ hlog2.le
    linarith
  have hs3 : Real.log (X:ℝ) - 4 * Real.log 2 < 4 * Real.log 2 * ((k / 2 / 2 : ℕ) : ℝ) := by
    nlinarith [hs1', hs2']
  have hs4 : 4 * Real.log 2 ≤ Real.log (X:ℝ) / 2 := by linarith
  have hs5 : Real.log (X:ℝ) / 2 < 4 * Real.log 2 * ((k / 2 / 2 : ℕ) : ℝ) := by linarith
  have hkey : Real.log (X:ℝ) < 8 * Real.log 2 * ((k / 2 / 2 : ℕ) : ℝ) := by nlinarith [hs5]
  have hcardA' : Real.log (X:ℝ) / (8 * Real.log 2) ≤ ((A.card : ℕ) : ℝ) := by
    rw [hcardA]
    apply (div_le_iff₀ (by linarith)).mpr
    nlinarith [hkey.le]
  have hcardB' : Real.log (X:ℝ) / (8 * Real.log 2) ≤ ((B.card : ℕ) : ℝ) := by
    have hBA : A.card ≤ B.card := by
      rw [hcardA, hcardB]
      omega
    exact hcardA'.trans (by exact_mod_cast hBA)
  have hcard : (Real.log (X:ℝ))^2 / (64 * (Real.log 2)^2) ≤ (((A.card * B.card : ℕ) : ℝ)) := by
    have h := mul_le_mul hcardA' hcardB' (by positivity) (by positivity)
    have heq : Real.log (X:ℝ) / (8 * Real.log 2) * (Real.log (X:ℝ) / (8 * Real.log 2))
        = (Real.log (X:ℝ))^2 / (64 * (Real.log 2)^2) := by
      field_simp
      ring
    rw [heq] at h
    simpa [Nat.cast_mul] using h
  -- the finite identity
  have hcast := h₂ X (k / 2)
  have hcast' : (∑ m ∈ Finset.Ico X (2*X), (((Finset.Icc 1 (k / 2 / 2)).filter (fun e => Nat.Prime (m - 2^e))).card : ℝ) * (((Finset.Icc (k / 2 / 2 + 1) (k / 2)).filter (fun e => Nat.Prime (m - 2^e))).card : ℝ)) = ∑ a ∈ Finset.Icc 1 (k / 2 / 2), ∑ b ∈ Finset.Icc (k / 2 / 2 + 1) (k / 2), (((Finset.Ico X (2*X)).filter (fun m => Nat.Prime (m - 2^a) ∧ Nat.Prime (m - 2^b))).card : ℝ) := by
    simp only [← Nat.cast_mul, ← Nat.cast_sum]
    rw [hcast]
  rw [hA, hB, hcast']
  -- sum bound
  have hsum : c₁ * (X:ℝ) / (Real.log (X:ℝ))^2 * (((A.card * B.card : ℕ) : ℝ)) ≤
      ∑ a ∈ A, ∑ b ∈ B, (((Finset.Ico X (2*X)).filter (fun m => Nat.Prime (m - 2^a) ∧ Nat.Prime (m - 2^b))).card : ℝ) := by
    have step1 : (∑ a ∈ A, ∑ b ∈ B, (c₁ * (X:ℝ) / (Real.log (X:ℝ))^2)) ≤
        ∑ a ∈ A, ∑ b ∈ B, (((Finset.Ico X (2*X)).filter (fun m => Nat.Prime (m - 2^a) ∧ Nat.Prime (m - 2^b))).card : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      have hA' : a ∈ Finset.Icc 1 (Nat.log 2 X / 2 / 2) := by
        rw [hk]; exact ha
      have hB' : b ∈ Finset.Icc (Nat.log 2 X / 2 / 2 + 1) (Nat.log 2 X / 2) := by
        rw [hk]; exact hb
      exact hT X ((le_max_left T 256).trans hX) a hA' b hB'
    have step2 : (∑ a ∈ A, ∑ b ∈ B, (c₁ * (X:ℝ) / (Real.log (X:ℝ))^2))
        = (((A.card * B.card : ℕ) : ℝ)) * (c₁ * (X:ℝ) / (Real.log (X:ℝ))^2) := by
      simp [Finset.sum_const, mul_assoc]
    rw [step2] at step1
    nlinarith [step1]
  -- final
  have hfin : c₁ * (X:ℝ) / (Real.log (X:ℝ))^2 * ((Real.log (X:ℝ))^2 / (64 * (Real.log 2)^2))
      = c₁ / (64 * (Real.log 2)^2) * (X:ℝ) := by
    have hlogX0 : Real.log (X:ℝ) ≠ 0 := by nlinarith [hlog2, hlogX]
    have hne : (Real.log (X:ℝ))^2 ≠ 0 := pow_ne_zero _ hlogX0
    have hne2 : 64 * (Real.log 2)^2 ≠ 0 := by positivity
    field_simp
  calc c₁ / (64 * (Real.log 2)^2) * (X:ℝ)
      = c₁ * (X:ℝ) / (Real.log (X:ℝ))^2 * ((Real.log (X:ℝ))^2 / (64 * (Real.log 2)^2)) := hfin.symm
    _ ≤ c₁ * (X:ℝ) / (Real.log (X:ℝ))^2 * (((A.card * B.card : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hcard (by positivity)
    _ ≤ _ := hsum
