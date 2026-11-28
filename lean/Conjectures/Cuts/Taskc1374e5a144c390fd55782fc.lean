import Mathlib

/-!
# `τ(n) ≪_ε n^ε`

Proof outline (`η = ε/2`, threshold `K = ⌈2^(1/η)⌉₊ + 1`):

* `Nat.card_divisors` writes `τ(n) = ∏ p ∈ n.primeFactors, (e_p + 1)` and
  `Nat.prod_primeFactors_pow_factorization` writes `n = ∏ p, p ^ e_p`.
* Primes are split at `K` with `Finset.prod_filter_mul_prod_filter_not`.
  * large primes `p ≥ K ≥ 2^(1/η)`: `e + 1 ≤ 2^e ≤ p^(η·e)`, so the subproduct is
    `≤ (∏ p^(e_p))^η = n^η` (`Real.finsetProd_rpow`).
  * small primes `p < K`: there are at most `K` of them (`S1 ⊆ range K`) and each
    satisfies `e_p + 1 ≤ log n / log 2 + 1` (from `p^(e_p) ∣ n`, `Real.log_pow`).
* Analysis: `(log n / log 2 + 1)^K ≤ ((2/log 2)·log n)^K` and
  `(log n)^K ≤ (K/η)^K · n^η` by `Real.log_le_rpow_div` with exponent `s = η/K`.
  Multiplying the two `n^η` factors and using `η + η = ε` gives the claim.
-/

/-- For every `ε > 0` there is `C > 0` with `τ(n) ≤ C n^ε` for all `n ≥ 1`,
where `τ(n) = n.divisors.card` is the number of divisors of `n`. -/
theorem card_divisors_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  -- ## Parameters
  set η : ℝ := ε / 2 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  set K : ℕ := ⌈(2 : ℝ) ^ (1 / η)⌉₊ + 1 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; omega
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

  -- ## Every prime `p ≥ K` satisfies `2 ≤ p ^ η`
  have hlarge : ∀ p : ℕ, p.Prime → K ≤ p → (2 : ℝ) ≤ (p : ℝ) ^ η := by
    intro p _ hpK
    have hceil : (2 : ℝ) ^ (1 / η) ≤ ((⌈(2 : ℝ) ^ (1 / η)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hKgt : ((⌈(2 : ℝ) ^ (1 / η)⌉₊ : ℕ) : ℝ) < (K : ℝ) := by
      rw [hKdef]; push_cast; linarith
    have hlt : (2 : ℝ) ^ (1 / η) < (p : ℝ) := by
      have : (K : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpK
      linarith
    calc (2 : ℝ) = (2 : ℝ) ^ (1 / η * η) := by
            rw [one_div_mul_cancel hη.ne', Real.rpow_one]
      _ = ((2 : ℝ) ^ (1 / η)) ^ η := Real.rpow_mul (by norm_num) _ _
      _ ≤ (p : ℝ) ^ η := Real.rpow_le_rpow (by positivity) hlt.le hη.le

  -- ## Main combinatorial bound
  have key : ∀ n : ℕ, 1 ≤ n →
      (n.divisors.card : ℝ) ≤ (Real.log n / Real.log 2 + 1) ^ K * (n : ℝ) ^ η := by
    intro n hn
    have hn0 : n ≠ 0 := by omega
    have hlog_nonneg : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    -- divisors counted by exponents
    have hcard : (n.divisors.card : ℝ)
        = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      rw [Nat.card_divisors hn0, Nat.cast_prod]
      simp only [Nat.cast_add, Nat.cast_one]
    set S1 := n.primeFactors.filter (fun p => p < K) with hS1
    set S2 := n.primeFactors.filter (fun p => ¬ p < K) with hS2
    have hsplit : (∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1))
        = (∏ p ∈ S1, ((n.factorization p : ℝ) + 1))
          * (∏ p ∈ S2, ((n.factorization p : ℝ) + 1)) := by
      rw [hS1, hS2]
      exact (Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => p < K) _).symm
    -- ## small primes: at most `K` factors, each `≤ log n / log 2 + 1`
    have hS1card : S1.card ≤ K := by
      have hsub : S1 ⊆ Finset.range K := by
        intro p hp
        rw [hS1] at hp
        simp only [Finset.mem_filter] at hp
        exact Finset.mem_range.mpr hp.2
      calc S1.card ≤ (Finset.range K).card := Finset.card_le_card hsub
        _ = K := Finset.card_range K
    have hL1 : 1 ≤ Real.log n / Real.log 2 + 1 := by
      have : 0 ≤ Real.log n / Real.log 2 := div_nonneg hlog_nonneg hlog2pos.le
      linarith
    have hsmall : (∏ p ∈ S1, ((n.factorization p : ℝ) + 1))
        ≤ (Real.log n / Real.log 2 + 1) ^ K := by
      have hb : ∀ p ∈ S1, ((n.factorization p : ℝ) + 1) ≤ Real.log n / Real.log 2 + 1 := by
        intro p hp
        rw [hS1] at hp
        simp only [Finset.mem_filter] at hp
        obtain ⟨hpS, _hpK⟩ := hp
        have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpS
        have hp2 : 2 ≤ p := hpprime.two_le
        -- `p ^ e ∣ n` hence `e ≤ log n / log 2`
        have hdvd : p ^ n.factorization p ∣ n :=
          (hpprime.pow_dvd_iff_le_factorization hn0).mpr le_rfl
        have hle_n : p ^ n.factorization p ≤ n := Nat.le_of_dvd (by omega) hdvd
        have hcast : (p : ℝ) ^ (n.factorization p) ≤ (n : ℝ) := by
          exact_mod_cast hle_n
        have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp2)
        have hlogpl : Real.log 2 ≤ Real.log p :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hp2)
        have hmono : Real.log ((p : ℝ) ^ (n.factorization p)) ≤ Real.log (n : ℝ) :=
          Real.log_le_log (by positivity) hcast
        rw [Real.log_pow] at hmono
        have hle1 : (n.factorization p : ℝ) ≤ Real.log n / Real.log p := by
          rw [le_div_iff₀ hlogp]
          linarith
        have hle2 : Real.log n / Real.log p ≤ Real.log n / Real.log 2 :=
          div_le_div_of_nonneg_left hlog_nonneg hlog2pos hlogpl
        linarith
      calc (∏ p ∈ S1, ((n.factorization p : ℝ) + 1))
          ≤ ∏ _p ∈ S1, (Real.log n / Real.log 2 + 1) :=
            Finset.prod_le_prod₀ (fun p _ => by positivity) hb
        _ = (Real.log n / Real.log 2 + 1) ^ S1.card := Finset.prod_const _
        _ ≤ (Real.log n / Real.log 2 + 1) ^ K := pow_le_pow_right₀ hL1 hS1card
    -- ## large primes: `e + 1 ≤ p ^ (η * e)`
    have hbig : (∏ p ∈ S2, ((n.factorization p : ℝ) + 1)) ≤ ((n : ℝ)) ^ η := by
      have hb : ∀ p ∈ S2, ((n.factorization p : ℝ) + 1) ≤ (p : ℝ) ^ (η * (n.factorization p : ℝ)) := by
        intro p hp
        rw [hS2] at hp
        simp only [Finset.mem_filter] at hp
        obtain ⟨hpS, hpK⟩ := hp
        have hpK' : K ≤ p := by omega
        have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpS
        have h2p : (2 : ℝ) ≤ (p : ℝ) ^ η := hlarge p hpprime hpK'
        have he1 : ((n.factorization p : ℝ) + 1) ≤ (2 : ℝ) ^ (n.factorization p) := by
          have h := Nat.lt_two_pow_self (n := n.factorization p)
          have h' : n.factorization p + 1 ≤ 2 ^ (n.factorization p) := h
          exact_mod_cast h'
        have hstep2 : (2 : ℝ) ^ (n.factorization p)
            ≤ ((p : ℝ) ^ η) ^ (n.factorization p) :=
          pow_le_pow_left₀ (by norm_num) h2p _
        have hstep3 : ((p : ℝ) ^ η) ^ (n.factorization p)
            = (p : ℝ) ^ (η * (n.factorization p : ℝ)) := by
          rw [← Real.rpow_natCast (x := (p : ℝ) ^ η),
            ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (p : ℝ))]
        calc ((n.factorization p : ℝ) + 1) ≤ (2 : ℝ) ^ (n.factorization p) := he1
          _ ≤ ((p : ℝ) ^ η) ^ (n.factorization p) := hstep2
          _ = (p : ℝ) ^ (η * (n.factorization p : ℝ)) := hstep3
      have hsub : S2 ⊆ n.primeFactors := by
        rw [hS2]; exact Finset.filter_subset _ _
      have hone : ∀ p ∈ n.primeFactors, p ∉ S2 → (1 : ℝ) ≤ (p : ℝ) ^ (η * (n.factorization p : ℝ)) := by
        intro p hpS _
        have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hpS).two_le
        have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
        have h2 : (0 : ℝ) ≤ η * (n.factorization p : ℝ) := by positivity
        exact Real.one_le_rpow h1 h2
      -- rewrite the whole product over `n.primeFactors` as `n ^ η`
      have hpowcast : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p))) = (n : ℝ) := by
        simp only [← Nat.cast_pow, ← Nat.cast_prod]
        rw [← Nat.prod_primeFactors_pow_factorization hn0]
      have hfac : ∀ p ∈ n.primeFactors,
          (p : ℝ) ^ (η * (n.factorization p : ℝ)) = ((p : ℝ) ^ (n.factorization p)) ^ η := by
        intro p _
        rw [← Real.rpow_natCast (x := (p : ℝ)) (n := n.factorization p),
          ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (p : ℝ)), mul_comm]
      calc (∏ p ∈ S2, ((n.factorization p : ℝ) + 1))
          ≤ ∏ p ∈ S2, ((p : ℝ) ^ (η * (n.factorization p : ℝ))) :=
            Finset.prod_le_prod₀ (fun p _ => by positivity) hb
        _ ≤ ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (η * (n.factorization p : ℝ))) :=
            Finset.prod_le_prod_of_subset_of_one_le₀ hsub (fun p _ => by positivity) hone
        _ = ∏ p ∈ n.primeFactors, (((p : ℝ) ^ (n.factorization p)) ^ η) :=
            Finset.prod_congr rfl hfac
        _ = ((∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p))) ^ η) :=
            Real.finsetProd_rpow _ _ (fun p _ => by positivity) η
        _ = ((n : ℝ)) ^ η := by rw [hpowcast]
    calc (n.divisors.card : ℝ)
        = (∏ p ∈ S1, ((n.factorization p : ℝ) + 1))
          * (∏ p ∈ S2, ((n.factorization p : ℝ) + 1)) := by rw [hcard, hsplit]
      _ ≤ (Real.log n / Real.log 2 + 1) ^ K * ((n : ℝ)) ^ η :=
          mul_le_mul hsmall hbig (by positivity) (by positivity)

  -- ## Analytic bound: `(log n / log 2 + 1)^K ≤ C₀ * n^η` for `n ≥ 2`
  set C₀ : ℝ := (2 / Real.log 2) ^ K * (((K : ℝ) / η) ^ K) with hC₀def
  refine ⟨max 1 C₀, by positivity, ?_⟩
  intro n hn
  rcases lt_or_eq_of_le hn with h2 | h1
  · -- case `n ≥ 2`
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
    have hlog_nonneg : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    -- `log n / log 2 + 1 ≤ (2 / log 2) * log n`
    have hL_le : Real.log n / Real.log 2 + 1 ≤ (2 / Real.log 2) * Real.log n := by
      have hx : 1 ≤ Real.log n / Real.log 2 := by
        rw [le_div_iff₀ hlog2pos]
        simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn2
      have hid : (2 / Real.log 2) * Real.log n = 2 * (Real.log n / Real.log 2) := by
        field_simp
      rw [hid]
      linarith
    have hL0 : (0 : ℝ) ≤ Real.log n / Real.log 2 + 1 := by
      have : 0 ≤ Real.log n / Real.log 2 := div_nonneg hlog_nonneg hlog2pos.le
      linarith
    have hLpow : (Real.log n / Real.log 2 + 1) ^ K
        ≤ ((2 / Real.log 2) * Real.log n) ^ K := pow_le_pow_left₀ hL0 hL_le K
    -- `(log n)^K ≤ (K/η)^K * n^η`
    set s : ℝ := η / K with hsdef
    have hs : 0 < s := by rw [hsdef]; positivity
    have hlog_le : Real.log n ≤ (n : ℝ) ^ s / s := Real.log_le_rpow_div hnpos.le hs
    have hpowK : (Real.log n) ^ K ≤ ((n : ℝ) ^ s / s) ^ K :=
      pow_le_pow_left₀ hlog_nonneg hlog_le K
    have h1s : 1 / s = (K : ℝ) / η := by
      rw [hsdef]; field_simp
    have hgoalK : ((n : ℝ) ^ s / s) ^ K = ((K : ℝ) / η) ^ K * (n : ℝ) ^ η := by
      have hsK : s * (K : ℝ) = η := by rw [hsdef]; field_simp
      calc ((n : ℝ) ^ s / s) ^ K = ((n : ℝ) ^ s) ^ K / s ^ K := div_pow _ _ _
        _ = (n : ℝ) ^ (s * (K : ℝ)) / s ^ K := by
            rw [← Real.rpow_natCast (x := (n : ℝ) ^ s), ← Real.rpow_mul hnpos.le]
        _ = (n : ℝ) ^ η / s ^ K := by rw [hsK]
        _ = (n : ℝ) ^ η * (1 / s) ^ K := by rw [div_eq_mul_inv, one_div, inv_pow]
        _ = (n : ℝ) ^ η * ((K : ℝ) / η) ^ K := by rw [h1s]
        _ = ((K : ℝ) / η) ^ K * (n : ℝ) ^ η := by ring
    have hlogK : (Real.log n) ^ K ≤ ((K : ℝ) / η) ^ K * (n : ℝ) ^ η :=
      hpowK.trans_eq hgoalK
    -- assemble
    have h2η : (n : ℝ) ^ η * (n : ℝ) ^ η = (n : ℝ) ^ ε := by
      rw [← Real.rpow_add hnpos]
      congr 1
      rw [hηdef]; ring
    have hstep : (Real.log n / Real.log 2 + 1) ^ K * (n : ℝ) ^ η ≤ C₀ * (n : ℝ) ^ ε := by
      have hAmul : (0 : ℝ) ≤ (2 / Real.log 2) ^ K := by positivity
      calc (Real.log n / Real.log 2 + 1) ^ K * (n : ℝ) ^ η
          ≤ ((2 / Real.log 2) * Real.log n) ^ K * (n : ℝ) ^ η :=
            mul_le_mul_of_nonneg_right hLpow (by positivity)
        _ = (2 / Real.log 2) ^ K * (Real.log n) ^ K * (n : ℝ) ^ η := by rw [mul_pow]
        _ ≤ (2 / Real.log 2) ^ K * (((K : ℝ) / η) ^ K * (n : ℝ) ^ η) * (n : ℝ) ^ η := by
            have := mul_le_mul_of_nonneg_left hlogK hAmul
            exact mul_le_mul_of_nonneg_right this (by positivity)
        _ = C₀ * ((n : ℝ) ^ η * (n : ℝ) ^ η) := by rw [hC₀def]; ring
        _ = C₀ * (n : ℝ) ^ ε := by rw [h2η]
    calc (n.divisors.card : ℝ)
        ≤ (Real.log n / Real.log 2 + 1) ^ K * (n : ℝ) ^ η := key n hn
      _ ≤ C₀ * (n : ℝ) ^ ε := hstep
      _ ≤ max 1 C₀ * (n : ℝ) ^ ε :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · -- case `n = 1`
    subst h1
    simp only [Nat.divisors_one, Finset.card_singleton, Nat.cast_one, Real.one_rpow, mul_one]
    exact le_max_left _ _


/-!
# 三次多项式的纤维界

设 `P : ℤ[X]` 满足 `natDegree P = 3`，`A : Finset ℕ`。则 `A × A` 中满足
`P x = P y` 的对数不超过 `3 * A.card`。

证明分两步：

1. 固定 `x`，任何满足 `P y = P x` 的 `y` 都是 `P - C (P.eval x)` 的根；
   该多项式次数 `≤ 3`、非零，故根的（重数计）个数 `≤ 3`（`Polynomial.card_roots'`）。
2. 按第一坐标分纤维求和（`Finset.card_eq_sum_card_fiberwise`），
   得 `≤ ∑_{x ∈ A} 3 = 3 * A.card`。
-/

/-- 三次整系数多项式 P：在 A × A 上满足 P(x) = P(y) 的对数不超过 3·|A|（对每个 x，三次方程至多三解）。 -/
theorem fiber_zero (P : Polynomial ℤ) (hdeg : P.natDegree = 3) (A : Finset ℕ) :
    ((A.product A).filter (fun q : ℕ × ℕ =>
        Polynomial.eval (q.1 : ℤ) P = Polynomial.eval (q.2 : ℤ) P)).card
      ≤ 3 * A.card := by
  classical
  -- 主集：`A × A` 中使 `P` 取相同值的点对
  set S : Finset (ℕ × ℕ) := (A.product A).filter (fun q : ℕ × ℕ =>
      Polynomial.eval (q.1 : ℤ) P = Polynomial.eval (q.2 : ℤ) P) with hSdef

  -- ## 第一步：`P - C a` 非零且 `natDegree ≤ 3`
  have hdeg_sub : ∀ a : ℤ, (P - Polynomial.C a).natDegree ≤ 3 := by
    intro a
    calc (P - Polynomial.C a).natDegree
        ≤ max P.natDegree (Polynomial.C a).natDegree := Polynomial.natDegree_sub_le _ _
      _ ≤ max P.natDegree 0 := max_le_max le_rfl (Polynomial.natDegree_C a).le
      _ = P.natDegree := max_eq_left (Nat.zero_le _)
      _ = 3 := hdeg

  have hne : ∀ a : ℤ, P - Polynomial.C a ≠ 0 := by
    intro a h
    have hP : P = Polynomial.C a := sub_eq_zero.mp h
    have hle : P.natDegree ≤ 0 := by
      rw [hP, Polynomial.natDegree_C]
    rw [hdeg] at hle
    exact absurd hle (by norm_num)

  have hroots : ∀ a : ℤ, (P - Polynomial.C a).roots.card ≤ 3 := by
    intro a
    calc (P - Polynomial.C a).roots.card
        ≤ (P - Polynomial.C a).natDegree := Polynomial.card_roots' _
      _ ≤ 3 := hdeg_sub a

  -- ## 第二步：每个纤维至多 3 个点
  have hfiber : ∀ x : ℕ, (A.filter (fun y : ℕ =>
      Polynomial.eval (y : ℤ) P = Polynomial.eval (x : ℤ) P)).card ≤ 3 := by
    intro x
    have hinj : Function.Injective (fun y : ℕ => (y : ℤ)) := fun a b h => Nat.cast_injective h
    calc (A.filter (fun y : ℕ =>
            Polynomial.eval (y : ℤ) P = Polynomial.eval (x : ℤ) P)).card
        = ((A.filter (fun y : ℕ =>
            Polynomial.eval (y : ℤ) P = Polynomial.eval (x : ℤ) P)).image
            (fun y : ℕ => (y : ℤ))).card := (Finset.card_image_of_injective _ hinj).symm
      _ ≤ (P - Polynomial.C (Polynomial.eval (x : ℤ) P)).roots.toFinset.card := by
          apply Finset.card_le_card
          intro z hz
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
          obtain ⟨-, hyeq⟩ := Finset.mem_filter.mp hy
          rw [Multiset.mem_toFinset,
            Polynomial.mem_roots (p := P - Polynomial.C (Polynomial.eval (x : ℤ) P))
              (a := (y : ℤ)) (hne (Polynomial.eval (x : ℤ) P)),
            Polynomial.IsRoot.def]
          simp [hyeq]
      _ ≤ (P - Polynomial.C (Polynomial.eval (x : ℤ) P)).roots.card := Multiset.toFinset_card_le _
      _ ≤ 3 := hroots _

  -- ## 第三步：按第一坐标分纤维求和
  have hmaps : Set.MapsTo (fun q : ℕ × ℕ => q.1) (↑S : Set (ℕ × ℕ)) (↑A : Set ℕ) := by
    intro q hq
    rw [hSdef] at hq
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1

  have hsum : S.card = ∑ b ∈ A, (S.filter (fun q : ℕ × ℕ => q.1 = b)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps

  have hbound : ∀ b ∈ A, (S.filter (fun q : ℕ × ℕ => q.1 = b)).card ≤ 3 := by
    intro b _
    have hsub : S.filter (fun q : ℕ × ℕ => q.1 = b)
        ⊆ (A.filter (fun y : ℕ =>
            Polynomial.eval (y : ℤ) P = Polynomial.eval (b : ℤ) P)).image
            (fun y : ℕ => (b, y)) := by
      intro q hq
      rw [hSdef] at hq
      obtain ⟨hqinner, hq1b⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqprod, hFeq⟩ := Finset.mem_filter.mp hqinner
      obtain ⟨_, hq2A⟩ := Finset.mem_product.mp hqprod
      have hqfst : q.1 = b := hq1b
      have hev : Polynomial.eval (q.1 : ℤ) P = Polynomial.eval (q.2 : ℤ) P := hFeq
      refine Finset.mem_image.mpr ⟨q.2, Finset.mem_filter.mpr ⟨hq2A, ?_⟩, ?_⟩
      · exact hev.symm.trans (by rw [hqfst])
      · exact Prod.ext hqfst.symm rfl
    calc (S.filter (fun q : ℕ × ℕ => q.1 = b)).card
        ≤ ((A.filter (fun y : ℕ =>
            Polynomial.eval (y : ℤ) P = Polynomial.eval (b : ℤ) P)).image
            (fun y : ℕ => (b, y))).card := Finset.card_le_card hsub
      _ = (A.filter (fun y : ℕ =>
            Polynomial.eval (y : ℤ) P = Polynomial.eval (b : ℤ) P)).card :=
          Finset.card_image_of_injective _ (fun y₁ y₂ h => by simpa using h)
      _ ≤ 3 := hfiber b

  calc S.card = ∑ b ∈ A, (S.filter (fun q : ℕ × ℕ => q.1 = b)).card := hsum
    _ ≤ ∑ b ∈ A, 3 := Finset.sum_le_sum hbound
    _ = A.card * 3 := Finset.sum_const_nat (fun b _ => rfl)
    _ = 3 * A.card := Nat.mul_comm _ _


/-!
# 三次多项式差纤维的非零界

设 `P : ℤ[X]` 是三次整系数多项式（`P.natDegree = 3`），`c ≠ 0`，`A : Finset ℕ`。则方程
`P(x) - P(y) = c` 在 `A × A` 中的解数不超过 `4 * τ(|c|)`，其中 `τ(n) = n.divisors.card`。

证明分三步：

1. **（单射到除子）** 由 `Polynomial.sub_dvd_eval_sub`，任一解满足
   `(x - y) ∣ P(x) - P(y) = c`；又因 `c ≠ 0` 必有 `x ≠ y`。于是差
   `d = x - y` 落在 `c` 的非零有符号除子集 `D` 中，且
   `#D ≤ 2 * τ(|c|)`（每个绝对值只对应 `d` 与 `-d` 两个除子）。
2. **（每个差至多两解）** 固定 `d ≠ 0`，记 `a = P.coeff 3`、`b = P.coeff 2`、
   `cc = P.coeff 1`。用 `Polynomial.eval_eq_sum_range` 与 `P.natDegree = 3` 展开，
   `ring` 得恒等式
   `P(y+d) - P(y) = d * (3*a*y^2 + (3*a*d + 2*b)*y + (a*d^2 + b*d + cc))`。
   由于 `a ≠ 0`、`d ≠ 0`，右端是首项系数 `3*a*d ≠ 0` 的二次式，故把它写成多项式
   `R := C (3*a*d) * X^2 + C (b') * X + C (c')`，其 `natDegree = 2`
   （`Polynomial.natDegree_C_mul_X_pow` + `Polynomial.natDegree_add_eq_left_of_natDegree_lt`），
   解都落在 `R.roots` 内；由 `Polynomial.card_le_degree_of_subset_roots` 得纤维 ≤ 2。
3. **（按差分层求和）** 用 `Finset.card_eq_sum_card_fiberwise` 按 `d = x - y` 分层，
   每层 ≤ 2，层数 ≤ `2 * τ(|c|)`，合计 ≤ `4 * τ(|c|)`。

主结果：`fiber_nonzero`。
-/

open Polynomial

namespace FiberNonzero

/-- 三次多项式的系数展开（用 `coeff` 表示）：`P z = c₀ + c₁z + c₂z² + c₃z³`。 -/
lemma eval_cubic (P : Polynomial ℤ) (hdeg : P.natDegree = 3) (z : ℤ) :
    P.eval z = P.coeff 0 + P.coeff 1 * z + P.coeff 2 * z ^ 2 + P.coeff 3 * z ^ 3 := by
  rw [Polynomial.eval_eq_sum_range, hdeg]
  simp [Finset.sum_range_succ]

/-- 首项系数：次数为 `3` 的多项式，其三次项系数非零。 -/
lemma coeff_three_ne_zero (P : Polynomial ℤ) (hdeg : P.natDegree = 3) :
    P.coeff 3 ≠ 0 := by
  have hP : P ≠ 0 := by
    intro h
    rw [h] at hdeg
    simp at hdeg
  have h := Polynomial.coeff_natDegree (p := P)
  rw [hdeg] at h
  rw [h]
  exact Polynomial.leadingCoeff_ne_zero.mpr hP

/-- 一阶差商恒等式：`P(y+d) - P(y) = d * (3a y² + (3ad + 2b) y + (ad² + bd + cc))`。 -/
lemma eval_add_sub_eval (P : Polynomial ℤ) (hdeg : P.natDegree = 3) (d y : ℤ) :
    Polynomial.eval (y + d) P - Polynomial.eval y P =
      d * (3 * P.coeff 3 * y ^ 2 + (3 * P.coeff 3 * d + 2 * P.coeff 2) * y
        + (P.coeff 3 * d ^ 2 + P.coeff 2 * d + P.coeff 1)) := by
  rw [eval_cubic P hdeg (y + d), eval_cubic P hdeg y]
  ring

/-- 固定非零差 `d`：`A × A` 中既满足差为 `d`、又满足 `P x - P y = c` 的对至多两个。
`y` 满足一个首项系数非零的二次方程，故至多两根；`x = y + d` 由 `y` 唯一确定。 -/
lemma fiber_card_le_two (P : Polynomial ℤ) (hdeg : P.natDegree = 3) (A : Finset ℕ)
    (c d : ℤ) (hd : d ≠ 0) :
    ((A.product A).filter (fun q : ℕ × ℕ =>
        Polynomial.eval (q.1 : ℤ) P - Polynomial.eval (q.2 : ℤ) P = c ∧
          (q.1 : ℤ) - (q.2 : ℤ) = d)).card ≤ 2 := by
  classical
  have ha : P.coeff 3 ≠ 0 := coeff_three_ne_zero P hdeg
  have hA : P.coeff 3 * 3 * d ≠ 0 :=
    mul_ne_zero (mul_ne_zero ha (by norm_num)) hd
  set F : Finset (ℕ × ℕ) :=
    (A.product A).filter (fun q : ℕ × ℕ =>
      Polynomial.eval (q.1 : ℤ) P - Polynomial.eval (q.2 : ℤ) P = c ∧
        (q.1 : ℤ) - (q.2 : ℤ) = d) with hF
  -- 把"解满足二次方程"实现为某个二次多项式的根
  set R : Polynomial ℤ :=
    C (P.coeff 3 * 3 * d) * X ^ 2
      + (C (d * (3 * P.coeff 3 * d + 2 * P.coeff 2)) * X
        + C (d * (P.coeff 3 * d ^ 2 + P.coeff 2 * d + P.coeff 1) - c)) with hR
  have hReval : ∀ y : ℤ, R.eval y = Polynomial.eval (y + d) P - Polynomial.eval y P - c := by
    intro y
    rw [hR]
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]
    rw [eval_add_sub_eval P hdeg d y]
    ring
  have hR1 : (C (P.coeff 3 * 3 * d) * X ^ 2 : Polynomial ℤ).natDegree = 2 :=
    Polynomial.natDegree_C_mul_X_pow 2 _ hA
  have hB1 : (C (d * (3 * P.coeff 3 * d + 2 * P.coeff 2)) * X : Polynomial ℤ).natDegree ≤ 1 := by
    have h := Polynomial.natDegree_mul_le
      (p := (C (d * (3 * P.coeff 3 * d + 2 * P.coeff 2)) : Polynomial ℤ)) (q := (X : Polynomial ℤ))
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X] at h
    simpa using h
  have hC1 : (C (d * (P.coeff 3 * d ^ 2 + P.coeff 2 * d + P.coeff 1) - c) :
      Polynomial ℤ).natDegree ≤ 1 := by
    rw [Polynomial.natDegree_C]
    norm_num
  have hR2 : (C (d * (3 * P.coeff 3 * d + 2 * P.coeff 2)) * X
      + C (d * (P.coeff 3 * d ^ 2 + P.coeff 2 * d + P.coeff 1) - c) :
        Polynomial ℤ).natDegree ≤ 1 :=
    (Polynomial.natDegree_add_le _ _).trans (max_le hB1 hC1)
  have hRdeg : R.natDegree = 2 := by
    have hlt : (C (d * (3 * P.coeff 3 * d + 2 * P.coeff 2)) * X
        + C (d * (P.coeff 3 * d ^ 2 + P.coeff 2 * d + P.coeff 1) - c) :
          Polynomial ℤ).natDegree
        < (C (P.coeff 3 * 3 * d) * X ^ 2 : Polynomial ℤ).natDegree := by
      rw [hR1]
      exact hR2.trans_lt (by norm_num)
    have h := Polynomial.natDegree_add_eq_left_of_natDegree_lt (p := C (P.coeff 3 * 3 * d) * X ^ 2)
      (q := C (d * (3 * P.coeff 3 * d + 2 * P.coeff 2)) * X
        + C (d * (P.coeff 3 * d ^ 2 + P.coeff 2 * d + P.coeff 1) - c)) hlt
    rw [hR, h, hR1]
  have hRne : R ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hRdeg
    omega
  -- `y` 坐标在 `F` 上单射（`x = y + d` 由 `y` 唯一确定）
  have hinj : Set.InjOn (fun q : ℕ × ℕ => (q.2 : ℤ)) ↑F := by
    intro q hq q' hq' heq
    have heq' : ((q.2 : ℕ) : ℤ) = ((q'.2 : ℕ) : ℤ) := heq
    rw [Finset.mem_coe] at hq hq'
    rw [hF, Finset.mem_filter] at hq hq'
    obtain ⟨-, -, hqd⟩ := hq
    obtain ⟨-, -, hqd'⟩ := hq'
    have hnat : q.2 = q'.2 := by exact_mod_cast heq'
    have hx : q.1 = q'.1 := by
      have h1 : (q.1 : ℤ) = (q.2 : ℤ) + d := by rw [← hqd]; ring
      have h2 : (q'.1 : ℤ) = (q'.2 : ℤ) + d := by rw [← hqd']; ring
      exact_mod_cast (show (q.1 : ℤ) = (q'.1 : ℤ) by rw [h1, h2, heq'])
    exact Prod.ext hx hnat
  set G : Finset ℤ := F.image (fun q : ℕ × ℕ => (q.2 : ℤ)) with hG
  have hcard : F.card = G.card := by
    rw [hG]
    exact (Finset.card_image_of_injOn hinj).symm
  -- `G` 落在 `R` 的根集里
  have hGsub : G.val ⊆ R.roots := by
    intro g hg
    have hgG : g ∈ G := hg
    rw [hG, Finset.mem_image] at hgG
    obtain ⟨q, hq, hgq⟩ := hgG
    rw [← hgq]
    rw [hF, Finset.mem_filter] at hq
    obtain ⟨-, hqc, hqd⟩ := hq
    rw [Polynomial.mem_roots hRne]
    show R.eval ((q.2 : ℕ) : ℤ) = 0
    rw [hReval]
    have hx : ((q.2 : ℕ) : ℤ) + d = (q.1 : ℤ) := by rw [← hqd]; ring
    rw [hx, hqc, sub_self]
  have hle := Polynomial.card_le_degree_of_subset_roots (p := R) (Z := G) hGsub
  rw [hRdeg] at hle
  exact hcard.trans_le hle

end FiberNonzero

/-- 三次整系数多项式 `P`，固定非零整数 `c`：方程 `P(x) − P(y) = c` 在任意有限集 `A ⊆ ℕ`
上的解数不超过 `4·τ(|c|)`（有符号除子各至多两解）。 -/
theorem fiber_nonzero (P : Polynomial ℤ) (hdeg : P.natDegree = 3) (A : Finset ℕ) (c : ℤ) (hc : c ≠ 0) :
    ((A.product A).filter (fun q : ℕ × ℕ =>
        Polynomial.eval (q.1 : ℤ) P - Polynomial.eval (q.2 : ℤ) P = c)).card
      ≤ 4 * (Int.natAbs c).divisors.card := by
  classical
  set S : Finset (ℕ × ℕ) := (A.product A).filter (fun q : ℕ × ℕ =>
    Polynomial.eval (q.1 : ℤ) P - Polynomial.eval (q.2 : ℤ) P = c) with hS
  set D : Finset ℤ := S.image (fun q : ℕ × ℕ => (q.1 : ℤ) - (q.2 : ℤ)) with hD
  -- 每个差 `d` 都是 `c` 的非零除子
  have hmem : ∀ d ∈ D, ∃ q ∈ S, (q.1 : ℤ) - (q.2 : ℤ) = d := by
    intro d hd
    rw [hD, Finset.mem_image] at hd
    obtain ⟨q, hq, hqd⟩ := hd
    exact ⟨q, hq, hqd⟩
  have hdvd : ∀ d ∈ D, d ∣ c := by
    intro d hd
    obtain ⟨q, hq, hqd⟩ := hmem d hd
    rw [hS, Finset.mem_filter] at hq
    obtain ⟨-, hqc⟩ := hq
    rw [← hqd, ← hqc]
    exact Polynomial.sub_dvd_eval_sub (q.1 : ℤ) (q.2 : ℤ) P
  have hdne : ∀ d ∈ D, d ≠ 0 := by
    intro d hd hzero
    obtain ⟨q, hq, hqd⟩ := hmem d hd
    rw [hS, Finset.mem_filter] at hq
    obtain ⟨-, hqc⟩ := hq
    have hxy : (q.1 : ℤ) = (q.2 : ℤ) := by omega
    rw [hxy, sub_self] at hqc
    exact hc hqc.symm
  -- `c` 的非零有符号除子个数 ≤ `2 * τ(|c|)`
  have hDcard : D.card ≤ 2 * (Int.natAbs c).divisors.card := by
    have h1 : D.card ≤ 2 * (D.image Int.natAbs).card := by
      refine Finset.card_le_mul_card_image D 2 ?_
      intro b _
      have hsub : {d ∈ D | Int.natAbs d = b} ⊆ ({(b : ℤ), -(b : ℤ)} : Finset ℤ) := by
        intro d hd
        rw [Finset.mem_filter] at hd
        obtain ⟨-, hdb⟩ := hd
        have hcast : Int.natAbs d = Int.natAbs ((b : ℤ)) := by
          rw [hdb, Int.natAbs_natCast]
        rcases Int.natAbs_eq_natAbs_iff.mp hcast with h | h
        · rw [h]; simp
        · rw [h]; simp
      exact (Finset.card_le_card hsub).trans (Finset.card_le_two (a := (b : ℤ)) (b := -(b : ℤ)))
    have h2 : D.image Int.natAbs ⊆ (Int.natAbs c).divisors := by
      intro n hn
      rw [Finset.mem_image] at hn
      obtain ⟨d, hd, rfl⟩ := hn
      rw [Nat.mem_divisors]
      exact ⟨Int.natAbs_dvd_natAbs.mpr (hdvd d hd), Int.natAbs_ne_zero.mpr hc⟩
    exact h1.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card h2))
  -- 每个差纤维至多两解
  have hfib : ∀ d ∈ D, (S.filter (fun q : ℕ × ℕ => (q.1 : ℤ) - (q.2 : ℤ) = d)).card ≤ 2 := by
    intro d hd
    have heq : S.filter (fun q : ℕ × ℕ => (q.1 : ℤ) - (q.2 : ℤ) = d)
        = (A.product A).filter (fun q : ℕ × ℕ =>
            Polynomial.eval (q.1 : ℤ) P - Polynomial.eval (q.2 : ℤ) P = c ∧
              (q.1 : ℤ) - (q.2 : ℤ) = d) := by
      rw [hS, Finset.filter_filter]
    rw [heq]
    exact FiberNonzero.fiber_card_le_two P hdeg A c d (hdne d hd)
  -- 按差分层求和
  have hsplit : S.card
      = ∑ d ∈ D, (S.filter (fun q : ℕ × ℕ => (q.1 : ℤ) - (q.2 : ℤ) = d)).card := by
    rw [hD]
    exact Finset.card_eq_sum_card_fiberwise
      (f := fun q : ℕ × ℕ => (q.1 : ℤ) - (q.2 : ℤ))
      (fun q hq => Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  rw [hsplit]
  calc ∑ d ∈ D, (S.filter (fun q : ℕ × ℕ => (q.1 : ℤ) - (q.2 : ℤ) = d)).card
      ≤ ∑ _d ∈ D, 2 := Finset.sum_le_sum hfib
    _ = D.card * 2 := by simp
    _ ≤ (2 * (Int.natAbs c).divisors.card) * 2 := Nat.mul_le_mul_right 2 hDcard
    _ = 4 * (Int.natAbs c).divisors.card := by ring

/-!
# 主定理：三次多项式值和的碰撞计数

记 `K = |A|`。目标集合是 `T × T` 中满足 `S u = S v` 的那些点对（`T = A³`，`S u = ∑_{i<3} P(u i)`）。
把点对投射到 `A⁴`（`(u₀,v₀), (u₁,v₁)`），剩余自由度是 `(u₂,v₂)`，约束为
`P u₂ - P v₂ = (P v₀ + P v₁) - (P u₀ + P u₁) =: c(qd)`。
于是 `|Call| ≤ ∑_{qd ∈ A⁴} |{(x,y) ∈ A² : P x - P y = c(qd)}|`，逐项用 `fiber_zero` / `fiber_nonzero` 界住。
-/

/-- 单点取值 `P(n)`。 -/
private abbrev evZ (P : Polynomial ℤ) (n : ℕ) : ℤ := Polynomial.eval (n : ℤ) P

/-- 把 `(u,v)` 的第 0、1 位按 `(u_i, v_i)` 配成两对。 -/
private abbrev qp (f : (Fin 3 → ℕ) × (Fin 3 → ℕ)) : (ℕ × ℕ) × (ℕ × ℕ) :=
  ((f.1 0, f.2 0), (f.1 1, f.2 1))

/-- 一对的差 `P x - P y`。 -/
private abbrev dfr (P : Polynomial ℤ) (p : ℕ × ℕ) : ℤ := evZ P p.1 - evZ P p.2

/-- 四元组的目标值 `(P v₀ + P v₁) − (P u₀ + P u₁)`。 -/
private abbrev dtg (P : Polynomial ℤ) (qd : (ℕ × ℕ) × (ℕ × ℕ)) : ℤ :=
  (evZ P qd.1.2 + evZ P qd.2.2) - (evZ P qd.1.1 + evZ P qd.2.1)

/-- 差值纤维 `{(x,y) ∈ A × A : P x - P y = c}`。 -/
private abbrev fib (P : Polynomial ℤ) (A : Finset ℕ) (c : ℤ) : Finset (ℕ × ℕ) :=
  (A.product A).filter (fun p => dfr P p = c)

namespace Conjectures.Cuts

theorem Taskc1374e5a144c390fd55782fc (P : Polynomial ℤ) (_h3 : 3 ≤ P.natDegree)
    (hdeg : P.natDegree = 3) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M →
      let T := Fintype.piFinset (fun _ : Fin 3 => A)
      let S := fun u : Fin 3 → ℕ => ∑ i : Fin 3, Polynomial.eval (u i : ℤ) P
      (((T ×ˢ T).filter
        (fun f => S f.1 = S f.2 ∧ ∀ σ : Equiv.Perm (Fin 3), f.2 ≠ f.1 ∘ σ)).card : ℝ)
        ≤ C * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 := by
  classical
  -- ## 常数
  obtain ⟨Cτ, hCτpos, hCτ⟩ := card_divisors_le_rpow (ε / 3) (by linarith)
  set BP : ℕ := ∑ i ∈ Finset.range 4, (P.coeff i).natAbs with hBP
  have hBPnn : (0 : ℝ) ≤ (BP : ℝ) := Nat.cast_nonneg _
  refine ⟨16 * (Cτ * (4 * (BP : ℝ)) ^ (ε / 3) + 1) + 27, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ (4 * (BP : ℝ)) ^ (ε / 3) := Real.rpow_nonneg (by positivity) _
    nlinarith
  intro M hM A hA
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by
    have : (1 : ℕ) ≤ M := by omega
    exact_mod_cast this
  -- ============ 平凡情形：`A = ∅` ============
  rcases eq_or_ne A ∅ with hAe | hAne
  · subst hAe
    have hp : (Fintype.piFinset (fun _ : Fin 3 => (∅ : Finset ℕ))) = ∅ := Fintype.piFinset_empty
    simp [hp]
  -- ============ 主情形 ============
  have hK1 : 1 ≤ A.card := by
    rcases Nat.eq_zero_or_pos A.card with h | h
    · exact absurd (Finset.card_eq_zero.mp h) hAne
    · exact h
  -- ## 基本记号
  set K : ℕ := A.card with hK
  have hKr0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  have hKr1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
  set Quad : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := (A ×ˢ A) ×ˢ (A ×ˢ A) with hQuad
  set TR : ℝ := Cτ * (4 * (BP : ℝ) * (M : ℝ) ^ 3) ^ (ε / 3) with hTRdef
  have hTRnn : 0 ≤ TR :=
    mul_nonneg hCτpos.le (Real.rpow_nonneg (by positivity) _)
  -- ## 各项次数界
  have hev_bound : ∀ n ∈ A, (evZ P n).natAbs ≤ BP * M ^ 3 := by
    intro n hn
    have hnI := hA hn
    rw [Finset.mem_Icc] at hnI
    obtain ⟨hn1, hnM⟩ := hnI
    have hsum : evZ P n = ∑ i ∈ Finset.range 4, P.coeff i * (n : ℤ) ^ i := by
      show Polynomial.eval (n : ℤ) P = _
      rw [Polynomial.eval_eq_sum_range, hdeg]
    rw [hsum]
    calc (∑ i ∈ Finset.range 4, P.coeff i * (n : ℤ) ^ i).natAbs
        ≤ ∑ i ∈ Finset.range 4, (P.coeff i * (n : ℤ) ^ i).natAbs := Int.natAbs_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range 4, (P.coeff i).natAbs * M ^ 3 := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mem_range] at hi
          rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
          apply Nat.mul_le_mul_left
          calc n ^ i ≤ n ^ 3 := pow_le_pow_right₀ hn1 (by omega)
            _ ≤ M ^ 3 := pow_le_pow_left₀ (Nat.zero_le n) hnM 3
      _ = BP * M ^ 3 := by
          rw [hBP, Finset.sum_mul]
  -- ## 四元组值的界
  have hdtg_bound : ∀ qd ∈ Quad, (dtg P qd).natAbs ≤ 4 * BP * M ^ 3 := by
    intro qd hqd
    rw [hQuad] at hqd
    simp only [Finset.mem_product] at hqd
    obtain ⟨⟨ha1, ha2⟩, hb1, hb2⟩ := hqd
    have e1 : (evZ P qd.1.1).natAbs ≤ BP * M ^ 3 := hev_bound qd.1.1 ha1
    have e2 : (evZ P qd.1.2).natAbs ≤ BP * M ^ 3 := hev_bound qd.1.2 ha2
    have e3 : (evZ P qd.2.1).natAbs ≤ BP * M ^ 3 := hev_bound qd.2.1 hb1
    have e4 : (evZ P qd.2.2).natAbs ≤ BP * M ^ 3 := hev_bound qd.2.2 hb2
    have h1 : (evZ P qd.1.2 + evZ P qd.2.2).natAbs ≤ BP * M ^ 3 + BP * M ^ 3 :=
      (Int.natAbs_add_le _ _).trans (add_le_add e2 e4)
    have h2 : (evZ P qd.1.1 + evZ P qd.2.1).natAbs ≤ BP * M ^ 3 + BP * M ^ 3 :=
      (Int.natAbs_add_le _ _).trans (add_le_add e1 e3)
    have h3 : dtg P qd
        = (evZ P qd.1.2 + evZ P qd.2.2) - (evZ P qd.1.1 + evZ P qd.2.1) := rfl
    rw [h3]
    calc ((evZ P qd.1.2 + evZ P qd.2.2) - (evZ P qd.1.1 + evZ P qd.2.1)).natAbs
        ≤ (evZ P qd.1.2 + evZ P qd.2.2).natAbs
            + (evZ P qd.1.1 + evZ P qd.2.1).natAbs := Int.natAbs_sub_le _ _
      _ ≤ (BP * M ^ 3 + BP * M ^ 3) + (BP * M ^ 3 + BP * M ^ 3) := add_le_add h1 h2
      _ = 4 * BP * M ^ 3 := by ring
  -- ## `τ` 的统一界
  have htau_bound : ∀ c : ℤ, c ≠ 0 → (c.natAbs : ℝ) ≤ 4 * (BP : ℝ) * (M : ℝ) ^ 3 →
      ((c.natAbs).divisors.card : ℝ) ≤ TR := by
    intro c hcne hle
    have hcn1 : 1 ≤ c.natAbs := Int.natAbs_pos.mpr hcne
    have hτ := hCτ c.natAbs hcn1
    have hrpow : ((c.natAbs : ℝ)) ^ (ε / 3)
        ≤ (4 * (BP : ℝ) * (M : ℝ) ^ 3) ^ (ε / 3) :=
      Real.rpow_le_rpow (by positivity) hle (by linarith)
    calc ((c.natAbs).divisors.card : ℝ) ≤ Cτ * ((c.natAbs : ℝ)) ^ (ε / 3) := hτ
      _ ≤ Cτ * (4 * (BP : ℝ) * (M : ℝ) ^ 3) ^ (ε / 3) :=
          mul_le_mul_of_nonneg_left hrpow hCτpos.le
      _ = TR := by rw [hTRdef]
  have hTR_eq : TR = Cτ * (4 * (BP : ℝ)) ^ (ε / 3) * (M : ℝ) ^ ε := by
    rw [hTRdef]
    have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hcast : (M : ℝ) ^ 3 = (M : ℝ) ^ ((3 : ℕ) : ℝ) := (Real.rpow_natCast (M : ℝ) 3).symm
    rw [show (4 * (BP : ℝ) * (M : ℝ) ^ 3) = (4 * (BP : ℝ)) * ((M : ℝ) ^ 3) by ring,
      Real.mul_rpow (by positivity) (by positivity), hcast, ← Real.rpow_mul hMnn]
    have h3e : ((3 : ℕ) : ℝ) * (ε / 3) = ε := by push_cast; ring
    rw [h3e]
    ring
  -- ============ `Call` 与目标集合 ============
  set T : Finset (Fin 3 → ℕ) := Fintype.piFinset (fun _ : Fin 3 => A) with hT
  set Sf : (Fin 3 → ℕ) → ℤ := fun u => ∑ i : Fin 3, evZ P (u i) with hSf
  set Call : Finset ((Fin 3 → ℕ) × (Fin 3 → ℕ)) :=
    (T ×ˢ T).filter (fun f => Sf f.1 = Sf f.2) with hCall
  set Tgt : Finset ((Fin 3 → ℕ) × (Fin 3 → ℕ)) :=
    (T ×ˢ T).filter
      (fun f => Sf f.1 = Sf f.2 ∧ ∀ σ : Equiv.Perm (Fin 3), f.2 ≠ f.1 ∘ σ) with hTgt
  have hmemT : ∀ (f : Fin 3 → ℕ), f ∈ Fintype.piFinset (fun _ : Fin 3 => A) → ∀ i, f i ∈ A := by
    intro f hf i
    rw [Fintype.mem_piFinset] at hf
    exact hf i
  have hTgt_sub : Tgt ⊆ Call := by
    intro f hf
    rw [hTgt, Finset.mem_filter] at hf
    rw [hCall, Finset.mem_filter]
    exact ⟨hf.1, hf.2.1⟩
  -- ============ 纤维分解 ============
  have hmapQ : ∀ f ∈ Call, qp f ∈ Quad := by
    intro f hf
    rw [hCall, Finset.mem_filter] at hf
    simp only [Finset.mem_product] at hf
    obtain ⟨⟨hf1, hf2⟩, -⟩ := hf
    have h1a : f.1 0 ∈ A := hmemT f.1 hf1 0
    have h2a : f.2 0 ∈ A := hmemT f.2 hf2 0
    have h1b : f.1 1 ∈ A := hmemT f.1 hf1 1
    have h2b : f.2 1 ∈ A := hmemT f.2 hf2 1
    have hq : qp f = ((f.1 0, f.2 0), (f.1 1, f.2 1)) := rfl
    rw [hq, hQuad]
    simp only [Finset.mem_product]
    exact ⟨⟨h1a, h2a⟩, h1b, h2b⟩
  have hCall_card : Call.card = ∑ qd ∈ Quad, (Call.filter (fun f => qp f = qd)).card :=
    Finset.card_eq_sum_card_fiberwise hmapQ
  -- 单条纤维：`f ↦ (f.1 2, f.2 2)` 注入 `fib`
  have hfib_le : ∀ qd ∈ Quad, (Call.filter (fun f => qp f = qd)).card
      ≤ (fib P A (dtg P qd)).card := by
    intro qd hqd
    refine Finset.card_le_card_of_injOn
      (fun f : (Fin 3 → ℕ) × (Fin 3 → ℕ) => (f.1 2, f.2 2)) ?_ ?_
    · intro f hf
      simp only [Finset.mem_coe, Finset.mem_filter] at hf
      obtain ⟨hfCall, hfq⟩ := hf
      rw [hCall, Finset.mem_filter] at hfCall
      simp only [Finset.mem_product] at hfCall
      obtain ⟨⟨hf1, hf2⟩, hSeq⟩ := hfCall
      have h1 : f.1 2 ∈ A := hmemT f.1 hf1 2
      have h2 : f.2 2 ∈ A := hmemT f.2 hf2 2
      have hd1 : (f.1 0, f.2 0) = qd.1 := congrArg Prod.fst hfq
      have hd2 : (f.1 1, f.2 1) = qd.2 := congrArg Prod.snd hfq
      have h00 : qd.1.1 = f.1 0 := congrArg Prod.fst hd1.symm
      have h01 : qd.1.2 = f.2 0 := congrArg Prod.snd hd1.symm
      have h10 : qd.2.1 = f.1 1 := congrArg Prod.fst hd2.symm
      have h11 : qd.2.2 = f.2 1 := congrArg Prod.snd hd2.symm
      have hsum3 : evZ P (f.1 0) + evZ P (f.1 1) + evZ P (f.1 2)
          = evZ P (f.2 0) + evZ P (f.2 1) + evZ P (f.2 2) := by
        have h := hSeq
        rw [hSf] at h
        simpa only [Fin.sum_univ_three] using h
      have hgoal : dfr P (f.1 2, f.2 2) = dtg P qd := by
        show evZ P (f.1 2) - evZ P (f.2 2)
          = (evZ P qd.1.2 + evZ P qd.2.2) - (evZ P qd.1.1 + evZ P qd.2.1)
        rw [h00, h01, h10, h11]
        linarith [hsum3]
      have hmem : (f.1 2, f.2 2) ∈ (A ×ˢ A).filter
          (fun p : ℕ × ℕ => dfr P p = dtg P qd) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_product.mpr ⟨h1, h2⟩, hgoal⟩
      exact hmem
    · intro f hf g hg hfg
      simp only [Finset.mem_coe, Finset.mem_filter] at hf hg
      obtain ⟨-, hfq⟩ := hf
      obtain ⟨-, hgq⟩ := hg
      have h1 : f.1 2 = g.1 2 := congrArg Prod.fst hfg
      have h2 : f.2 2 = g.2 2 := congrArg Prod.snd hfg
      have e0 : (f.1 0, f.2 0) = (g.1 0, g.2 0) :=
        (congrArg Prod.fst hfq).trans (congrArg Prod.fst hgq).symm
      have e1 : (f.1 1, f.2 1) = (g.1 1, g.2 1) :=
        (congrArg Prod.snd hfq).trans (congrArg Prod.snd hgq).symm
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · fin_cases i
        · exact congrArg Prod.fst e0
        · exact congrArg Prod.fst e1
        · exact h1
      · fin_cases i
        · exact congrArg Prod.snd e0
        · exact congrArg Prod.snd e1
        · exact h2
  -- ============ 逐项两支界 ============
  have hfib0 : ∀ qd ∈ Quad, dtg P qd = 0 → (fib P A (dtg P qd)).card ≤ 3 * K := by
    intro qd _ h0
    have heq : fib P A (dtg P qd)
        = (A ×ˢ A).filter
            (fun p : ℕ × ℕ => Polynomial.eval (p.1 : ℤ) P = Polynomial.eval (p.2 : ℤ) P) := by
      rw [fib, h0]
      apply Finset.filter_congr
      intro p _
      show Polynomial.eval (p.1 : ℤ) P - Polynomial.eval (p.2 : ℤ) P = 0 ↔ _
      rw [sub_eq_zero]
    rw [heq, hK]
    exact fiber_zero P hdeg A
  have hfibnz : ∀ qd ∈ Quad, dtg P qd ≠ 0 → ((fib P A (dtg P qd)).card : ℝ) ≤ 4 * TR := by
    intro qd hqd hne
    have hnat := hdtg_bound qd hqd
    have hle : ((dtg P qd).natAbs : ℝ) ≤ 4 * (BP : ℝ) * (M : ℝ) ^ 3 := by
      have : ((dtg P qd).natAbs : ℝ) ≤ ((4 * BP * M ^ 3 : ℕ) : ℝ) := by exact_mod_cast hnat
      simpa using this
    have hτ := htau_bound (dtg P qd) hne hle
    have hfz := fiber_nonzero P hdeg A (dtg P qd) hne
    have hfz' : ((fib P A (dtg P qd)).card : ℝ)
        ≤ 4 * ((Int.natAbs (dtg P qd)).divisors.card : ℝ) := by exact_mod_cast hfz
    nlinarith
  -- ============ `Q₀` 的界 ============
  set Q0 : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := Quad.filter (fun qd => dtg P qd = 0) with hQ0
  set P0 : Finset (ℕ × ℕ) := (A ×ˢ A).filter (fun p => dfr P p = 0) with hP0
  have hP0card : P0.card ≤ 3 * K := by
    have heq : P0 = (A ×ˢ A).filter
        (fun q : ℕ × ℕ => Polynomial.eval (q.1 : ℤ) P = Polynomial.eval (q.2 : ℤ) P) := by
      rw [hP0]
      apply Finset.filter_congr
      intro q _
      show Polynomial.eval (q.1 : ℤ) P - Polynomial.eval (q.2 : ℤ) P = 0 ↔ _
      rw [sub_eq_zero]
    rw [heq, hK]
    exact fiber_zero P hdeg A
  have hQ0_decomp : Q0.card
      = ∑ p ∈ A ×ˢ A, (Q0.filter (fun qd => qd.1 = p)).card := by
    refine Finset.card_eq_sum_card_fiberwise ?_
    intro qd hqd
    simp only [Finset.mem_coe] at hqd
    rw [hQ0, Finset.mem_filter] at hqd
    obtain ⟨hqdQuad, -⟩ := hqd
    rw [hQuad] at hqdQuad
    exact (Finset.mem_product.mp hqdQuad).1
  have hQ0_fiber : ∀ p ∈ A ×ˢ A, (Q0.filter (fun qd => qd.1 = p)).card
      ≤ (fib P A (-(dfr P p))).card := by
    intro p hp
    refine Finset.card_le_card_of_injOn (fun qd : (ℕ × ℕ) × (ℕ × ℕ) => qd.2) ?_ ?_
    · intro qd hqd
      simp only [Finset.mem_coe, Finset.mem_filter] at hqd
      obtain ⟨hqdQ0, hqd1⟩ := hqd
      rw [hQ0, Finset.mem_filter] at hqdQ0
      obtain ⟨hqdQuad, hqd0⟩ := hqdQ0
      rw [hQuad] at hqdQuad
      simp only [Finset.mem_product] at hqdQuad
      have h1' : qd.2.1 ∈ A := hqdQuad.2.1
      have h2' : qd.2.2 ∈ A := hqdQuad.2.2
      have h0' : (evZ P qd.1.2 + evZ P qd.2.2) - (evZ P qd.1.1 + evZ P qd.2.1) = 0 := hqd0
      have hAB : evZ P qd.1.2 + evZ P qd.2.2 = evZ P qd.1.1 + evZ P qd.2.1 :=
        sub_eq_zero.mp h0'
      rw [hqd1] at hAB
      have hgoal : dfr P qd.2 = -(dfr P p) := by
        show evZ P qd.2.1 - evZ P qd.2.2 = -(evZ P p.1 - evZ P p.2)
        linarith
      have hmem : qd.2 ∈ (A ×ˢ A).filter (fun q : ℕ × ℕ => dfr P q = -(dfr P p)) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_product.mpr ⟨h1', h2'⟩, hgoal⟩
      exact hmem
    · intro qd hqd qd' hqd' h
      simp only [Finset.mem_coe, Finset.mem_filter] at hqd hqd'
      obtain ⟨-, hqd1⟩ := hqd
      obtain ⟨-, hqd1'⟩ := hqd'
      exact Prod.ext (hqd1.trans hqd1'.symm) h
  -- ## 两支上的纤维界（`p` 作为 `A²` 中的点）
  have hfibP0 : ∀ p ∈ P0, ((fib P A (-(dfr P p))).card : ℝ) ≤ 3 * (K : ℝ) := by
    intro p hp
    rw [hP0, Finset.mem_filter] at hp
    obtain ⟨-, hpz⟩ := hp
    have hz : -(dfr P p) = 0 := by rw [hpz, neg_zero]
    have heq : fib P A (-(dfr P p))
        = (A ×ˢ A).filter
            (fun q : ℕ × ℕ => Polynomial.eval (q.1 : ℤ) P = Polynomial.eval (q.2 : ℤ) P) := by
      rw [fib, hz]
      apply Finset.filter_congr
      intro q _
      show Polynomial.eval (q.1 : ℤ) P - Polynomial.eval (q.2 : ℤ) P = 0 ↔ _
      rw [sub_eq_zero]
    have h1 : (fib P A (-(dfr P p))).card ≤ 3 * A.card := by
      rw [heq]
      exact fiber_zero P hdeg A
    have h2 : ((3 * A.card : ℕ) : ℝ) = 3 * (K : ℝ) := by
      rw [hK]; push_cast; ring
    calc ((fib P A (-(dfr P p))).card : ℝ) ≤ ((3 * A.card : ℕ) : ℝ) := by exact_mod_cast h1
      _ = 3 * (K : ℝ) := h2
  have hfibPnz : ∀ p ∈ A ×ˢ A, dfr P p ≠ 0 →
      ((fib P A (-(dfr P p))).card : ℝ) ≤ 4 * TR := by
    intro p hp hpz
    have hne : -(dfr P p) ≠ 0 := neg_ne_zero.mpr hpz
    simp only [Finset.mem_product] at hp
    obtain ⟨hp1, hp2⟩ := hp
    have e1 : (evZ P p.1).natAbs ≤ BP * M ^ 3 := hev_bound p.1 hp1
    have e2 : (evZ P p.2).natAbs ≤ BP * M ^ 3 := hev_bound p.2 hp2
    have hnat : (dfr P p).natAbs ≤ BP * M ^ 3 + BP * M ^ 3 :=
      (Int.natAbs_sub_le _ _).trans (add_le_add e1 e2)
    have hle : (((-(dfr P p)).natAbs) : ℝ) ≤ 4 * (BP : ℝ) * (M : ℝ) ^ 3 := by
      have hna : ((-(dfr P p)).natAbs) = (dfr P p).natAbs := Int.natAbs_neg _
      rw [hna]
      have hcast : ((dfr P p).natAbs : ℝ) ≤ ((BP * M ^ 3 + BP * M ^ 3 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      have hM3 : (0 : ℝ) ≤ (M : ℝ) ^ 3 := by positivity
      have hfin : ((BP * M ^ 3 + BP * M ^ 3 : ℕ) : ℝ) ≤ 4 * (BP : ℝ) * (M : ℝ) ^ 3 := by
        push_cast
        nlinarith [mul_nonneg hBPnn hM3]
      linarith
    have hτ := htau_bound (-(dfr P p)) hne hle
    have hfz := fiber_nonzero P hdeg A (-(dfr P p)) hne
    have hfz' : ((fib P A (-(dfr P p))).card : ℝ)
        ≤ 4 * ((Int.natAbs (-(dfr P p))).divisors.card : ℝ) := by exact_mod_cast hfz
    nlinarith
  -- ## `Q₀` 的计数界
  have hQ0_le : (Q0.card : ℝ)
      ≤ (P0.card : ℝ) * (3 * (K : ℝ)) + ((A ×ˢ A).card : ℝ) * (4 * TR) := by
    calc (Q0.card : ℝ) = ∑ p ∈ A ×ˢ A, ((Q0.filter (fun qd => qd.1 = p)).card : ℝ) := by
          rw [hQ0_decomp]; push_cast; ring
      _ ≤ ∑ p ∈ A ×ˢ A, ((fib P A (-(dfr P p))).card : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          exact_mod_cast hQ0_fiber p hp
      _ = ∑ p ∈ P0, ((fib P A (-(dfr P p))).card : ℝ)
            + ∑ p ∈ (A ×ˢ A).filter (fun p => ¬ dfr P p = 0),
                ((fib P A (-(dfr P p))).card : ℝ) := by
          rw [hP0]
          exact (Finset.sum_filter_add_sum_filter_not (A ×ˢ A)
            (fun p => dfr P p = 0) (fun p => ((fib P A (-(dfr P p))).card : ℝ))).symm
      _ ≤ (P0.card : ℝ) * (3 * (K : ℝ)) + ((A ×ˢ A).card : ℝ) * (4 * TR) := by
          apply add_le_add
          · calc ∑ p ∈ P0, ((fib P A (-(dfr P p))).card : ℝ)
                ≤ ∑ _p ∈ P0, (3 * (K : ℝ)) := Finset.sum_le_sum hfibP0
              _ = (P0.card : ℝ) * (3 * (K : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
          · calc ∑ p ∈ (A ×ˢ A).filter (fun p => ¬ dfr P p = 0),
                  ((fib P A (-(dfr P p))).card : ℝ)
                ≤ ∑ _p ∈ (A ×ˢ A).filter (fun p => ¬ dfr P p = 0), (4 * TR) := by
                  apply Finset.sum_le_sum
                  intro p hp
                  rw [Finset.mem_filter] at hp
                  exact hfibPnz p hp.1 hp.2
              _ = ((A ×ˢ A).filter (fun p => ¬ dfr P p = 0)).card * (4 * TR) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
              _ ≤ ((A ×ˢ A).card : ℝ) * (4 * TR) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  exact_mod_cast Finset.card_filter_le (A ×ˢ A) (fun p => ¬ dfr P p = 0)
  have hKsq : ((A ×ˢ A).card : ℝ) = (K : ℝ) ^ 2 := by
    rw [Finset.card_product, hK]
    push_cast
    ring
  have hQuadcard : (Quad.card : ℝ) = (K : ℝ) ^ 4 := by
    rw [hQuad, Finset.card_product, Finset.card_product, hK]
    push_cast
    ring
  have hQ0_final : (Q0.card : ℝ) ≤ 9 * (K : ℝ) ^ 2 + 4 * (K : ℝ) ^ 2 * TR := by
    have h1 : (P0.card : ℝ) ≤ 3 * (K : ℝ) := by exact_mod_cast hP0card
    calc (Q0.card : ℝ)
        ≤ (P0.card : ℝ) * (3 * (K : ℝ)) + ((A ×ˢ A).card : ℝ) * (4 * TR) := hQ0_le
      _ = (P0.card : ℝ) * (3 * (K : ℝ)) + (K : ℝ) ^ 2 * (4 * TR) := by rw [hKsq]
      _ ≤ (3 * (K : ℝ)) * (3 * (K : ℝ)) + (K : ℝ) ^ 2 * (4 * TR) := by
          have h2 : (P0.card : ℝ) * (3 * (K : ℝ)) ≤ (3 * (K : ℝ)) * (3 * (K : ℝ)) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
          linarith
      _ = 9 * (K : ℝ) ^ 2 + 4 * (K : ℝ) ^ 2 * TR := by ring
  -- ## 完整集合的界
  have hQ0term : ∀ qd ∈ Q0, ((fib P A (dtg P qd)).card : ℝ) ≤ 3 * (K : ℝ) := by
    intro qd hqd
    rw [hQ0, Finset.mem_filter] at hqd
    have h1 := hfib0 qd hqd.1 hqd.2
    exact_mod_cast h1
  have hCall_le : (Call.card : ℝ)
      ≤ (Q0.card : ℝ) * (3 * (K : ℝ)) + (Quad.card : ℝ) * (4 * TR) := by
    calc (Call.card : ℝ) = ∑ qd ∈ Quad, ((Call.filter (fun f => qp f = qd)).card : ℝ) := by
          rw [hCall_card]; push_cast; ring
      _ ≤ ∑ qd ∈ Quad, ((fib P A (dtg P qd)).card : ℝ) := by
          apply Finset.sum_le_sum
          intro qd hqd
          exact_mod_cast hfib_le qd hqd
      _ = ∑ qd ∈ Q0, ((fib P A (dtg P qd)).card : ℝ)
            + ∑ qd ∈ Quad.filter (fun qd => ¬ dtg P qd = 0),
                ((fib P A (dtg P qd)).card : ℝ) := by
          rw [hQ0]
          exact (Finset.sum_filter_add_sum_filter_not Quad (fun qd => dtg P qd = 0)
            (fun qd => ((fib P A (dtg P qd)).card : ℝ))).symm
      _ ≤ (Q0.card : ℝ) * (3 * (K : ℝ)) + (Quad.card : ℝ) * (4 * TR) := by
          apply add_le_add
          · calc ∑ qd ∈ Q0, ((fib P A (dtg P qd)).card : ℝ)
                ≤ ∑ _qd ∈ Q0, (3 * (K : ℝ)) := Finset.sum_le_sum hQ0term
              _ = (Q0.card : ℝ) * (3 * (K : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
          · calc ∑ qd ∈ Quad.filter (fun qd => ¬ dtg P qd = 0),
                  ((fib P A (dtg P qd)).card : ℝ)
                ≤ ∑ _qd ∈ Quad.filter (fun qd => ¬ dtg P qd = 0), (4 * TR) := by
                  apply Finset.sum_le_sum
                  intro qd hqd
                  rw [Finset.mem_filter] at hqd
                  exact hfibnz qd hqd.1 hqd.2
              _ = (Quad.filter (fun qd => ¬ dtg P qd = 0)).card * (4 * TR) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
              _ ≤ (Quad.card : ℝ) * (4 * TR) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  exact_mod_cast Finset.card_filter_le Quad (fun qd => ¬ dtg P qd = 0)
  -- ============ 汇总 ============
  have hK34 : (K : ℝ) ^ 3 ≤ (K : ℝ) ^ 4 := pow_le_pow_right₀ hKr1 (by norm_num)
  have hstep1 : (Tgt.card : ℝ)
      ≤ (Q0.card : ℝ) * (3 * (K : ℝ)) + (Quad.card : ℝ) * (4 * TR) :=
    le_trans (by exact_mod_cast Finset.card_le_card hTgt_sub) hCall_le
  have hA1 : (Q0.card : ℝ) * (3 * (K : ℝ))
      ≤ 27 * (K : ℝ) ^ 3 + 12 * (K : ℝ) ^ 3 * TR := by
    have hm := mul_le_mul_of_nonneg_right hQ0_final (show (0 : ℝ) ≤ 3 * (K : ℝ) by positivity)
    have he : (9 * (K : ℝ) ^ 2 + 4 * (K : ℝ) ^ 2 * TR) * (3 * (K : ℝ))
        = 27 * (K : ℝ) ^ 3 + 12 * (K : ℝ) ^ 3 * TR := by ring
    rw [he] at hm
    exact hm
  have hA2 : (27 : ℝ) * (K : ℝ) ^ 3 + 12 * (K : ℝ) ^ 3 * TR
      ≤ 27 * (K : ℝ) ^ 4 + 12 * (K : ℝ) ^ 4 * TR := by
    have ha : (27 : ℝ) * (K : ℝ) ^ 3 ≤ 27 * (K : ℝ) ^ 4 := by
      have h' := mul_le_mul_of_nonneg_left hK34 (show (0 : ℝ) ≤ 27 by norm_num)
      linarith
    have hb : (12 : ℝ) * (K : ℝ) ^ 3 * TR ≤ 12 * (K : ℝ) ^ 4 * TR := by
      have h34 : (K : ℝ) ^ 3 * TR ≤ (K : ℝ) ^ 4 * TR :=
        mul_le_mul hK34 le_rfl hTRnn (by positivity)
      nlinarith [h34]
    linarith
  have hA3 : (Quad.card : ℝ) * (4 * TR) = 4 * (K : ℝ) ^ 4 * TR := by
    rw [hQuadcard]; ring
  have hfin : (Tgt.card : ℝ) ≤ 27 * (K : ℝ) ^ 4 + 16 * (K : ℝ) ^ 4 * TR := by
    calc (Tgt.card : ℝ)
        ≤ (Q0.card : ℝ) * (3 * (K : ℝ)) + (Quad.card : ℝ) * (4 * TR) := hstep1
      _ ≤ (27 * (K : ℝ) ^ 3 + 12 * (K : ℝ) ^ 3 * TR) + 4 * (K : ℝ) ^ 4 * TR := by
          rw [hA3]; linarith [hA1]
      _ ≤ (27 * (K : ℝ) ^ 4 + 12 * (K : ℝ) ^ 4 * TR) + 4 * (K : ℝ) ^ 4 * TR := by
          linarith [hA2]
      _ = 27 * (K : ℝ) ^ 4 + 16 * (K : ℝ) ^ 4 * TR := by ring
  have hQnn : (0 : ℝ) ≤ Cτ * (4 * (BP : ℝ)) ^ (ε / 3) :=
    mul_nonneg hCτpos.le (Real.rpow_nonneg (by positivity) _)
  have hMeps1 : (1 : ℝ) ≤ (M : ℝ) ^ ε := Real.one_le_rpow hM1 hε.le
  have hkey : (Tgt.card : ℝ)
      ≤ (16 * (Cτ * (4 * (BP : ℝ)) ^ (ε / 3) + 1) + 27) * (M : ℝ) ^ ε * (K : ℝ) ^ 4 := by
    have hbase : 16 * (K : ℝ) ^ 4 * TR
        = 16 * (Cτ * (4 * (BP : ℝ)) ^ (ε / 3)) * (M : ℝ) ^ ε * (K : ℝ) ^ 4 := by
      rw [hTR_eq]; ring
    nlinarith [hfin, hbase, hMeps1]
  rw [hK] at hkey
  simpa only [hTgt, hCall, hT, hSf, evZ] using hkey

end Conjectures.Cuts
/-! ## 交叉验证：本定理的类型与 `Conjectures/Cuts/Taskc1374e5a144c390fd55782fc.lean`
中的陈述逐字一致（下面这条 `example` 直接用逐字陈述刻画同一个类型）。 -/

example : (∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     x1.natDegree = (3 : ℕ) →       ∀ (x4 : ℝ),         (0 : ℝ) < x4 →           ∃ (x6 : ℝ),             (0 : ℝ) < x6 ∧               ∀ (x7 : ℕ),                 (2 : ℕ) ≤ x7 →                   ∀ x9 ⊆ Finset.Icc (1 : ℕ) x7,                     have x11 : Finset (Fin (3 : ℕ) → ℕ) := Fintype.piFinset fun (x11 : Fin (3 : ℕ)) => x9;                     have x12 : (Fin (3 : ℕ) → ℕ) → ℤ := fun (x12 : Fin (3 : ℕ) → ℕ) => ∑ x13 : Fin (3 : ℕ), Polynomial.eval (↑(x12 x13)) x1;                     ↑{x13 ∈ x11.product x11 | x12 x13.1 = x12 x13.2 ∧ ∀ (x14 : Equiv.Perm (Fin (3 : ℕ))), x13.2 ≠ x13.1 ∘ ⇑x14}.card ≤ x6 * ↑x7 ^ x4 * ↑x9.card ^ (4 : ℕ)) :=
  Conjectures.Cuts.Taskc1374e5a144c390fd55782fc