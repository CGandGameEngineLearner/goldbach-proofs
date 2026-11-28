import Mathlib

/-! Six powers of two, with a signed triple-power weight.
Source: Huixi Li and Zhixin Liu, https://arxiv.org/html/2610.15784v1#S2 ,
equations (8)–(13), and section 6, equation (62).
The cap L and prime cutoff are integers. The first moment is uniform over
all caps with cutoff + 3·2^L ≤ K/1000000, where the even target is 2K.
The second moment supplies one pair in this same range. In the paper's choice
2^L=o(K) and the prime cutoff is o(K), so this range includes it eventually.

#4255 already extracts witnesses from the number of six-power representations.
This cut treats the prime-plus-three-powers distribution. Both premises are
closed, and the proof pairs complementary odd targets using finite reflection.
-/

-- child 1 zh: 对全部满足截断条件的指数上限与素数下限，素数加二幂的带符号计数在奇数目标上的一阶矩具有指定下界。
-- child 1 en: Uniform first mass of the signed prime-plus-powers weights on odd sites for admissible cutoff pairs.
-- child 2 zh: 对每个充分大的偶数目标，存在同一范围内的一组截断参数，使带符号计数的二阶矩低于给定阈值。
-- child 2 en: For every sufficiently large even target, find an admissible cutoff pair giving the stated upper bound on the signed second moment.

theorem Conjectures.Cuts.Cut552e85acde57b644a7505471
    (hfirst : ∃ T : ℕ, ∀ K L cutoff : ℕ, T ≤ K → 0 < L →
      cutoff + 3 * 2^L ≤ K / 1000000 →
      let w := fun (j x : ℕ) => ∑ a : Fin j → Fin L,
        let p := x - ∑ i : Fin j, 2 ^ ((a i).val + 1)
        if cutoff < p ∧ p.Prime then Real.log p else 0
      let f := fun (i : Fin K) =>
        let x := 2*i.val+1
        w 3 x - (L : ℝ)/4 * w 2 x - (L : ℝ)^2/16 * w 1 x
      ((11 : ℝ)/16 - 1/4096) * (2*(K : ℝ)) * (L : ℝ)^3 ≤ ∑ i : Fin K, f i)
    (hsecond : ∃ T : ℕ, ∀ K : ℕ, T ≤ K →
      ∃ L cutoff : ℕ, 0 < L ∧ cutoff + 3 * 2^L ≤ K / 1000000 ∧
      let w := fun (j x : ℕ) => ∑ a : Fin j → Fin L,
        let p := x - ∑ i : Fin j, 2 ^ ((a i).val + 1)
        if cutoff < p ∧ p.Prime then Real.log p else 0
      let f := fun (i : Fin K) =>
        let x := 2*i.val+1
        w 3 x - (L : ℝ)/4 * w 2 x - (L : ℝ)^2/16 * w 1 x
      (∑ i : Fin K, (f i)^2) ≤ ((241 : ℝ)/128 + 1/1024) * (2*(K : ℝ)) * (L : ℝ)^6) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ ∃ a : Fin 6 → ℕ, N = p + q + ∑ i : Fin 6, 2 ^ (a i + 1) := by
  classical
  /- The positive exponents in an ordered tuple are written as `a i + 1`. -/
  let dyadicShift {j L : ℕ} (a : Fin j → Fin L) : ℕ :=
    ∑ i, 2 ^ ((a i).val + 1)

  /- Li–Liu, arXiv:2610.15784v1, (8), on a target at most the outer parameter N.
  The integer cutoff is the floor of the lower prime cutoff. -/
  let primePowerWeight (j L cutoff x : ℕ) : ℝ :=
    ∑ a : Fin j → Fin L,
      let p := x - dyadicShift a
      if cutoff < p ∧ p.Prime then Real.log p else 0

  have primePowerWeight_nonneg (j L cutoff x : ℕ) :
      0 ≤ primePowerWeight j L cutoff x := by
    dsimp only [primePowerWeight]
    apply Finset.sum_nonneg
    intro a _
    split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.2.one_le)
    · exact le_rfl

  have witness_of_positive_weight {j L cutoff x : ℕ}
      (h : 0 < primePowerWeight j L cutoff x) :
      ∃ (p : ℕ) (a : Fin j → Fin L),
        cutoff < p ∧ p.Prime ∧ x = p + dyadicShift a := by
    classical
    by_contra! hnone
    apply (not_le_of_gt h)
    dsimp only [primePowerWeight]
    apply Finset.sum_nonpos
    intro a _
    split_ifs with hp
    · have hw := hnone (x - dyadicShift a) a hp.1 hp.2
      have hp' := hp.2.pos
      omega
    · exact le_rfl

  /- Positive correlation of the log-weighted triple-power representation counts at
  complementary odd arguments gives the precise six-power witnesses of the site.
  The odd targets are parametrised by `i : Fin K` with `N = 2*K`. -/
  have sixPowerWitness_of_positive_triple_reflection (K L cutoff : ℕ)
      (h : 0 < ∑ i : Fin K,
        primePowerWeight 3 L cutoff (2 * i.val + 1) *
        primePowerWeight 3 L cutoff (2 * (Fin.rev i).val + 1)) :
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ ∃ a : Fin 6 → ℕ,
        2 * K = p + q + ∑ i : Fin 6, 2 ^ (a i + 1) := by
    classical
    obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ =>
      mul_nonneg (primePowerWeight_nonneg 3 L cutoff (2 * i.val + 1))
        (primePowerWeight_nonneg 3 L cutoff (2 * (Fin.rev i).val + 1)))).mp h
    have hx : 0 < primePowerWeight 3 L cutoff (2 * i.val + 1) :=
      pos_of_mul_pos_left hi (primePowerWeight_nonneg ..)
    have hy : 0 < primePowerWeight 3 L cutoff (2 * (Fin.rev i).val + 1) :=
      pos_of_mul_pos_right hi (primePowerWeight_nonneg ..)
    obtain ⟨p, a, _, hp, hpa⟩ := witness_of_positive_weight hx
    obtain ⟨q, b, _, hq, hqb⟩ := witness_of_positive_weight hy
    let u : Fin 3 → ℕ := fun t => (a t).val
    let v : Fin 3 → ℕ := fun t => (b t).val
    refine ⟨p, q, hp, hq, Fin.append u v, ?_⟩
    have hsplit : (∑ t : Fin (3+3), 2 ^ (Fin.append u v t + 1) : ℕ) =
        dyadicShift a + dyadicShift b := by
      rw [Fin.sum_univ_add]
      dsimp only [dyadicShift]
      congr 1
    rw [hsplit]
    have hrev : (Fin.rev i).val = K - (i.val+1) := rfl
    have hiK := i.isLt
    omega



  /- The finite Cauchy–Schwarz step in (13), with the denominator cleared.
  The sequence may take negative values. -/
  have odd_reflection_cauchy {K : ℕ} (g : Fin K → ℝ) :
      2 * (∑ i, g i) ^ 2 ≤
        (K : ℝ) * ((∑ i, g i ^ 2) + ∑ i, g i * g i.rev) := by
    have hreindex : (∑ i, g (Fin.rev i)) = ∑ i, g i := Equiv.sum_comp Fin.revPerm g
    have hreindex₂ : (∑ i, g (Fin.rev i) ^ 2) = ∑ i, g i ^ 2 :=
      Equiv.sum_comp Fin.revPerm (fun i => g i ^ 2)
    have hexpand : (∑ i, (g i + g i.rev) ^ 2) =
        2 * ((∑ i, g i ^ 2) + ∑ i, g i * g i.rev) := by
      calc
        _ = ∑ i, ((g i ^ 2 + g i.rev ^ 2) + 2 * (g i * g i.rev)) := by
          apply Finset.sum_congr rfl
          intros
          ring
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hreindex₂]
          ring
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin K => (1 : ℝ))
      (fun i => g i + g i.rev)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at h
    rw [Finset.sum_add_distrib, hreindex, hexpand] at h
    nlinarith only [h]

  /- Quantitative form of Lemma 2.1 prior to taking limits. `f` is the
  signed one-prime representation function from (9) and `r` majorizes its
  positive part, as does the unsigned triple-power function `r'₃` in the paper.
  `mass` is a nonnegative lower bound on its signed mass and `energy` an upper
  bound on its signed second moment. -/
  have triple_reflection_lower_bound {K : ℕ} (hK : 0 < K) (f r : Fin K → ℝ)
      (hmajor : ∀ i, max (f i) 0 ≤ r i) {mass energy : ℝ} (hmass0 : 0 ≤ mass)
      (hmass : mass ≤ ∑ i, f i) (henergy : (∑ i, f i ^ 2) ≤ energy) :
      4 / (2 * (K : ℝ)) * mass ^ 2 - energy ≤ ∑ i, r i * r i.rev := by
    let g : Fin K → ℝ := fun i => max (f i) 0
    have hg0 (i : Fin K) : 0 ≤ g i := le_max_right _ _
    have hmassg : mass ≤ ∑ i, g i := hmass.trans (Finset.sum_le_sum fun i _ => le_max_left _ _)
    have hmassg₂ : mass ^ 2 ≤ (∑ i, g i) ^ 2 := by gcongr
    have hgenergy : (∑ i, g i ^ 2) ≤ energy := by
      refine le_trans (Finset.sum_le_sum fun i _ => ?_) henergy
      by_cases hi : 0 ≤ f i
      · simp [g, max_eq_left hi]
      · simp [g, max_eq_right (le_of_not_ge hi), sq_nonneg]
    have hpair : (∑ i, g i * g i.rev) ≤ ∑ i, r i * r i.rev :=
      Finset.sum_le_sum fun i _ => mul_le_mul (hmajor i) (hmajor i.rev) (hg0 _) ((hg0 i).trans (hmajor i))
    have hscaled : 2 * mass ^ 2 ≤ (K : ℝ) * (energy + ∑ i, r i * r i.rev) :=
      (mul_le_mul_of_nonneg_left hmassg₂ (by norm_num)).trans <|
        (odd_reflection_cauchy g).trans <|
          mul_le_mul_of_nonneg_left (add_le_add hgenergy hpair) (Nat.cast_nonneg K)
    have hK' : 0 < (K : ℝ) := by exact_mod_cast hK
    have hdivide : (2 * mass ^ 2) / (K : ℝ) ≤ energy + ∑ i, r i * r i.rev :=
      (div_le_iff₀ hK').2 (by simpa only [mul_comm] using hscaled)
    have hcoeff : 4 / (2 * (K : ℝ)) * mass ^ 2 = (2 * mass ^ 2) / (K : ℝ) := by ring
    linarith only [hdivide, hcoeff]

  /- With `a = 1/4` and `b = 1/16`, (11) gives normalized first mass tending
  to `11/16`, and (62) gives a normalized signed energy upper bound tending
  to `241/128` after the auxiliary error is made small. These explicit error
  allowances suffice for the positive constant in Theorem 1.1, equation (4).
  The two analytic inequalities are hypotheses of this finite conclusion. -/
  have six_power_moment_budget {K : ℕ} (hK : 0 < K) (f r : Fin K → ℝ)
      (hmajor : ∀ i, max (f i) 0 ≤ r i) {L : ℝ} (hL : 0 ≤ L)
      (hfirst : ((11 : ℝ) / 16 - 1 / 4096) * (2 * (K : ℝ)) * L ^ 3 ≤ ∑ i, f i)
      (hsecond : (∑ i, f i ^ 2) ≤
        ((241 : ℝ) / 128 + 1 / 1024) * (2 * (K : ℝ)) * L ^ 6) :
      (2 * (K : ℝ)) * L ^ 6 / 1000 ≤ ∑ i, r i * r i.rev := by
    have hK' : 0 < (K : ℝ) := by exact_mod_cast hK
    have hmass0 : (0 : ℝ) ≤ ((11 : ℝ) / 16 - 1 / 4096) * (2 * (K : ℝ)) * L ^ 3 := by
      have : (0 : ℝ) ≤ 11 / 16 - 1 / 4096 := by norm_num
      positivity
    apply le_trans _ (triple_reflection_lower_bound hK f r hmajor hmass0 hfirst hsecond)
    field_simp
    nlinarith [mul_nonneg (sq_nonneg (K : ℝ)) (sq_nonneg (L ^ 3))]

  /- The signed weight (9) for `a = 1/4`, `b = 1/16` on the odd target `2*i+1`. -/
  let signedWeight (L cutoff : ℕ) {K : ℕ} (i : Fin K) : ℝ :=
    primePowerWeight 3 L cutoff (2*i.val+1) -
      (L : ℝ) / 4 * primePowerWeight 2 L cutoff (2*i.val+1) -
      (L : ℝ)^2 / 16 * primePowerWeight 1 L cutoff (2*i.val+1)

  /- The two quantitative moment estimates sufficient for an even target `2*K`.
  The second bound follows from the Parseval comparison (12) and the analytic
  upper bound (62) once their error terms fit the displayed allowances. -/
  let MomentBounds (K L cutoff : ℕ) : Prop :=
    ((11 : ℝ) / 16 - 1 / 4096) * (2 * (K : ℝ)) * (L : ℝ)^3 ≤
        ∑ i : Fin K, signedWeight L cutoff i ∧
    (∑ i : Fin K, (signedWeight L cutoff i)^2) ≤
        ((241 : ℝ) / 128 + 1 / 1024) * (2 * (K : ℝ)) * (L : ℝ)^6

  /- Applying the finite estimate to the actual prime-plus-powers sums recovers
  two primes and exactly six positive binary powers from the two moment bounds. -/
  have six_power_witness_of_moment_bounds (K L cutoff : ℕ) (hK : 0 < K) (hL : 0 < L)
      (hm : MomentBounds K L cutoff) :
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ ∃ a : Fin 6 → ℕ,
        2*K = p + q + ∑ i, 2 ^ (a i + 1) := by
    have hmajor (i : Fin K) : max (signedWeight L cutoff i) 0 ≤
        primePowerWeight 3 L cutoff (2*i.val+1) := by
      refine max_le ?_ (primePowerWeight_nonneg ..)
      dsimp only [signedWeight]
      have h₂ := primePowerWeight_nonneg 2 L cutoff (2*i.val+1)
      have h₁ := primePowerWeight_nonneg 1 L cutoff (2*i.val+1)
      have ha : 0 ≤ (L : ℝ) / 4 * primePowerWeight 2 L cutoff (2*i.val+1) := by positivity
      have hb : 0 ≤ (L : ℝ)^2 / 16 * primePowerWeight 1 L cutoff (2*i.val+1) := by positivity
      linarith
    apply sixPowerWitness_of_positive_triple_reflection K L cutoff
    have hstrict : 0 < (2 * (K : ℝ)) * (L : ℝ)^6 / 1000 := by positivity
    exact hstrict.trans_le (six_power_moment_budget hK (signedWeight L cutoff)
      (fun i : Fin K => primePowerWeight 3 L cutoff (2*i.val+1)) hmajor
      (Nat.cast_nonneg L) hm.1 hm.2)
  obtain ⟨T₁, h₁⟩ := hfirst
  obtain ⟨T₂, h₂⟩ := hsecond
  refine ⟨2 * (max T₁ T₂ + 1), ?_⟩
  intro N hN heven
  obtain ⟨K, hK⟩ := heven
  have hKN : N = 2*K := by omega
  obtain ⟨L, cutoff, hL, hrange, hE⟩ := h₂ K (by omega)
  have hM := h₁ K L cutoff (by omega) hL hrange
  have hb : MomentBounds K L cutoff := ⟨hM,hE⟩
  rw [hKN]
  exact six_power_witness_of_moment_bounds K L cutoff (by omega) hL hb
