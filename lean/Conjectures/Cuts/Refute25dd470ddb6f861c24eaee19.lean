import Mathlib

/-!
# Refutation of the cut `L-goldbach-cut-6808ac6d4347fea08cc89764`

The frozen statement asserts that, for all sufficiently large even `n`, the number `L(n)` of
cube-root-rough semiprimes `u` in the central window `[(n+2)/3, 2n/3]` (i.e. `u = p q` with
`p = q` or `p < q` primes and `p > ⌊n^{1/3}⌋`) is at most `23/50` times the terminal sieve volume
`V(n) = |I| · φ(n)/n · ∏_{p ≤ √n, p ∤ n} (1 - 2/p)`.

This is false. Along `n = 2^K` the one-sided count is of order `n / log n` while the volume is of
order `n / (log n)²`, so the ratio `L(n)/V(n)` tends to infinity. Concretely, for `z = n^{1/3}`
and each dyadic block `Y = 2^j z` (`0 ≤ j < J = K/6 - 1`), the primes `p ∈ (11Y/10, 19Y/10]`
and, for each such `p`, the primes `q ∈ (11n/(30p), 19n/(30p)]` produce distinct products
`pq ∈ [n/3, 2n/3]` with `p = minFac(pq) > z`. The prime number theorem (Mathlib's
`Nat.isEquivalent_primeCounting`) gives at least `Y / (4 log Y)` such `p` and at least
`n / (23 Y log n)` such `q`, so each block contributes at least `(10/912) n / (log n)²`
products, and there are `J` blocks. For `n = 2^K` the volume is
`V(n) ≤ n · (1/2) · ∏_{p ≤ 2^{K/2}} (1 - 1/p)² ≤ 2n / log²(2^{K/2}) = 8n / (log n)²`, using the
elementary Euler–Mertens bound `∏_{p ≤ N} (1 - 1/p) ≤ 1 / log N` proved below from the harmonic
series. Hence `(23/50) V(n) ≤ 184 n / (log n)² < J · (10/912) n / (log n)²` as soon as `J ≥ 337`,
which gives the refutation for all large `K`.
-/

open Finset Filter Asymptotics Topology
open scoped BigOperators Real

namespace GoldbachRefute6808

theorem log_le_harmonic (N : ℕ) : Real.log N ≤ ∑ m ∈ range N, (1 / ((m : ℝ) + 1)) := by
  have h0 : Real.log N ≤ Real.log ((N : ℝ) + 1) := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · exact Real.log_le_log (by exact_mod_cast hN) (by exact_mod_cast Nat.le_succ N)
  have h2 := Finset.sum_range_sub (fun k : ℕ => Real.log ((k : ℝ) + 1)) N
  have h3 : ∑ m ∈ range N, (Real.log (((m + 1 : ℕ) : ℝ) + 1) - Real.log ((m : ℝ) + 1)) =
      Real.log ((N : ℝ) + 1) := by
    rw [h2]; simp
  have h : Real.log ((N : ℝ) + 1) =
      ∑ m ∈ range N, (Real.log ((m : ℝ) + 2) - Real.log ((m : ℝ) + 1)) := by
    rw [← h3]
    simp only [Nat.cast_add, Nat.cast_one, add_assoc, show (1 : ℝ) + 1 = 2 from by norm_num]
  refine h0.trans (le_of_eq h) |>.trans ?_
  refine Finset.sum_le_sum (fun m _ => ?_)
  have h1 : Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) ≤ ((m : ℝ) + 2) / ((m : ℝ) + 1) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) (by positivity)] at h1
  have : ((m : ℝ) + 2) / ((m : ℝ) + 1) - 1 = 1 / ((m : ℝ) + 1) := by
    field_simp
    linarith
  rw [this] at h1
  exact h1

theorem geom_mul' (K : ℕ) (x : ℝ) : (1 - x) * ∑ j ∈ range (K + 1), x ^ j = 1 - x ^ (K + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, mul_add, ih, sub_mul]
    ring

theorem geom_sum_le' (K : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx : x < 1) :
    ∑ j ∈ range (K + 1), x ^ j ≤ 1 / (1 - x) := by
  have hpos : 0 < 1 - x := by linarith
  have h := geom_mul' K x
  rw [le_div_iff₀ hpos, mul_comm, h]
  have := pow_nonneg hx0 (K + 1)
  nlinarith

theorem one_div_prod' (S : Finset ℕ) (f : ℕ → ℝ) : ∏ p ∈ S, (1 / f p) = 1 / ∏ p ∈ S, f p := by
  rw [Finset.prod_div_distrib]; simp

set_option maxHeartbeats 1000000 in
theorem mertens_prod_le (N : ℕ) (hN : 2 ≤ N) :
    (∏ p ∈ Nat.primesLE N, (1 - 1 / (p : ℝ))) ≤ 1 / Real.log N := by
  classical
  set S := Nat.primesLE N with hS
  set K := Nat.log 2 N with hK
  have hK1 : 2 ^ K ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hK2 : N < 2 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hmem : ∀ p ∈ S, p.Prime ∧ p ≤ N := fun p hp =>
    ⟨(Nat.mem_primesLE.mp hp).2, (Nat.mem_primesLE.mp hp).1⟩
  have hP : 0 < ∏ p ∈ S, (1 - 1 / (p : ℝ)) :=
    Finset.prod_pos (fun p hp => sub_pos.mpr ((div_lt_one (by exact_mod_cast (hmem p hp).1.pos)).mpr
      (by exact_mod_cast (hmem p hp).1.one_lt)))
  obtain ⟨E, hE⟩ : ∃ E : ℕ → (S → ℕ), E = fun m x => (m + 1).factorization (x : ℕ) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : S → Finset ℕ, t = fun _ => range (K + 1) := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : (x : S) → ℕ → ℝ,
      f = fun (x : S) (j : ℕ) => 1 / (((x : ℕ) : ℝ)) ^ j := ⟨_, rfl⟩
  have hbox : ∀ m ∈ range N, E m ∈ Fintype.piFinset t := by
    intro m hm
    rw [Fintype.mem_piFinset]
    intro x
    rw [ht, hE, mem_range]
    have hdvd : (x : ℕ) ^ ((m + 1).factorization (x : ℕ)) ∣ m + 1 := by
      rw [← Nat.multiplicity_eq_factorization (hmem _ x.2).1]
      exact pow_multiplicity_dvd _ _
    have hx2 : 2 ≤ (x : ℕ) := (hmem _ x.2).1.two_le
    have h1 : 2 ^ ((m + 1).factorization (x : ℕ)) ≤ (x : ℕ) ^ ((m + 1).factorization (x : ℕ)) :=
      Nat.pow_le_pow_left hx2 _
    have h2 := h1.trans (Nat.le_of_dvd (Nat.succ_pos m) hdvd)
    have h3 : m + 1 ≤ N := (Finset.mem_range.mp hm)
    have h4 := Nat.le_log_iff_pow_le (by norm_num) (by omega : (N : ℕ) ≠ 0) |>.mpr (h2.trans h3)
    have h5 : (m + 1).factorization (x : ℕ) ≤ K := by rw [hK]; exact h4
    show (m + 1).factorization (x : ℕ) < K + 1
    omega
  have hinj : Set.InjOn E (range N) := by
    intro m hm m' hm' hEE
    have h1 : ∀ p, (m + 1).factorization p = (m' + 1).factorization p := by
      intro p
      by_cases hp : p ∈ S
      · simpa [hE] using congrFun hEE ⟨p, hp⟩
      have hnot : ¬ (p ≤ N ∧ Nat.Prime p) := fun h => hp (Nat.mem_primesLE.mpr h)
      have hzero : (m + 1).factorization p = 0 ∧ (m' + 1).factorization p = 0 := by
        by_cases hpr : p.Prime
        · have hpN : N < p := lt_of_not_ge (fun h => hnot ⟨h, hpr⟩)
          have hd1 : ¬ p ∣ m + 1 := fun h =>
            not_le_of_gt hpN ((Nat.le_of_dvd (Nat.succ_pos m) h).trans (Finset.mem_range.mp hm))
          have hd2 : ¬ p ∣ m' + 1 := fun h =>
            not_le_of_gt hpN ((Nat.le_of_dvd (Nat.succ_pos m') h).trans (Finset.mem_range.mp hm'))
          exact ⟨Nat.factorization_eq_zero_of_not_dvd hd1, Nat.factorization_eq_zero_of_not_dvd hd2⟩
        · exact ⟨Nat.factorization_eq_zero_of_not_prime _ hpr,
            Nat.factorization_eq_zero_of_not_prime _ hpr⟩
      rw [hzero.1, hzero.2]
    exact Nat.succ_injective (Nat.eq_of_factorization_eq (Nat.succ_ne_zero _) (Nat.succ_ne_zero _) h1)
  have hsub : ∀ m ∈ range N, (m + 1).factorization.support ⊆ S := by
    intro m hm p hp
    rw [Finsupp.mem_support_iff] at hp
    have hpr : p.Prime := by
      by_contra hpr
      exact hp (Nat.factorization_eq_zero_of_not_prime _ hpr)
    have hd : p ∣ m + 1 := by
      by_contra hd
      exact hp (Nat.factorization_eq_zero_of_not_dvd hd)
    rw [hS, Nat.mem_primesLE]
    exact ⟨(Nat.le_of_dvd (Nat.succ_pos m) hd).trans (Finset.mem_range.mp hm), hpr⟩
  have hterm : ∀ m ∈ range N, (∏ x : S, f x (E m x)) = 1 / ((m : ℝ) + 1) := by
    intro m hm
    have hm1 : m + 1 ≠ 0 := Nat.succ_ne_zero m
    have hpow : ∏ x ∈ S, ((x : ℕ) : ℝ) ^ (m + 1).factorization x = ((m + 1 : ℕ) : ℝ) := by
      have h := Nat.prod_factorization_pow_eq_self hm1
      rw [Finsupp.prod] at h
      rw [← Finset.prod_subset (f := fun x : ℕ => ((x : ℕ) : ℝ) ^ (m + 1).factorization x) (hsub m hm)
        (fun p _ hp => by rw [Finsupp.notMem_support_iff.mp hp]; simp)]
      simp only [← Nat.cast_pow, ← Nat.cast_prod]
      rw [h]
    simp only [hf, hE]
    rw [Finset.prod_coe_sort S (fun x : ℕ => 1 / ((x : ℝ)) ^ (m + 1).factorization x),
      one_div_prod', hpow]
    push_cast
    rfl
  have key1 : ∑ m ∈ range N, (1 / ((m : ℝ) + 1)) = ∑ m ∈ range N, (∏ x : S, f x (E m x)) :=
    Finset.sum_congr rfl (fun m hm => (hterm m hm).symm)
  have key2 : ∑ m ∈ range N, (∏ x : S, f x (E m x)) =
      ∑ e ∈ (range N).image E, (∏ x : S, f x (e x)) :=
    (Finset.sum_image (f := fun e => ∏ x : S, f x (e x)) hinj).symm
  have fnonneg : ∀ (x : S) (j : ℕ), 0 ≤ f x j := fun x j => by rw [hf]; positivity
  have key3 : ∑ e ∈ (range N).image E, (∏ x : S, f x (e x)) ≤
      ∑ e ∈ Fintype.piFinset t, (∏ x : S, f x (e x)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hbox)
      (by
        intro e _ _
        exact Finset.prod_nonneg (fun x _ => fnonneg x (e x)))
  have key4 : ∑ e ∈ Fintype.piFinset t, (∏ x : S, f x (e x)) = ∏ x : S, (∑ j ∈ t x, f x j) :=
    (Finset.prod_univ_sum t f).symm
  have key : ∑ m ∈ range N, (1 / ((m : ℝ) + 1)) ≤ ∏ x : S, (∑ j ∈ t x, f x j) :=
    (le_of_eq key1).trans (le_of_eq key2) |>.trans (key3.trans (le_of_eq key4))
  have hinner : ∀ x : S, ∑ j ∈ t x, f x j ≤ ((x : ℕ) : ℝ) / (((x : ℕ) : ℝ) - 1) := by
    intro x
    have hx2 := (hmem _ x.2).1.two_le
    have hxR : 2 ≤ ((x : ℕ) : ℝ) := by exact_mod_cast hx2
    have hg := geom_sum_le' K (1 / ((x : ℕ) : ℝ)) (by positivity)
      ((div_lt_one (by exact_mod_cast (hmem _ x.2).1.pos)).mpr (by linarith))
    have h1 : ∑ j ∈ t x, f x j = ∑ j ∈ range (K + 1), (1 / ((x : ℕ) : ℝ)) ^ j := by
      rw [ht, hf]
      exact Finset.sum_congr rfl (fun j _ => (one_div_pow _ j).symm)
    rw [h1]
    calc
      _ ≤ 1 / (1 - 1 / ((x : ℕ) : ℝ)) := hg
      _ = ((x : ℕ) : ℝ) / (((x : ℕ) : ℝ) - 1) := by rw [one_div]; field_simp
  have key2 : ∏ x : S, (∑ j ∈ t x, f x j) ≤ ∏ x : S, ((x : ℕ) : ℝ) / (((x : ℕ) : ℝ) - 1) :=
    Finset.prod_le_prod₀ (fun x _ => Finset.sum_nonneg (fun j _ => fnonneg x j)) (fun x _ => hinner x)
  have key3 : ∏ x : S, ((x : ℕ) : ℝ) / (((x : ℕ) : ℝ) - 1) = 1 / ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
    rw [Finset.prod_coe_sort S (fun p : ℕ => ((p : ℝ)) / ((p : ℝ) - 1)), ← one_div_prod']
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hpp := (hmem p hp).1
    have hp1 : ((p : ℝ) - 1) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hpp.ne_one)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    field_simp
  have hfinal : ∑ m ∈ range N, (1 / ((m : ℝ) + 1)) ≤ 1 / ∏ p ∈ S, (1 - 1 / (p : ℝ)) :=
    key.trans (key2.trans (le_of_eq key3))
  have hinv : Real.log N ≤ (∏ p ∈ S, (1 - 1 / (p : ℝ)))⁻¹ := by
    rw [inv_eq_one_div]; exact log_le_harmonic N |>.trans hfinal
  have hfin := mul_le_mul_of_nonneg_left hinv hP.le
  rw [mul_inv_cancel₀ hP.ne'] at hfin
  rw [le_div_iff₀ hpos]
  exact hfin

/-- The prime counting function on real arguments. -/
noncomputable def pc (x : ℝ) : ℝ := (Nat.primeCounting ⌊x⌋₊ : ℝ)

theorem pnt_ratio : Tendsto (fun x : ℝ => pc x / (x / Real.log x)) atTop (𝓝 1) := by
  have hv : ∀ᶠ x : ℝ in atTop, x / Real.log x ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact (div_ne_zero (ne_of_gt (lt_trans zero_lt_one hx)) (Real.log_pos hx).ne')
  have h := (isEquivalent_iff_tendsto_one hv).mp Nat.isEquivalent_primeCounting
  exact h.congr (fun x => by simp [pc])

theorem pi_bounds : ∀ᶠ x : ℝ in atTop,
    (9 / 10 : ℝ) * (x / Real.log x) ≤ pc x ∧ pc x ≤ (11 / 10 : ℝ) * (x / Real.log x) := by
  have hlo := pnt_ratio.eventually_const_lt (by norm_num : (9 / 10 : ℝ) < 1)
  have hhi := pnt_ratio.eventually_lt_const (by norm_num : (1 : ℝ) < 11 / 10)
  filter_upwards [hlo, hhi, eventually_gt_atTop 1] with x h1 h2 hx
  have hg : 0 < x / Real.log x := div_pos (lt_trans zero_lt_one hx) (Real.log_pos hx)
  constructor
  · exact (lt_div_iff₀ hg).mp h1 |>.le
  · exact (div_lt_iff₀ hg).mp h2 |>.le

/-- For large `Y`, the interval `[11Y/10, 19Y/10]` contains at least `Y / (4 log Y)` primes. -/
theorem window_primes : ∀ᶠ Y : ℝ in atTop,
    Y / (4 * Real.log Y) ≤
      (((Nat.primesLE ⌊19 * Y / 10⌋₊) \ Nat.primesLE ⌊11 * Y / 10⌋₊) : Finset ℕ).card := by
  have hlo : ∀ᶠ x : ℝ in atTop, (9 / 10 : ℝ) * (x / Real.log x) ≤ pc x := by
    filter_upwards [pi_bounds] with x hx
    exact hx.1
  have hhi : ∀ᶠ x : ℝ in atTop, pc x ≤ (11 / 10 : ℝ) * (x / Real.log x) := by
    filter_upwards [pi_bounds] with x hx
    exact hx.2
  obtain ⟨A₁, hA₁⟩ := eventually_atTop.mp hlo
  obtain ⟨A₂, hA₂⟩ := eventually_atTop.mp hhi
  filter_upwards [eventually_ge_atTop (10 : ℝ), eventually_ge_atTop (Real.exp 10),
    eventually_ge_atTop A₁, eventually_ge_atTop A₂] with Y hY10 hYe hY₁ hY₂
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le (Real.exp_pos 10) hYe
  have hL10 : (10 : ℝ) ≤ Real.log Y := by
    have h := Real.log_le_log (Real.exp_pos 10) hYe
    rwa [Real.log_exp] at h
  have hL0 : (0 : ℝ) < Real.log Y := by linarith
  set a : ℕ := ⌊19 * Y / 10⌋₊ with ha
  set b : ℕ := ⌊11 * Y / 10⌋₊ with hb'
  have ha1 : (a : ℝ) ≤ 19 * Y / 10 := by exact_mod_cast Nat.floor_le (by positivity)
  have ha1' : (a : ℝ) ≤ (19 / 10 : ℝ) * Y := by exact ha1.trans (le_of_eq (by ring))
  have ha2 : 19 * Y / 10 < (a : ℝ) + 1 := by exact_mod_cast Nat.lt_floor_add_one _
  have hb1 : (b : ℝ) ≤ 11 * Y / 10 := by exact_mod_cast Nat.floor_le (by positivity)
  have hb1' : (b : ℝ) ≤ (11 / 10 : ℝ) * Y := by exact hb1.trans (le_of_eq (by ring))
  have hb2 : 11 * Y / 10 < (b : ℝ) + 1 := by exact_mod_cast Nat.lt_floor_add_one _
  have ha0 : (0 : ℝ) < a := by
    have : 0 < 19 * Y / 10 - 1 := by nlinarith
    linarith
  have hb0 : (0 : ℝ) < b := by
    have : 0 < 11 * Y / 10 - 1 := by nlinarith
    linarith
  have hloga0 : (0 : ℝ) < Real.log a := Real.log_pos (by linarith)
  have hlogb0 : (0 : ℝ) < Real.log b := Real.log_pos (by linarith)
  have hba : b ≤ a := by
    have h2 : (b : ℝ) < 19 * Y / 10 := by linarith
    exact_mod_cast (by linarith : (b : ℝ) ≤ (a : ℝ))
  have hloga : Real.log a ≤ Real.log Y + 1 := by
    refine (Real.log_le_log ha0 ha1).trans ?_
    have h1 : 19 * Y / 10 ≤ Real.exp 1 * Y := by
      have := Real.add_one_le_exp (1 : ℝ)
      nlinarith
    calc
      Real.log (19 * Y / 10) ≤ Real.log (Real.exp 1 * Y) := Real.log_le_log (by positivity) h1
      _ = Real.log Y + 1 := by rw [Real.log_mul (Real.exp_ne_zero 1) hY0.ne', Real.log_exp]; ring
  have hlogb : Real.log Y ≤ Real.log b := by
    refine Real.log_le_log hY0 ?_
    linarith
  -- PNT bounds at the (natural) endpoints
  have haY : (0 : ℝ) < 19 * Y / 10 - 1 := by nlinarith
  have hbY : (0 : ℝ) < 11 * Y / 10 - 1 := by nlinarith
  have hloa := hA₁ ((a : ℝ)) (by linarith)
  have hhib := hA₂ ((b : ℝ)) (by linarith)
  simp only [pc, show (⌊((a : ℕ) : ℝ)⌋₊) = a from by simp,
    show (⌊((b : ℕ) : ℝ)⌋₊) = b from by simp] at hloa hhib
  have hcard : (((Nat.primesLE a \ Nat.primesLE b : Finset ℕ)).card : ℝ) =
      (Nat.primeCounting a : ℝ) - (Nat.primeCounting b : ℝ) := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Nat.primesLE_mono hba),
      Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
    rw [Nat.cast_sub (Nat.monotone_primeCounting hba)]
  rw [hcard]
  -- (i): the lower main term at `a`
  have ha' : (18 / 10 : ℝ) * Y ≤ a := by
    have : (1 : ℝ) ≤ Y / 10 := by linarith
    linarith
  have hi : ((162 : ℝ) / 100) * (Y / (Real.log Y + 1)) ≤ (9 / 10 : ℝ) * (a / Real.log a) := by
    have h1 : ((18 / 10 : ℝ) * Y) * Real.log a ≤ a * Real.log a :=
      mul_le_mul_of_nonneg_right ha' hloga0.le
    have h2 : a * Real.log a ≤ a * (Real.log Y + 1) :=
      mul_le_mul_of_nonneg_left hloga ha0.le
    have h3 : a * (Real.log Y + 1) ≥ ((18 / 10 : ℝ) * Y) * Real.log a := by linarith
    have h4 : ((18 / 10 : ℝ) * Y) / (Real.log Y + 1) ≤ a / Real.log a :=
      (div_le_div_iff₀ (by linarith) hloga0).mpr h3
    calc
      _ = (9 / 10 : ℝ) * (((18 / 10 : ℝ) * Y) / (Real.log Y + 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by norm_num)
  -- (ii): the upper main term at `b`
  have hii : (11 / 10 : ℝ) * (b / Real.log b) ≤ ((121 : ℝ) / 100) * (Y / Real.log Y) := by
    have h1 : b * Real.log Y ≤ (11 / 10 : ℝ) * Y * Real.log b := by
      have h1a : b * Real.log Y ≤ (11 / 10 : ℝ) * Y * Real.log Y :=
        mul_le_mul_of_nonneg_right hb1' hL0.le
      have h1b : (11 / 10 : ℝ) * Y * Real.log Y ≤ (11 / 10 : ℝ) * Y * Real.log b :=
        mul_le_mul_of_nonneg_left hlogb (by positivity)
      exact h1a.trans h1b
    have h2 : b / Real.log b ≤ ((11 / 10 : ℝ) * Y) / Real.log Y :=
      (div_le_div_iff₀ hlogb0 hL0).mpr h1
    calc
      _ = (11 / 10 : ℝ) * (b / Real.log b) := rfl
      _ ≤ (11 / 10 : ℝ) * (((11 / 10 : ℝ) * Y) / Real.log Y) :=
        mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = _ := by ring
  -- (iii): combine
  have hratio : (10 / 11 : ℝ) ≤ Real.log Y / (Real.log Y + 1) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  have hR0 : (0 : ℝ) ≤ Y / Real.log Y := by positivity
  have h3 := mul_le_mul_of_nonneg_left hratio
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 162 / 100) hR0)
  have hid : (162 : ℝ) / 100 * (Y / (Real.log Y + 1)) =
      (162 / 100) * (Y / Real.log Y) * (Real.log Y / (Real.log Y + 1)) := by
    field_simp
  rw [hid] at hi
  have hYd : Y / (4 * Real.log Y) = (1 / 4 : ℝ) * (Y / Real.log Y) := by ring
  rw [hYd]
  linarith

theorem cube_two_pow (K : ℕ) (hK : 6 ∣ K) : (⌊(((2 ^ K : ℕ) : ℝ)) ^ (1 / 3 : ℝ)⌋₊) = 2 ^ (K / 3) := by
  have h2 : ((K : ℝ) / 3) = ((K / 3 : ℕ) : ℝ) := by
    exact (Nat.cast_div (dvd_trans (by norm_num : (3 : ℕ) ∣ 6) hK) (by norm_num : ((3 : ℝ)) ≠ 0)).symm
  have h1 : ((2 ^ K : ℕ) : ℝ) ^ (1 / 3 : ℝ) = ((2 ^ (K / 3) : ℕ) : ℝ) := by
    have he : ((K : ℝ) * ((1 : ℝ) / 3)) = ((K / 3 : ℕ) : ℝ) := by
      rw [div_eq_mul_one_div] at h2; exact h2
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast, he]
  rw [h1]
  exact Nat.floor_natCast (R := ℝ) (2 ^ (K / 3) : ℕ)
theorem minFac_mul_prime (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≤ q) :
    (p * q).minFac = p := by
  have h2 : p ≤ (p * q).minFac := by
    refine (Nat.le_minFac).2 ?_ |>.resolve_left ?_
    · intro r hr hrdvd
      rcases hr.dvd_mul.1 hrdvd with h | h
      · rcases (Nat.dvd_prime hp).mp h with h' | h'
        · exact absurd h' hr.ne_one
        · omega
      · rcases (Nat.dvd_prime hq).mp h with h' | h'
        · exact absurd h' hr.ne_one
        · omega
    · intro h
      have h2 := hp.two_le
      have h3 := hq.two_le
      nlinarith
  exact le_antisymm (Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right _ _)) h2
theorem card_cen_le (n : ℕ) (hn : 1 ≤ n) : (Finset.Icc ((n + 2) / 3) (2 * n / 3)).card ≤ n := by
  have h1 : (Finset.Icc ((n + 2) / 3) (2 * n / 3)).card ≤ (Finset.range (2 * n / 3)).card := by
    apply Finset.card_le_card_of_injOn (fun u : ℕ => u - 1)
    · intro u hu
      have hu' := (Finset.mem_Icc.mp hu)
      simp only
      exact Finset.mem_range.mpr (by omega)
    · intro u hu v hv huv
      have hu' := (Finset.mem_Icc.mp hu)
      have hv' := (Finset.mem_Icc.mp hv)
      simp only at huv
      omega
  rw [Finset.card_range] at h1
  have : 3 * (2 * n / 3) ≤ 2 * n := Nat.mul_div_le (2 * n) 3
  omega

/-- The primes in the window `(11Y/10, 19Y/10]`. -/
noncomputable def win (Y : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊19 * Y / 10⌋₊) \ Nat.primesLE ⌊11 * Y / 10⌋₊

theorem mem_win' {Y : ℝ} {p : ℕ} (hp : p ∈ win Y) :
    Nat.Prime p ∧ (p : ℝ) ≤ 19 * Y / 10 ∧ 11 * Y / 10 < (p : ℝ) := by
  obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hp
  have hpm := Nat.mem_primesLE.mp h1
  refine ⟨hpm.2, ?_, ?_⟩
  · have hx0 : (0 : ℝ) < 19 * Y / 10 := by
      by_contra h
      have hf : ⌊19 * Y / 10⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      have : 2 ≤ p := hpm.2.two_le
      omega
    have hc : ((p : ℕ) : ℝ) ≤ ((⌊19 * Y / 10⌋₊ : ℕ) : ℝ) := by exact_mod_cast hpm.1
    exact hc.trans (Nat.floor_le hx0.le)
  · have h3 : ⌊11 * Y / 10⌋₊ < p := by
      by_contra hle
      exact h2 (Nat.mem_primesLE.mpr ⟨Nat.le_of_not_gt hle, hpm.2⟩)
    have hlt : 11 * Y / 10 < ((⌊11 * Y / 10⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have h5 : ((⌊11 * Y / 10⌋₊ + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt h3
    push_cast at h5
    linarith

theorem sqrt_two_pow (K : ℕ) (hK : 2 ∣ K) : Nat.sqrt (2 ^ K) = 2 ^ (K / 2) := by
  have h : 2 ^ K = (2 ^ (K / 2)) ^ 2 := by
    rw [← Nat.pow_mul]
    congr 1
    exact (Nat.div_mul_cancel hK).symm
  rw [h, Nat.sqrt_eq']

theorem even_two_pow (K : ℕ) (hK : K ≠ 0) : Even (2 ^ K) := by
  refine ⟨2 ^ (K - 1), ?_⟩
  calc
    (2 : ℕ) ^ K = 2 * 2 ^ (K - 1) := by rw [← Nat.pow_succ']; congr 1; omega
    _ = 2 ^ (K - 1) + 2 ^ (K - 1) := by ring

set_option maxHeartbeats 2000000 in
/-- **Refutation core.**  For every bound there is an even `n` beyond it for which the
one-sided count of cube-root-rough semiprimes exceeds `23/50` of the terminal sieve volume. -/
theorem refute_core (x5 : ℕ) : ∃ n, x5 ≤ n ∧ Even n ∧
    (23 / 50 : ℝ) * ((↑(Finset.Icc ((n + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * n / (3 : ℕ))).card : ℝ) * (↑n.totient : ℝ) / (↑n : ℝ) * ∏ p ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) n.sqrt) with ¬ p ∣ n, ((1 : ℝ) - (2 : ℝ) / (p : ℝ))) < (↑({u ∈ Finset.Icc ((n + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * n / (3 : ℕ)) | ⌊(↑n : ℝ) ^ (1 / 3 : ℝ)⌋₊ < u.minFac ∧ Nat.Prime u.minFac ∧ Nat.Prime (u / u.minFac)}).card : ℝ) := by
  -- abbreviations for the inlined sets
  obtain ⟨cen, hcen⟩ : ∃ cen : ℕ → Finset ℕ,
      cen = fun n => Finset.Icc ((n + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * n / (3 : ℕ)) := ⟨_, rfl⟩
  obtain ⟨semi, hsemi⟩ : ∃ semi : ℕ → Finset ℕ,
      semi = fun n => {u ∈ Finset.Icc ((n + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * n / (3 : ℕ)) | ⌊(↑n : ℝ) ^ (1 / 3 : ℝ)⌋₊ < u.minFac ∧ Nat.Prime u.minFac ∧ Nat.Prime (u / u.minFac)} := ⟨_, rfl⟩
  obtain ⟨vol, hvoldef⟩ : ∃ vol : ℕ → ℝ, vol = fun n => ((↑(Finset.Icc ((n + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * n / (3 : ℕ))).card : ℝ) * (↑n.totient : ℝ) / (↑n : ℝ) * ∏ p ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) n.sqrt) with ¬ p ∣ n, ((1 : ℝ) - (2 : ℝ) / (p : ℝ))) := ⟨_, rfl⟩
  have hcen' : ∀ m : ℕ, cen m =
      Finset.Icc ((m + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * m / (3 : ℕ)) := fun m => by rw [hcen]
  have hsemi' : ∀ m : ℕ, semi m =
      {u ∈ Finset.Icc ((m + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * m / (3 : ℕ)) |
        ⌊(↑m : ℝ) ^ (1 / 3 : ℝ)⌋₊ < u.minFac ∧ Nat.Prime u.minFac ∧ Nat.Prime (u / u.minFac)} :=
    fun m => by rw [hsemi]
  obtain ⟨A, hA⟩ := eventually_atTop.mp window_primes
  set L : ℕ := x5 + 2100 + (⌊A⌋₊ + 1) with hL
  have hL2 : 2 ≤ L := by
    have : (0 : ℕ) < L := by
      have : (0 : ℕ) < ⌊A⌋₊ + 1 := Nat.succ_pos _
      omega
    omega
  have hLbig : 2100 ≤ L := by omega
  have hLA : A < (2 ^ L : ℝ) := by
    have h1 : ((⌊A⌋₊ + 1 : ℕ) : ℝ) < ((2 ^ (⌊A⌋₊ + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_two_pow_self (n := ⌊A⌋₊ + 1)
    push_cast at h1
    have h2 : ((2 ^ (⌊A⌋₊ + 1) : ℕ) : ℝ) ≤ (2 ^ L : ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : (1 : ℕ) ≤ 2) (by omega)
    push_cast at h2
    have h3 : A < ((⌊A⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one A
    linarith
  set K : ℕ := 6 * L with hK
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = 2 ^ K := ⟨_, rfl⟩
  have hvol' : vol n = ((↑(Finset.Icc ((n + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * n / (3 : ℕ))).card : ℝ) * (↑n.totient : ℝ) / (↑n : ℝ) *
      ∏ p ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) n.sqrt) with ¬ p ∣ n,
        ((1 : ℝ) - (2 : ℝ) / (p : ℝ))) := by rw [hvoldef]
  have hK6 : 6 ∣ K := ⟨L, rfl⟩
  have hKpos : 0 < K := by omega
  have hK3 : K / 3 = 2 * L := by omega
  have hK2 : K / 2 = 3 * L := by omega
  have hn0 : 0 < n := by
    rw [hn]
    exact Nat.two_pow_pos K
  have hn1 : 1 ≤ n := hn0
  have hn20 : 20 ≤ n := by
    have h6 : 6 ≤ K := by omega
    calc
      20 ≤ 2 ^ 6 := by norm_num
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) h6
      _ = n := hn.symm
  refine ⟨n, ?_, ?_, ?_⟩
  · have h1 : x5 ≤ L := by omega
    calc
      x5 ≤ L := h1
      _ ≤ K := by omega
      _ ≤ 2 ^ K := (Nat.lt_two_pow_self (n := K)).le
      _ = n := hn.symm
  ·
    rw [hn]
    exact even_two_pow K hKpos.ne'
  · rw [← hvol', ← hsemi' n]
    -- the arithmetic facts about the chosen point
    have hlogn : Real.log n = 6 * (L : ℝ) * Real.log 2 := by
      rw [hn, hK]; push_cast; rw [Real.log_pow, Nat.cast_mul]; ring
    have hlogn0 : (0 : ℝ) < Real.log n := by rw [hlogn]; positivity
    have hs : Nat.sqrt n = 2 ^ (3 * L) := by
      rw [hn, sqrt_two_pow K (dvd_trans (by norm_num : (2 : ℕ) ∣ 6) hK6), hK2]
    have hlogs : Real.log (Nat.sqrt n : ℕ) = 3 * (L : ℝ) * Real.log 2 := by
      rw [hs]; push_cast; rw [Real.log_pow, Nat.cast_mul]; ring
    have hz : ⌊(↑n : ℝ) ^ (1 / 3 : ℝ)⌋₊ = 2 ^ (2 * L) := by
      rw [hn, cube_two_pow K hK6, hK3]
    -- (1) upper bound for the volume
    have hv1 : (((Finset.Icc ((n + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * n / (3 : ℕ))).card : ℝ)) ≤ (n : ℝ) := by
      exact_mod_cast card_cen_le n hn1
    have hv2 : ((Nat.totient n : ℝ) / (n : ℝ)) = 1 / 2 := by
      have hK1 : K = K - 1 + 1 := by omega
      rw [hn, hK1, Nat.totient_prime_pow_succ (p := 2) (n := K - 1) Nat.prime_two]
      norm_num [pow_succ]
      have hp0 : (0 : ℝ) < ((2 ^ (K - 1) : ℕ) : ℝ) := by positivity
      field_simp
    have hv3 : (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) n.sqrt) with ¬ p ∣ n,
        ((1 : ℝ) - (2 : ℝ) / (p : ℝ))) ≤ 4 / (Real.log (Nat.sqrt n : ℕ)) ^ 2 := by
      obtain ⟨T, hT⟩ : ∃ T : Finset ℕ,
          T = (Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) n.sqrt)).filter (fun p => ¬ p ∣ n) :=
        ⟨_, rfl⟩
      obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S = Nat.primesLE (Nat.sqrt n) := ⟨_, rfl⟩
      have hss : 2 ≤ Nat.sqrt n := by
        rw [hs]
        calc
          2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (3 * L) := Nat.pow_le_pow_right (by norm_num : (1 : ℕ) ≤ 2) (by omega)
      have h2S : 2 ∈ S := by
        rw [hS, Nat.mem_primesLE]
        exact ⟨hss, Nat.prime_two⟩
      have h2dvd : 2 ∣ n := by
        refine ⟨2 ^ (K - 1), ?_⟩
        have hpow : 2 ^ K = 2 ^ (K - 1 + 1) := by rw [Nat.sub_add_cancel hKpos]
        rw [hn, hpow, Nat.pow_succ']
      have h2T : 2 ∉ T := by
        intro h
        rw [hT] at h
        simp only [Finset.mem_filter] at h
        exact h.2 h2dvd
      have hTeq : T = S.erase 2 := by
        ext p
        rw [hT, hS, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Finset.mem_erase,
          Nat.mem_primesLE]
        constructor
        · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
          refine ⟨fun h2' => h4 ?_, h2, h3⟩
          rw [h2']
          exact h2dvd
        · rintro ⟨h1, h2, h3⟩
          refine ⟨⟨⟨h3.two_le, h2⟩, h3⟩, fun hdvd => ?_⟩
          rw [hn] at hdvd
          exact h1 (Nat.prime_eq_prime_of_dvd_pow h3 Nat.prime_two hdvd)
      have hp2T : ∀ p ∈ T, 2 ≤ p := by
        intro p hp
        rw [hT] at hp
        have hp' := (Finset.mem_filter.mp hp).1
        have hp'' := (Finset.mem_filter.mp hp').1
        exact (Finset.mem_Icc.mp hp'').1
      have hp2S : ∀ p ∈ S, 2 ≤ p := by
        intro p hp
        rw [hS] at hp
        exact (Nat.mem_primesLE.mp hp).2.two_le
      have hinv : ∀ p : ℕ, 2 ≤ p → ((1 : ℝ) / (p : ℝ)) ≤ 1 / 2 := fun p hp =>
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hp)
      have hinv2 : ∀ p : ℕ, 2 ≤ p → ((2 : ℝ) / (p : ℝ)) ≤ 1 := fun p hp => by
        have := hinv p hp
        have hE : (2 : ℝ) / (p : ℝ) = 2 * ((1 : ℝ) / (p : ℝ)) := by ring
        linarith
      have hsq : ∀ p : ℕ, (1 - (1 : ℝ) / (p : ℝ)) ^ 2 - (1 - (2 : ℝ) / (p : ℝ)) =
          ((1 : ℝ) / (p : ℝ)) ^ 2 := fun p => by ring
      -- the product is the full product over odd primes `≤ √n`
      have hB : (∏ p ∈ S.erase 2, ((1 : ℝ) - (2 : ℝ) / (p : ℝ))) ≤
          (∏ p ∈ S.erase 2, ((1 : ℝ) - (1 : ℝ) / (p : ℝ))) ^ 2 := by
        rw [← Finset.prod_pow]
        refine Finset.prod_le_prod₀ (f := fun p : ℕ => (1 - (2 : ℝ) / (p : ℝ)))
          (g := fun p : ℕ => (1 - (1 : ℝ) / (p : ℝ)) ^ 2) (fun p hp => ?_) (fun p hp => ?_)
        · have := hinv2 p (hp2S p ((Finset.mem_erase.mp hp).2))
          linarith
        · have := hsq p
          linarith [sq_nonneg ((1 : ℝ) / (p : ℝ))]
      have hC : (∏ p ∈ S.erase 2, ((1 : ℝ) - (1 : ℝ) / (p : ℝ))) =
          2 * (∏ p ∈ S, ((1 : ℝ) - (1 : ℝ) / (p : ℝ))) := by
        rw [← Finset.insert_erase h2S, Finset.prod_insert (Finset.notMem_erase 2 S)]
        norm_num
        ring
      have hm : (∏ p ∈ S, ((1 : ℝ) - (1 : ℝ) / (p : ℝ))) ≤ 1 / Real.log (Nat.sqrt n : ℕ) := by
        rw [hS]
        exact mertens_prod_le (Nat.sqrt n) hss
      have hnonneg : 0 ≤ ∏ p ∈ S, ((1 : ℝ) - (1 : ℝ) / (p : ℝ)) :=
        Finset.prod_nonneg (fun p hp => by
          have := hinv p (hp2S p hp)
          have := hsq p
          linarith)
      show (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) n.sqrt) with ¬ p ∣ n,
          ((1 : ℝ) - (2 : ℝ) / (p : ℝ))) ≤ _
      rw [← hT, hTeq]
      calc
        _ ≤ (∏ p ∈ S.erase 2, ((1 : ℝ) - (1 : ℝ) / (p : ℝ))) ^ 2 := hB
        _ = (2 * (∏ p ∈ S, ((1 : ℝ) - (1 : ℝ) / (p : ℝ)))) ^ 2 := by rw [hC]
        _ ≤ (2 * (1 / Real.log (Nat.sqrt n : ℕ))) ^ 2 := by
          refine pow_le_pow_left₀ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hnonneg) ?_ 2
          exact mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 2)
        _ = _ := by ring
    have hvol : (23 / 50 : ℝ) * vol n ≤ (23 / 25 : ℝ) * n / (9 * ((L : ℝ) * Real.log 2) ^ 2) := by
      rw [hvol']
      have hprod0 : (0 : ℝ) ≤ ∏ p ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) n.sqrt) with ¬ p ∣ n,
          ((1 : ℝ) - (2 : ℝ) / (p : ℝ)) := by
        apply Finset.prod_nonneg
        intro p hp
        have hp2 : 2 ≤ p :=
          (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
        have : ((2 : ℝ) / (p : ℝ)) ≤ 1 := by
          rw [div_le_one (by exact_mod_cast (show 0 < p by omega))]; exact_mod_cast hp2
        linarith
      have hstep : (((Finset.Icc ((n + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * n / (3 : ℕ))).card : ℝ) * (Nat.totient n : ℝ) / (n : ℝ)) *
          (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) n.sqrt) with ¬ p ∣ n,
            ((1 : ℝ) - (2 : ℝ) / (p : ℝ))) ≤
          (n : ℝ) * (1 / 2 : ℝ) * (4 / (Real.log (Nat.sqrt n : ℕ)) ^ 2) := by
        have h1 : (((Finset.Icc ((n + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * n / (3 : ℕ))).card : ℝ) * (Nat.totient n : ℝ) / (n : ℝ)) =
            ((Finset.Icc ((n + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * n / (3 : ℕ))).card : ℝ) * (1 / 2 : ℝ) := by
          rw [mul_div_assoc, hv2]
        rw [h1]
        have h2 : ((Finset.Icc ((n + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * n / (3 : ℕ))).card : ℝ) * (1 / 2 : ℝ) *
            (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) n.sqrt) with ¬ p ∣ n,
              ((1 : ℝ) - (2 : ℝ) / (p : ℝ))) ≤
            ((n : ℝ) * (1 / 2 : ℝ)) *
            (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) n.sqrt) with ¬ p ∣ n,
              ((1 : ℝ) - (2 : ℝ) / (p : ℝ))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hv1 (by norm_num : (0 : ℝ) ≤ 1 / 2)) hprod0
        have h3 : ((n : ℝ) * (1 / 2 : ℝ)) *
            (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) n.sqrt) with ¬ p ∣ n,
              ((1 : ℝ) - (2 : ℝ) / (p : ℝ))) ≤
            ((n : ℝ) * (1 / 2 : ℝ)) * (4 / (Real.log (Nat.sqrt n : ℕ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hv3 (mul_nonneg (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) ≤ 1 / 2))
        exact h2.trans h3
      calc
        _ = (23 / 50 : ℝ) * ((((Finset.Icc ((n + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * n / (3 : ℕ))).card : ℝ) * (Nat.totient n : ℝ) / (n : ℝ)) *
            (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) n.sqrt) with ¬ p ∣ n,
              ((1 : ℝ) - (2 : ℝ) / (p : ℝ)))) := rfl
        _ ≤ (23 / 50 : ℝ) * ((n : ℝ) * (1 / 2 : ℝ) * (4 / (Real.log (Nat.sqrt n : ℕ)) ^ 2)) :=
          mul_le_mul_of_nonneg_left hstep (by norm_num)
        _ = _ := by rw [hlogs]; ring
    -- (2) lower bound for the count
    set J : ℕ := K / 6 - 1 with hJ
    have hJL : J = L - 1 := by omega
    have hJbig : 2099 ≤ J := by omega
    obtain ⟨Y, hY⟩ : ∃ Y : ℕ → ℝ, Y = fun j => ((2 ^ (j + K / 3) : ℕ) : ℝ) := ⟨_, rfl⟩
    obtain ⟨Bp, hBp⟩ : ∃ Bp : ℕ → Finset ℕ, Bp = fun j => win (Y j) := ⟨_, rfl⟩
    obtain ⟨Bq, hBq⟩ : ∃ Bq : ℕ → Finset ℕ,
      Bq = fun (p : ℕ) => win ((n : ℝ) / (3 * (p : ℕ))) := ⟨_, rfl⟩
    -- facts about the block primes
    have hfacts : ∀ j ∈ Finset.range J, ∀ p ∈ Bp j,
        Nat.Prime p ∧ 10 * p ≤ 19 * 2 ^ (j + K / 3) ∧ 11 * 2 ^ (j + K / 3) < 10 * p ∧
          2 ^ (2 * L) < p ∧ A ≤ (n : ℝ) / (3 * (p : ℕ)) ∧
          ((2 ^ (2 * L) : ℕ) : ℝ) ≤ (n : ℝ) / (3 * (p : ℕ)) := by
      intro j hj p hp
      simp only [hBp] at hp
      obtain ⟨hpP, hp1, hp2⟩ := mem_win' hp
      have hj1 : j + K / 3 ≤ 3 * L - 2 := by
        simp only [Finset.mem_range] at hj
        omega
      have hYj : Y j = ((2 ^ (j + K / 3) : ℕ) : ℝ) := by rw [hY]
      rw [hYj, le_div_iff₀ (by norm_num : (0 : ℝ) < 10)] at hp1
      rw [hYj, div_lt_iff₀ (by norm_num : (0 : ℝ) < 10)] at hp2
      have hle : 10 * p ≤ 19 * 2 ^ (j + K / 3) := by
        have hr : ((10 * p : ℕ) : ℝ) ≤ ((19 * 2 ^ (j + K / 3) : ℕ) : ℝ) := by
          push_cast
          push_cast at hp1
          linarith
        exact_mod_cast hr
      have hgt : 11 * 2 ^ (j + K / 3) < 10 * p := by
        have hr : ((11 * 2 ^ (j + K / 3) : ℕ) : ℝ) < ((10 * p : ℕ) : ℝ) := by
          push_cast
          push_cast at hp2
          linarith
        exact_mod_cast hr
      have hcz : 2 ^ (2 * L) < p := by
        rw [hK3] at hp2
        push_cast at hp2
        have hle' : ((2 ^ (2 * L) : ℕ) : ℝ) ≤ ((2 ^ (j + 2 * L) : ℕ) : ℝ) := by
          exact_mod_cast Nat.pow_le_pow_right (by norm_num : (1 : ℕ) ≤ 2) (by omega)
        push_cast at hle'
        have hZ : (0 : ℝ) < ((2 ^ (2 * L) : ℕ) : ℝ) := by positivity
        have hr : ((2 ^ (2 * L) : ℕ) : ℝ) < ((p : ℕ) : ℝ) := by push_cast at hZ ⊢; linarith
        exact_mod_cast hr
      -- the threshold for the second window
      have hW : 57 * 2 ^ (3 * L - 2) < 10 * 2 ^ (4 * L) := by
        have hsplit : 2 ^ (4 * L) = 2 ^ (L + 2) * 2 ^ (3 * L - 2) := by
          rw [← Nat.pow_add]
          congr 1
          omega
        rw [hsplit]
        have hX : (0 : ℕ) < 2 ^ (3 * L - 2) := Nat.two_pow_pos _
        have h16 : (16 : ℕ) ≤ 2 ^ (L + 2) := by
          calc
            (16 : ℕ) = 2 ^ 4 := by norm_num
            _ ≤ 2 ^ (L + 2) := Nat.pow_le_pow_right (by norm_num : (1 : ℕ) ≤ 2) (by omega)
        calc
          57 * 2 ^ (3 * L - 2) < 160 * 2 ^ (3 * L - 2) := by omega
          _ = 10 * 16 * 2 ^ (3 * L - 2) := by ring
          _ ≤ 10 * 2 ^ (L + 2) * 2 ^ (3 * L - 2) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 10 h16) (le_refl _)
          _ = 10 * (2 ^ (L + 2) * 2 ^ (3 * L - 2)) := by ring
      have hle2 : 30 * p ≤ 57 * 2 ^ (3 * L - 2) := by
        calc
          30 * p = 3 * (10 * p) := by ring
          _ ≤ 3 * (19 * 2 ^ (3 * L - 2)) :=
            Nat.mul_le_mul_left 3
              (hle.trans (Nat.mul_le_mul_left 19 (Nat.pow_le_pow_right (by norm_num : (1 : ℕ) ≤ 2) hj1)))
          _ = 57 * 2 ^ (3 * L - 2) := by ring
      have h3p : 3 * p < 2 ^ (4 * L) := by omega
      have h3p' : ((3 * p : ℕ) : ℝ) < ((2 ^ (4 * L) : ℕ) : ℝ) := by exact_mod_cast h3p
      have hy : ((2 ^ (2 * L) : ℕ) : ℝ) ≤ (n : ℝ) / (3 * (p : ℕ)) := by
        rw [le_div_iff₀ (by
          have h1 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hpP.pos
          positivity : (0 : ℝ) < 3 * ((p : ℕ) : ℝ))]
        have hnn : ((2 ^ (6 * L) : ℕ) : ℝ) = ((2 ^ (4 * L) : ℕ) : ℝ) * ((2 ^ (2 * L) : ℕ) : ℝ) := by
          rw [← Nat.cast_mul, ← Nat.pow_add]
          congr 1
          ring
        rw [hn, hnn]
        have hle' : ((2 ^ (2 * L) : ℕ) : ℝ) * ((3 * p : ℕ) : ℝ) ≤
            ((2 ^ (2 * L) : ℕ) : ℝ) * ((2 ^ (4 * L) : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left h3p'.le (by positivity)
        simpa [mul_comm] using hle'
      have hA2 : A ≤ (n : ℝ) / (3 * (p : ℕ)) := by
        calc
          A ≤ ((2 ^ (2 * L) : ℕ) : ℝ) := hLA.le.trans (by
            exact_mod_cast Nat.pow_le_pow_right (by norm_num : (1 : ℕ) ≤ 2) (by omega))
          _ ≤ (n : ℝ) / (3 * (p : ℕ)) := hy
      exact ⟨hpP, hle, hgt, hcz, hA2, hy⟩
    -- membership of the products
    have hmem : ∀ j ∈ Finset.range J, ∀ p ∈ Bp j, ∀ q ∈ Bq p,
        p * q ∈ semi n ∧ (p * q).minFac = p ∧ p < q := by
      intro j hj p hp q hq
      obtain ⟨hpP, hle, hgt, hcz, hA2, hyv⟩ := hfacts j hj p hp
      simp only [hBq] at hq
      obtain ⟨hqP, hq1, hq2⟩ := mem_win' hq
      have hj1 : j + K / 3 ≤ 3 * L - 2 := by
        simp only [Finset.mem_range] at hj
        omega
      have hpne : ((p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpP.ne_zero
      have h3p : (0 : ℝ) < 3 * (p : ℝ) := by positivity
      have hy : ((n : ℝ) / (3 * (p : ℝ))) * (3 * (p : ℝ)) = (n : ℝ) := by field_simp
      have hqle : 30 * p * q ≤ 19 * n := by
        have hq1' := (le_div_iff₀ (c := (10 : ℝ)) (by norm_num : (0 : ℝ) < 10)).mp hq1
        have hm := mul_le_mul_of_nonneg_right hq1' h3p.le
        rw [mul_assoc (19 : ℝ) _ _, hy] at hm
        have hr : ((30 * p * q : ℕ) : ℝ) ≤ ((19 * n : ℕ) : ℝ) := by
          calc
            ((30 * p * q : ℕ) : ℝ) = ((q : ℕ) : ℝ) * 10 * (3 * ((p : ℕ) : ℝ)) := by push_cast; ring
            _ ≤ ((19 : ℕ) : ℝ) * ((n : ℕ) : ℝ) := hm
            _ = _ := by push_cast; ring
        exact_mod_cast hr
      have hqgt : 11 * n < 30 * p * q := by
        have hq2' := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 10)).mp hq2
        have hm := mul_lt_mul_of_pos_right hq2' h3p
        rw [mul_assoc (11 : ℝ) _ _, hy] at hm
        have hr : ((11 * n : ℕ) : ℝ) < ((30 * p * q : ℕ) : ℝ) := by
          calc
            ((11 * n : ℕ) : ℝ) = ((11 : ℕ) : ℝ) * ((n : ℕ) : ℝ) := by push_cast; ring
            _ < ((q : ℕ) : ℝ) * 10 * (3 * ((p : ℕ) : ℝ)) := hm
            _ = _ := by push_cast; ring
        exact_mod_cast hr
      have hple2 : 10 * p ≤ 19 * 2 ^ (3 * L - 2) :=
        hle.trans (Nat.mul_le_mul_left 19 (Nat.pow_le_pow_right (by norm_num : (1 : ℕ) ≤ 2) hj1))
      have hqp : p < q := by
        by_contra hle'
        have hqle2 : q ≤ p := Nat.le_of_not_gt hle'
        obtain ⟨X, hX⟩ : ∃ X : ℕ, X = 2 ^ (6 * L - 4) := ⟨_, rfl⟩
        have hXpos : 0 < X := by
          rw [hX]
          exact Nat.two_pow_pos _
        have hXn : 16 * X = n := by
          rw [hX, hn]
          calc
            (16 : ℕ) * 2 ^ (6 * L - 4) = 2 ^ (4 + (6 * L - 4)) := by
              rw [show (16 : ℕ) = 2 ^ 4 from by norm_num, ← Nat.pow_add]
            _ = 2 ^ (6 * L) := by
              have h : 4 + (6 * L - 4) = 6 * L := by omega
              rw [h]
            _ = 2 ^ K := by rw [hK]
        have hsq : 100 * (p * p) ≤ 361 * X := by
          rw [hX]
          calc
            100 * (p * p) = (10 * p) * (10 * p) := by ring
            _ ≤ 19 * 2 ^ (3 * L - 2) * (19 * 2 ^ (3 * L - 2)) := Nat.mul_le_mul hple2 hple2
            _ = 361 * (2 ^ (3 * L - 2) * 2 ^ (3 * L - 2)) := by ring
            _ = 361 * 2 ^ ((3 * L - 2) + (3 * L - 2)) := by rw [← Nat.pow_add]
            _ = 361 * 2 ^ (6 * L - 4) := by
              have h : (3 * L - 2) + (3 * L - 2) = 6 * L - 4 := by omega
              rw [h]
        have h1 : 3000 * (p * q) ≤ 3000 * (p * p) := by gcongr
        have h2 : 3000 * (p * p) ≤ 10830 * X := by
          calc
            3000 * (p * p) = 30 * (100 * (p * p)) := by ring
            _ ≤ 30 * (361 * X) := Nat.mul_le_mul_left 30 hsq
            _ = 10830 * X := by ring
        have h3 : 1100 * n < 3000 * (p * q) := by linarith [hqgt]
        rw [← hXn] at h3
        have h4 : 1100 * (16 * X) < 10830 * X := h3.trans_le (h1.trans h2)
        have h5 : (1100 * 16) * X = 1100 * (16 * X) := by ring
        rw [← h5] at h4
        have h6 : 10830 * X ≤ 17600 * X := Nat.mul_le_mul_right X (by norm_num : (10830 : ℕ) ≤ 17600)
        omega
      have hqle' : 10 * (3 * (p * q)) ≤ 19 * n := by
        rw [show 10 * (3 * (p * q)) = 30 * p * q from by ring]
        exact hqle
      have hqgt' : 11 * n < 10 * (3 * (p * q)) := by
        rw [show 10 * (3 * (p * q)) = 30 * p * q from by ring]
        exact hqgt
      obtain ⟨v, hv⟩ : ∃ v : ℕ, v = 3 * (p * q) := ⟨_, rfl⟩
      rw [← hv] at hqle' hqgt'
      have hlo : n + 2 ≤ v := by omega
      have hhi : v ≤ 2 * n := by omega
      rw [hv] at hlo hhi
      have hmf : (p * q).minFac = p := minFac_mul_prime p q hpP hqP hqp.le
      refine ⟨?_, hmf, hqp⟩
      show p * q ∈ semi n
      rw [hsemi']
      rw [Finset.mem_filter, hz]
      refine ⟨?_, ?_, ?_, ?_⟩
      · have hmem1 : (n + 2) / 3 ≤ p * q := by
          have h1 : (n + 2) / 3 ≤ 3 * (p * q) / 3 := Nat.div_le_div_right hlo
          rwa [Nat.mul_div_cancel_left _ (by omega : (0 : ℕ) < 3)] at h1
        have hmem2 : p * q ≤ 2 * n / 3 :=
          (Nat.le_div_iff_mul_le (k := 3) (by omega)).mpr (by simpa [mul_comm] using hhi)
        exact Finset.mem_Icc.mpr ⟨hmem1, hmem2⟩
      · rw [hmf]; exact hcz
      · rw [hmf]; exact hpP
      · rw [hmf, Nat.mul_div_cancel_left q hpP.pos]; exact hqP
    -- distinct blocks have disjoint prime sets
    have hdisj : ∀ j ∈ Finset.range J, ∀ j' ∈ Finset.range J, ∀ p ∈ Bp j, ∀ p' ∈ Bp j',
        p = p' → j = j' := by
      intro j hj j' hj' p hp p' hp' hpp
      obtain ⟨hpP, hle, hgt, hcz, hA2, hyv⟩ := hfacts j hj p hp
      obtain ⟨hpP', hle', hgt', hcz', hA2'⟩ := hfacts j' hj' p' hp'
      rw [hpp] at hle hgt
      simp only [Finset.mem_range] at hj hj'
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have hX : (0 : ℕ) < 2 ^ (j + K / 3) := Nat.two_pow_pos _
        have hX' : (0 : ℕ) < 2 ^ (j' + K / 3) := Nat.two_pow_pos _
        have hpow : 2 * 2 ^ (j + K / 3) ≤ 2 ^ (j' + K / 3) := by
          calc
            2 * 2 ^ (j + K / 3) = 2 ^ ((j + K / 3) + 1) := by rw [Nat.pow_succ]; ring
            _ ≤ 2 ^ (j' + K / 3) := Nat.pow_le_pow_right (by norm_num : (1 : ℕ) ≤ 2) (by omega)
        omega
      · have hX : (0 : ℕ) < 2 ^ (j + K / 3) := Nat.two_pow_pos _
        have hX' : (0 : ℕ) < 2 ^ (j' + K / 3) := Nat.two_pow_pos _
        have hpow : 2 * 2 ^ (j' + K / 3) ≤ 2 ^ (j + K / 3) := by
          calc
            2 * 2 ^ (j' + K / 3) = 2 ^ ((j' + K / 3) + 1) := by rw [Nat.pow_succ]; ring
            _ ≤ 2 ^ (j + K / 3) := Nat.pow_le_pow_right (by norm_num : (1 : ℕ) ≤ 2) (by omega)
        omega
    -- the injection
    have hcard1 : ((Finset.range J).sigma (fun j => (Bp j).sigma (fun p => Bq p))).card ≤
        (semi n).card := by
      refine Finset.card_le_card_of_injOn (fun x : Σ _ : ℕ, Σ _ : ℕ, ℕ => x.2.1 * x.2.2) ?_ ?_
      · rintro ⟨j, p, q⟩ hj
        have hj1 := Finset.mem_sigma.mp hj
        have hj2 := Finset.mem_sigma.mp hj1.2
        exact (hmem j hj1.1 p hj2.1 q hj2.2).1
      · rintro ⟨j, p, q⟩ hj ⟨j', p', q'⟩ hj' heq
        have hj1 := Finset.mem_sigma.mp hj
        have hj2 := Finset.mem_sigma.mp hj1.2
        have hj'1 := Finset.mem_sigma.mp hj'
        have hj'2 := Finset.mem_sigma.mp hj'1.2
        have h1 := (hmem j hj1.1 p hj2.1 q hj2.2).2.1
        have h2 := (hmem j' hj'1.1 p' hj'2.1 q' hj'2.2).2.1
        simp only at heq
        have heq' : (p * q).minFac = (p' * q').minFac := by rw [heq]
        rw [h1, h2] at heq'
        have hp_eq : p = p' := heq'
        have hq_eq : q = q' := by
          have h : p * q = p * q' := by rw [heq, hp_eq]
          have hpP : Nat.Prime p := (hfacts j hj1.1 p hj2.1).1
          exact Nat.eq_of_mul_eq_mul_left hpP.pos h
        have hjj : j = j' := hdisj j hj1.1 j' hj'1.1 p hj2.1 p' hj'2.1 hp_eq
        simp only [hjj, hp_eq, hq_eq]
    -- per-block bounds
    have hb : ∀ j ∈ Finset.range J, (10 / 912 : ℝ) * (n : ℝ) / (Real.log n) ^ 2 ≤
        ∑ p ∈ Bp j, ((Bq p).card : ℝ) := by
      intro j hj
      have hYj : Y j = ((2 ^ (j + K / 3) : ℕ) : ℝ) := by rw [hY]
      simp only [Finset.mem_range] at hj
      have hY1 : (1 : ℝ) < Y j := by
        rw [hYj]
        have h2 : (2 : ℕ) ≤ 2 ^ (j + K / 3) := by
          calc
            2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (j + K / 3) := Nat.pow_le_pow_right (by norm_num : (1 : ℕ) ≤ 2) (by omega)
        exact_mod_cast h2
      have hYn : Y j ≤ (n : ℝ) := by
        rw [hYj, hn]
        exact_mod_cast Nat.pow_le_pow_right (by norm_num : (1 : ℕ) ≤ 2) (by omega)
      have hlogY : Real.log (Y j) ≤ Real.log n :=
        Real.log_le_log (lt_trans zero_lt_one hY1) hYn
      have hlogY0 : (0 : ℝ) < Real.log (Y j) := Real.log_pos (by linarith)
      have hA1 : A ≤ Y j := by
        rw [hYj]
        have hle : (2 ^ L : ℕ) ≤ 2 ^ (j + K / 3) := by
          rw [hK3]
          exact Nat.pow_le_pow_right (by norm_num : (1 : ℕ) ≤ 2) (by omega)
        exact hLA.le.trans (by exact_mod_cast hle)
      have hc1 : Y j / (4 * Real.log n) ≤ ((Bp j).card : ℝ) := by
        have h := hA (Y j) hA1
        rw [hBp]
        have h2 : Y j / (4 * Real.log n) ≤ Y j / (4 * Real.log (Y j)) :=
          div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
        exact h2.trans h
      have hc2 : ∀ p ∈ Bp j, ((10 / 57 : ℝ) * ((n : ℝ) / Y j)) / (4 * Real.log n) ≤
          ((Bq p).card : ℝ) := by
        intro p hp
        obtain ⟨hpP, hle, hgt, hcz, hA2, hyv⟩ := hfacts j (Finset.mem_range.mpr hj) p hp
        have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpP.pos
        have h := hA ((n : ℝ) / (3 * (p : ℕ))) hA2
        rw [hBq]
        have hp1 : (3 * (p : ℝ)) ≤ (57 / 10 : ℝ) * Y j := by
          simp only [hBp] at hp
          have hw := mem_win' hp
          have hw' := (le_div_iff₀ (c := (10 : ℝ)) (by norm_num : (0 : ℝ) < 10)).mp hw.2.1
          have hring : (57 / 10 : ℝ) * Y j = (3 / 10 : ℝ) * (19 * Y j) := by ring
          rw [hring]
          have hm := mul_le_mul_of_nonneg_left hw' (by norm_num : (0 : ℝ) ≤ 3 / 10)
          have hring2 : (3 : ℝ) * ((p : ℕ) : ℝ) = (3 / 10 : ℝ) * (((p : ℕ) : ℝ) * 10) := by ring
          rw [hring2]
          exact hm
        have hyvR : (2 : ℝ) ^ (2 * L) ≤ (n : ℝ) / (3 * (p : ℝ)) := by
          have h := hyv
          push_cast at h
          exact h
        have hyv' : ((10 / 57 : ℝ) * ((n : ℝ) / Y j)) ≤ (n : ℝ) / (3 * (p : ℝ)) := by
          have h1 : (n : ℝ) / ((57 / 10 : ℝ) * Y j) ≤ (n : ℝ) / (3 * (p : ℝ)) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hp1
          have h2 : (10 / 57 : ℝ) * ((n : ℝ) / Y j) = (n : ℝ) / ((57 / 10 : ℝ) * Y j) := by
            field_simp
          calc
            ((10 / 57 : ℝ) * ((n : ℝ) / Y j)) = (n : ℝ) / ((57 / 10 : ℝ) * Y j) := h2
            _ ≤ _ := h1
        have hyv0 : (0 : ℝ) < (n : ℝ) / (3 * (p : ℝ)) := by positivity
        have hlogyv : Real.log ((n : ℝ) / (3 * (p : ℝ))) ≤ Real.log n := by
          refine Real.log_le_log hyv0 ?_
          rw [div_le_iff₀ (by positivity)]
          calc
            (n : ℝ) = (n : ℝ) * 1 := by ring
            _ ≤ (n : ℝ) * (3 * (p : ℝ)) := by
              refine mul_le_mul_of_nonneg_left (by
                have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpP.pos
                linarith) (Nat.cast_nonneg n)
        have hlogyv0 : (0 : ℝ) < Real.log ((n : ℝ) / (3 * (p : ℝ))) := by
          refine Real.log_pos ?_
          have hbig : (16 : ℝ) ≤ (2 : ℝ) ^ (2 * L) := by
            have : (16 : ℕ) ≤ 2 ^ (2 * L) := by
              calc
                (16 : ℕ) = 2 ^ 4 := by norm_num
                _ ≤ 2 ^ (2 * L) := Nat.pow_le_pow_right (by norm_num : (1 : ℕ) ≤ 2) (by omega)
            exact_mod_cast this
          linarith
        calc
          ((10 / 57 : ℝ) * ((n : ℝ) / Y j)) / (4 * Real.log n)
              ≤ ((n : ℝ) / (3 * (p : ℝ))) / (4 * Real.log n) :=
            div_le_div_of_nonneg_right hyv' (by linarith)
          _ ≤ ((n : ℝ) / (3 * (p : ℝ))) / (4 * Real.log ((n : ℝ) / (3 * (p : ℝ)))) :=
            div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
          _ ≤ _ := h
      have hc3 : (((Bp j).card : ℝ) * (((10 / 57 : ℝ) * ((n : ℝ) / Y j)) / (4 * Real.log n))) ≤
          ∑ p ∈ Bp j, ((Bq p).card : ℝ) := by
        have heq : ((Bp j).card : ℝ) * (((10 / 57 : ℝ) * ((n : ℝ) / Y j)) / (4 * Real.log n)) =
            ∑ _p ∈ Bp j, ((10 / 57 : ℝ) * ((n : ℝ) / Y j)) / (4 * Real.log n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        rw [heq]
        exact Finset.sum_le_sum
          (f := fun _p : ℕ => ((10 / 57 : ℝ) * ((n : ℝ) / Y j)) / (4 * Real.log n))
          (g := fun p : ℕ => ((Bq p).card : ℝ)) (fun p hp => hc2 p hp)
      have hlast : (10 / 912 : ℝ) * (n : ℝ) / (Real.log n) ^ 2 =
          (Y j / (4 * Real.log n)) * (((10 / 57 : ℝ) * ((n : ℝ) / Y j)) / (4 * Real.log n)) := by
        have hY0 : (0 : ℝ) < Y j := by linarith
        field_simp
          [hlogn0.ne', show (Real.log n) ^ 2 = (Real.log n) * (Real.log n) by ring]
        ring
      rw [hlast]
      exact (mul_le_mul_of_nonneg_right hc1 (by positivity)).trans hc3
    have htotal : ((J : ℕ) : ℝ) * ((10 / 912 : ℝ) * (n : ℝ) / (Real.log n) ^ 2) ≤
        ((semi n).card : ℝ) := by
      have hcs : ((Finset.range J).sigma (fun j => (Bp j).sigma (fun p => Bq p))).card =
          ∑ j ∈ Finset.range J, ∑ p ∈ Bp j, (Bq p).card := by
        rw [Finset.card_sigma]
        exact Finset.sum_congr rfl (fun j _ => Finset.card_sigma _ _)
      calc
        ((J : ℕ) : ℝ) * ((10 / 912 : ℝ) * (n : ℝ) / (Real.log n) ^ 2) =
            ∑ _j ∈ Finset.range J, (10 / 912 : ℝ) * (n : ℝ) / (Real.log n) ^ 2 := by
              rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
        _ ≤ ∑ j ∈ Finset.range J, ∑ p ∈ Bp j, ((Bq p).card : ℝ) :=
          Finset.sum_le_sum (fun j hj => hb j hj)
        _ = ((Finset.range J).sigma (fun j => (Bp j).sigma (fun p => Bq p))).card := by
          rw [hcs]
          push_cast
          exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun p _ => rfl))
        _ ≤ ((semi n).card : ℕ) := by exact_mod_cast hcard1
    -- final comparison
    have hkey : (23 / 25 : ℝ) * (n : ℝ) / (9 * ((L : ℝ) * Real.log 2) ^ 2) <
        ((J : ℕ) : ℝ) * ((10 / 912 : ℝ) * (n : ℝ) / (Real.log n) ^ 2) := by
      have hlogn' : (Real.log n) ^ 2 = 36 * ((L : ℝ) * Real.log 2) ^ 2 := by
        rw [hlogn]; ring
      rw [hlogn']
      have hrhs : ((J : ℕ) : ℝ) * ((10 / 912 : ℝ) * (n : ℝ) / (36 * ((L : ℝ) * Real.log 2) ^ 2)) =
          ((J : ℕ) : ℝ) * (10 / 912 : ℝ) * (n : ℝ) / (36 * ((L : ℝ) * Real.log 2) ^ 2) := by ring
      rw [hrhs, div_lt_div_iff₀ (by positivity : (0 : ℝ) < 9 * ((L : ℝ) * Real.log 2) ^ 2)
        (by positivity : (0 : ℝ) < 36 * ((L : ℝ) * Real.log 2) ^ 2)]
      have hJ : (400 : ℝ) ≤ ((J : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 400 ≤ J)
      have hpos : (0 : ℝ) < (n : ℝ) * ((L : ℝ) * Real.log 2) ^ 2 := by positivity
      have h1 : (23 / 25 : ℝ) * 36 < ((10 : ℝ) / 912) * 9 * (400 : ℝ) := by norm_num
      have h2 : ((10 : ℝ) / 912) * 9 * (400 : ℝ) ≤ ((10 : ℝ) / 912) * 9 * ((J : ℕ) : ℝ) := by
        exact mul_le_mul_of_nonneg_left hJ (by positivity)
      have h3 : ((J : ℕ) : ℝ) * (10 / 912 : ℝ) * 9 = ((10 : ℝ) / 912) * 9 * ((J : ℕ) : ℝ) := by ring
      have hlt : (23 / 25 : ℝ) * 36 < ((J : ℕ) : ℝ) * (10 / 912 : ℝ) * 9 := by rw [h3]; exact h1.trans_le h2
      have hmul := mul_lt_mul_of_pos_right hlt hpos
      have heq1 : ((23 / 25 : ℝ) * (n : ℝ)) * (36 * ((L : ℝ) * Real.log 2) ^ 2) =
          ((23 / 25 : ℝ) * 36) * ((n : ℝ) * ((L : ℝ) * Real.log 2) ^ 2) := by ring
      have heq3 : (((J : ℕ) : ℝ) * (10 / 912 : ℝ) * (n : ℝ)) * (9 * ((L : ℝ) * Real.log 2) ^ 2) =
          (((J : ℕ) : ℝ) * (10 / 912 : ℝ) * 9) * ((n : ℝ) * ((L : ℝ) * Real.log 2) ^ 2) := by ring
      rw [heq1]
      rw [heq3]
      exact hmul
    exact hvol.trans_lt (hkey.trans_le htotal)

end GoldbachRefute6808
/-- The frozen cut statement fails: along powers of two the one-sided count of cube-root-rough
semiprimes grows like a constant times `n / log n`, while the terminal sieve volume is of order
`n / (log n)²`. -/
theorem Conjectures.Cuts.Refute25dd470ddb6f861c24eaee19 : ¬ (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → ℕ := fun (x2 : ℕ) => ⌊(↑x2 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x3 : ℕ → Finset ℕ := fun (x3 : ℕ) => {x4 ∈ x1 x3 | x2 x3 < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)}; have x4 : ℕ → ℝ := fun (x4 : ℕ) => (↑(x1 x4).card : ℝ) * (↑x4.totient : ℝ) / (↑x4 : ℝ) * ∏ x5 ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) x4.sqrt) with ¬x5 ∣ x4, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ)); ∃ (x5 : ℕ), ∀ (x6 : ℕ), x5 ≤ x6 → Even x6 → (↑(x3 x6).card : ℝ) ≤ (23 / 50 : ℝ) * x4 x6) := by
  intro h
  obtain ⟨x5, h5⟩ := h
  obtain ⟨n, hn, hE, hlt⟩ := GoldbachRefute6808.refute_core x5
  have h5' := h5 n hn hE
  simp only [] at h5'
  exact absurd h5' (not_le_of_gt hlt)