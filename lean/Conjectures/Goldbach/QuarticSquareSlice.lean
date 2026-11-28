import Mathlib

/-!
A diagonal-scale fourth-power triple-collision bound on slices of fixed square-sum
defect.

For a finite set `A` of positive integers below `M` and an integer `h`, the number
of pairs of triples `x, y : Fin 3 -> A` with equal sum of fourth powers and with
the difference of the sums of squares equal to `h` is at most `C M^eps |A|^3`.

Method.  For fixed `x`, the triple `y` has prescribed sum of squares `s` and sum
of fourth powers `q`, so `u = y 0 ^ 2` and `t = y 1 * y 2` satisfy
`(2u - s - 2t) (2u - s + 2t) = 2q - s^2`; this injects the solutions, up to the
symmetry `y 1 <-> y 2`, into the divisors of `2q - s^2`, and `d(n) <= C n^eps`
(`divisor_bound`).  The degenerate slice `2q = s^2` is exactly the Heron locus,
where one coordinate is the sum of the other two; there the pairs are counted
directly: there are at most `3 |A|^2` degenerate triples, and at most `3 |A|` of
them with a prescribed sum of squares.
-/

namespace Conjectures.Goldbach.QuarticSquareSlice_aux

def W (A : Finset ℕ) (k : ℕ) (x : Fin 3 → ↥A) : ℤ := ∑ i, ((x i : ℕ) : ℤ)^k

/-- For `a > 1` and `e : ℕ`, `e + 1 ≤ C * a ^ e` with `C = max 1 (1 / (a - 1))`. -/
private lemma succ_le_mul_pow {a : ℝ} (ha : 1 < a) (e : ℕ) :
    (e + 1 : ℝ) ≤ max 1 (1 / (a - 1)) * a ^ e := by
  have ht : 0 < a - 1 := by linarith
  have h1 : 1 + (e : ℝ) * (a - 1) ≤ a ^ e := by
    have := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ a - 1) e
    simpa [add_sub_cancel] using this
  have hC1 : 1 ≤ max 1 (1 / (a - 1)) := le_max_left _ _
  have hCt : 1 ≤ max 1 (1 / (a - 1)) * (a - 1) :=
    (div_le_iff₀ ht).mp (le_max_right _ _)
  have he : (e : ℝ) ≤ max 1 (1 / (a - 1)) * (a - 1) * (e : ℝ) := by
    have := mul_le_mul_of_nonneg_right hCt (Nat.cast_nonneg e)
    linarith
  calc (e + 1 : ℝ) ≤ max 1 (1 / (a - 1)) + max 1 (1 / (a - 1)) * (a - 1) * (e : ℝ) := by
        linarith
    _ = max 1 (1 / (a - 1)) * (1 + (e : ℝ) * (a - 1)) := by ring
    _ ≤ max 1 (1 / (a - 1)) * a ^ e :=
        mul_le_mul_of_nonneg_left h1 (le_trans zero_le_one hC1)

/-- `e + 1 ≤ 2 ^ e` for `e : ℕ`. -/
private lemma succ_le_two_pow (e : ℕ) : (e + 1 : ℝ) ≤ (2 : ℝ) ^ e := by
  calc (e + 1 : ℝ) = 1 + (e : ℝ) * 1 := by ring
    _ ≤ (1 + 1 : ℝ) ^ e := one_add_mul_le_pow (by norm_num) e
    _ = (2 : ℝ) ^ e := by norm_num

theorem divisor_bound : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ)^ε := by
  intro ε hε
  classical
  have ha : 1 < (2 : ℝ) ^ ε := Real.one_lt_rpow (by norm_num) hε
  have hC0ex : ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ e : ℕ, (e + 1 : ℝ) ≤ C0 * ((2 : ℝ) ^ ε) ^ e :=
    ⟨max 1 (1 / ((2 : ℝ) ^ ε - 1)), le_max_left _ _, fun e => succ_le_mul_pow ha e⟩
  obtain ⟨C0, hC0, hC0e⟩ := hC0ex
  set P : ℕ := ⌈(2 : ℝ) ^ (ε⁻¹)⌉₊
  refine ⟨C0 ^ P, pow_pos (lt_of_lt_of_le zero_lt_one hC0) P, ?_⟩
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Nat.divisors_zero, Real.zero_rpow hε.ne']
  have hcard : (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.card_divisors hn
  have hper : ∀ p ∈ n.primeFactors,
      ((n.factorization p + 1 : ℕ) : ℝ) ≤
        (if (p : ℝ) ^ ε < 2 then C0 else 1) * ((p : ℝ) ^ ε) ^ n.factorization p := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hpa : (2 : ℝ) ^ ε ≤ (p : ℝ) ^ ε :=
      Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp2) hε.le
    by_cases h : (p : ℝ) ^ ε < 2
    · simp only [h, ↓reduceIte]
      have h1 := hC0e (n.factorization p)
      have h2 : ((2 : ℝ) ^ ε) ^ n.factorization p ≤ ((p : ℝ) ^ ε) ^ n.factorization p :=
        pow_le_pow_left₀ (le_trans zero_le_one ha.le) hpa _
      simpa using h1.trans (mul_le_mul_of_nonneg_left h2 (le_trans zero_le_one hC0))
    · simp only [h, ↓reduceIte, one_mul]
      have h2 : (2 : ℝ) ^ n.factorization p ≤ ((p : ℝ) ^ ε) ^ n.factorization p :=
        pow_le_pow_left₀ (by norm_num) (le_of_not_gt h) _
      simpa using (succ_le_two_pow (n.factorization p)).trans h2
  have h1 : (n.divisors.card : ℝ) ≤
      ∏ p ∈ n.primeFactors,
        ((if (p : ℝ) ^ ε < 2 then C0 else 1) * ((p : ℝ) ^ ε) ^ n.factorization p) := by
    rw [hcard]
    exact Finset.prod_le_prod₀ (fun p _ => Nat.cast_nonneg _) hper
  have h2 : ∏ p ∈ n.primeFactors, (if (p : ℝ) ^ ε < 2 then C0 else 1) ≤ C0 ^ P := by
    rw [← Finset.prod_filter, Finset.prod_const]
    refine pow_le_pow_right₀ hC0 ?_
    have hsub : n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ ε < 2) ⊆ Finset.range P := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Finset.mem_range]
      have hlt : (p : ℝ) < (2 : ℝ) ^ (ε⁻¹) :=
        (Real.lt_rpow_inv_iff_of_pos (Nat.cast_nonneg p) (by norm_num : (0 : ℝ) ≤ 2) hε).mpr hp.2
      exact Nat.lt_ceil.mpr hlt
    exact (Finset.card_le_card hsub).trans (le_of_eq (Finset.card_range P))
  have h3 : ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ n.factorization p = (n : ℝ) ^ ε := by
    have hcongr : ∀ p ∈ n.primeFactors,
        ((p : ℝ) ^ ε) ^ n.factorization p = ((p : ℝ) ^ n.factorization p) ^ ε := by
      intro p hp
      have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
      rw [← Real.rpow_natCast ((p : ℝ) ^ ε) (n.factorization p),
        ← Real.rpow_mul hp0 ε (n.factorization p : ℝ),
        ← Real.rpow_natCast (p : ℝ) (n.factorization p),
        ← Real.rpow_mul hp0 (n.factorization p : ℝ) ε, mul_comm]
    rw [Finset.prod_congr rfl hcongr, Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
    have hnprod : ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p = (n : ℝ) := by
      exact_mod_cast Nat.prod_factorization_pow_eq_self hn
    rw [hnprod]
  rw [Finset.prod_mul_distrib, h3] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right h2 ?_)
  exact Real.rpow_nonneg (Nat.cast_nonneg n) ε


private def a (A : Finset ℕ) (x : Fin 3 → ↥A) : ℤ := ((x 0 : ℕ) : ℤ)
private def b (A : Finset ℕ) (x : Fin 3 → ↥A) : ℤ := ((x 1 : ℕ) : ℤ)
private def c (A : Finset ℕ) (x : Fin 3 → ↥A) : ℤ := ((x 2 : ℕ) : ℤ)

private lemma a_nonneg (A : Finset ℕ) (x : Fin 3 → ↥A) : 0 ≤ a A x := Int.natCast_nonneg _
private lemma b_nonneg (A : Finset ℕ) (x : Fin 3 → ↥A) : 0 ≤ b A x := Int.natCast_nonneg _
private lemma c_nonneg (A : Finset ℕ) (x : Fin 3 → ↥A) : 0 ≤ c A x := Int.natCast_nonneg _

private lemma W_two (A : Finset ℕ) (x : Fin 3 → ↥A) :
    W A 2 x = a A x ^ 2 + b A x ^ 2 + c A x ^ 2 := by
  simp [W, a, b, c, Fin.sum_univ_three]

private lemma W_four (A : Finset ℕ) (x : Fin 3 → ↥A) :
    W A 4 x = a A x ^ 4 + b A x ^ 4 + c A x ^ 4 := by
  simp [W, a, b, c, Fin.sum_univ_three]

private def d1 (A : Finset ℕ) (s : ℤ) (x : Fin 3 → ↥A) : ℤ :=
  2 * a A x ^ 2 - s - 2 * b A x * c A x

private def d2 (A : Finset ℕ) (s : ℤ) (x : Fin 3 → ↥A) : ℤ :=
  2 * a A x ^ 2 - s + 2 * b A x * c A x

private lemma d1_mul_d2 (A : Finset ℕ) (s q : ℤ) (x : Fin 3 → ↥A)
    (h2 : W A 2 x = s) (h4 : W A 4 x = q) :
    d1 A s x * d2 A s x = 2 * q - s ^ 2 := by
  rw [W_two] at h2
  rw [W_four] at h4
  simp only [d1, d2]
  rw [← h2, ← h4]
  ring

private lemma int_eq_of_natAbs_eq {u v : ℤ} (h1 : u.natAbs = v.natAbs)
    (h2 : decide (0 ≤ u) = decide (0 ≤ v)) : u = v := by
  have h2' : (0 ≤ u) ↔ (0 ≤ v) := decide_eq_decide.mp h2
  rcases le_total 0 u with hu | hu
  · rcases le_total 0 v with hv | hv
    · rw [← Int.natAbs_of_nonneg hu, ← Int.natAbs_of_nonneg hv, h1]
    · have hv0 : v = 0 := le_antisymm hv (h2'.mp hu)
      have hu0 : u = 0 := by rw [← Int.natAbs_of_nonneg hu, h1, hv0]; simp
      linarith
  · rcases le_total 0 v with hv | hv
    · have hu0 : u = 0 := le_antisymm hu (h2'.mpr hv)
      have hv0 : v = 0 := by rw [← Int.natAbs_of_nonneg hv, ← h1, hu0]; simp
      linarith
    · have hu' : 0 ≤ -u := by linarith
      have hv' : 0 ≤ -v := by linarith
      have h3 : (-u).natAbs = (-v).natAbs := by rw [Int.natAbs_neg, Int.natAbs_neg, h1]
      have h4 : -u = -v := by
        rw [← Int.natAbs_of_nonneg hu', ← Int.natAbs_of_nonneg hv', h3]
      linarith

private lemma inj_core (A : Finset ℕ) (s q : ℤ) (hN : 2 * q - s ^ 2 ≠ 0)
    (x y : Fin 3 → ↥A)
    (h2x : W A 2 x = s) (h4x : W A 4 x = q)
    (h2y : W A 2 y = s) (h4y : W A 4 y = q)
    (hd : d1 A s x = d1 A s y)
    (hb : decide (b A x ≤ c A x) = decide (b A y ≤ c A y)) :
    x = y := by
  have hpx := d1_mul_d2 A s q x h2x h4x
  have hpy := d1_mul_d2 A s q y h2y h4y
  have hne : d1 A s x ≠ 0 := by
    intro h0
    apply hN
    rw [← hpx, h0, zero_mul]
  have hd2 : d2 A s x = d2 A s y := by
    rw [hd] at hpx
    exact mul_left_cancel₀ (hd ▸ hne) (hpx.trans hpy.symm)
  have hsum2 : a A x ^ 2 + b A x ^ 2 + c A x ^ 2 = a A y ^ 2 + b A y ^ 2 + c A y ^ 2 := by
    rw [← W_two, ← W_two, h2x, h2y]
  simp only [d1, d2] at hd hd2
  have ha : a A x = a A y := by
    nlinarith [a_nonneg A x, a_nonneg A y]
  have hbc : b A x * c A x = b A y * c A y := by linarith
  have hbsq : b A x ^ 2 + c A x ^ 2 = b A y ^ 2 + c A y ^ 2 := by
    have : a A x ^ 2 = a A y ^ 2 := by rw [ha]
    linarith
  have hsum : b A x + c A x = b A y + c A y := by
    nlinarith [b_nonneg A x, c_nonneg A x, b_nonneg A y, c_nonneg A y]
  have hbit : b A x ≤ c A x ↔ b A y ≤ c A y := decide_eq_decide.mp hb
  have hprod : (b A x - b A y) * (b A x - c A y) = 0 := by
    have hid : (b A x - b A y) * (b A x - c A y) =
        (b A x ^ 2 - (b A x + c A x) * b A x + b A x * c A x) +
        ((b A x + c A x) - (b A y + c A y)) * b A x +
        (b A y * c A y - b A x * c A x) := by ring
    have hz : b A x ^ 2 - (b A x + c A x) * b A x + b A x * c A x = 0 := by ring
    have h1 : (b A x + c A x) - (b A y + c A y) = 0 := by linarith
    have h2 : b A y * c A y - b A x * c A x = 0 := by linarith
    rw [hid, hz, h1, h2]
    ring
  have hbeq : b A x = b A y := by
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · have hxy : b A x = c A y := by linarith
      have hyx : c A x = b A y := by linarith
      have hbit' : b A x ≤ c A x ↔ c A x ≤ b A x := by
        rw [← hyx, ← hxy] at hbit
        exact hbit
      have hbcx : b A x = c A x := by
        rcases le_total (b A x) (c A x) with h1 | h1
        · linarith [hbit'.mp h1]
        · linarith [hbit'.mpr h1]
      linarith
  have hceq : c A x = c A y := by linarith
  have ha' : (x 0 : ℕ) = (y 0 : ℕ) := by
    have : ((x 0 : ℕ) : ℤ) = ((y 0 : ℕ) : ℤ) := ha
    exact_mod_cast this
  have hb' : (x 1 : ℕ) = (y 1 : ℕ) := by
    have : ((x 1 : ℕ) : ℤ) = ((y 1 : ℕ) : ℤ) := hbeq
    exact_mod_cast this
  have hc' : (x 2 : ℕ) = (y 2 : ℕ) := by
    have : ((x 2 : ℕ) : ℤ) = ((y 2 : ℕ) : ℤ) := hceq
    exact_mod_cast this
  funext i
  fin_cases i
  · exact Subtype.ext ha'
  · exact Subtype.ext hb'
  · exact Subtype.ext hc'

private lemma mem_divisors_of_fiber (A : Finset ℕ) (s q : ℤ) (hN : 2 * q - s ^ 2 ≠ 0)
    (x : Fin 3 → ↥A) (h2 : W A 2 x = s) (h4 : W A 4 x = q) :
    (d1 A s x).natAbs ∈ (2 * q - s ^ 2).natAbs.divisors := by
  have hp := d1_mul_d2 A s q x h2 h4
  have hne : d1 A s x ≠ 0 := fun h0 => hN (by rw [← hp, h0, zero_mul])
  rw [Nat.mem_divisors]
  refine ⟨⟨(d2 A s x).natAbs, ?_⟩, Int.natAbs_ne_zero.mpr hN⟩
  rw [← Int.natAbs_mul, hp]

theorem fiber_le_divisors (A : Finset ℕ) (s q : ℤ) (h : 2 * q ≠ s ^ 2) :
    (Finset.univ.filter (fun x : Fin 3 → ↥A => W A 2 x = s ∧ W A 4 x = q)).card ≤
      4 * (2 * q - s ^ 2).natAbs.divisors.card := by
  classical
  have hN : 2 * q - s ^ 2 ≠ 0 := sub_ne_zero.mpr h
  set F : Finset (Fin 3 → ↥A) :=
    Finset.univ.filter (fun x => W A 2 x = s ∧ W A 4 x = q)
  set n : ℕ := (2 * q - s ^ 2).natAbs
  let f : (Fin 3 → ↥A) → ℕ × Bool × Bool :=
    fun x => ((d1 A s x).natAbs, (decide (0 ≤ d1 A s x), decide (b A x ≤ c A x)))
  set T : Finset (ℕ × Bool × Bool) :=
    n.divisors ×ˢ ((Finset.univ : Finset Bool) ×ˢ Finset.univ)
  have hmaps : Set.MapsTo f (F : Set (Fin 3 → ↥A)) (T : Set (ℕ × Bool × Bool)) := by
    intro x hx
    have hx' : W A 2 x = s ∧ W A 4 x = q := by simpa [F] using hx
    show f x ∈ T
    rw [Finset.mem_product]
    refine ⟨mem_divisors_of_fiber A s q hN x hx'.1 hx'.2, ?_⟩
    simp
  have hinj : Set.InjOn f (F : Set (Fin 3 → ↥A)) := by
    intro x hx y hy hxy
    have hx' : W A 2 x = s ∧ W A 4 x = q := by simpa [F] using hx
    have hy' : W A 2 y = s ∧ W A 4 y = q := by simpa [F] using hy
    dsimp only [f] at hxy
    have h1 : (d1 A s x).natAbs = (d1 A s y).natAbs := congrArg Prod.fst hxy
    have h23 := congrArg Prod.snd hxy
    have h2 : decide (0 ≤ d1 A s x) = decide (0 ≤ d1 A s y) := congrArg Prod.fst h23
    have h3 : decide (b A x ≤ c A x) = decide (b A y ≤ c A y) := congrArg Prod.snd h23
    exact inj_core A s q hN x y hx'.1 hx'.2 hy'.1 hy'.2 (int_eq_of_natAbs_eq h1 h2) h3
  have hle : F.card ≤ T.card := Finset.card_le_card_of_injOn f hmaps hinj
  have hcard : T.card = 4 * n.divisors.card := by
    simp only [T, Finset.card_product, Finset.card_univ, Fintype.card_bool]
    ring
  rw [hcard] at hle
  exact hle

private lemma eq_or_neg_of_natAbs_eq {u v : ℤ} (h : u.natAbs = v.natAbs) : u = v ∨ u = -v := by
  have hz : (u.natAbs : ℤ) = (v.natAbs : ℤ) := by exact_mod_cast h
  rcases le_total 0 u with hu | hu <;> rcases le_total 0 v with hv | hv
  · left; rw [← Int.natAbs_of_nonneg hu, ← Int.natAbs_of_nonneg hv, h]
  · right
    have hv' : 0 ≤ -v := by linarith
    have e1 : u = (u.natAbs : ℤ) := by rw [Int.natAbs_of_nonneg hu]
    have e2 : -v = (v.natAbs : ℤ) := by
      rw [← Int.natAbs_of_nonneg hv', Int.natAbs_neg]
    linarith
  · right
    have hu' : 0 ≤ -u := by linarith
    have e1 : v = (v.natAbs : ℤ) := by rw [Int.natAbs_of_nonneg hv]
    have e2 : -u = (u.natAbs : ℤ) := by
      rw [← Int.natAbs_of_nonneg hu', Int.natAbs_neg]
    linarith
  · left
    have hu' : 0 ≤ -u := by linarith
    have hv' : 0 ≤ -v := by linarith
    have e1 : -u = (u.natAbs : ℤ) := by
      rw [← Int.natAbs_of_nonneg hu', Int.natAbs_neg]
    have e2 : -v = (v.natAbs : ℤ) := by
      rw [← Int.natAbs_of_nonneg hv', Int.natAbs_neg]
    linarith

private lemma inj_core_pos (A : Finset ℕ) (hA : ∀ t ∈ A, 1 ≤ t) (s q : ℤ)
    (hN : 2 * q - s ^ 2 ≠ 0) (x y : Fin 3 → ↥A)
    (h2x : W A 2 x = s) (h4x : W A 4 x = q)
    (h2y : W A 2 y = s) (h4y : W A 4 y = q)
    (hd : (d1 A s x).natAbs = (d1 A s y).natAbs)
    (hb : decide (b A x ≤ c A x) = decide (b A y ≤ c A y)) :
    x = y := by
  rcases eq_or_neg_of_natAbs_eq hd with hd' | hd'
  · exact inj_core A s q hN x y h2x h4x h2y h4y hd' hb
  · exfalso
    have hpx := d1_mul_d2 A s q x h2x h4x
    have hpy := d1_mul_d2 A s q y h2y h4y
    have hne : d1 A s x ≠ 0 := fun h0 => hN (by rw [← hpx, h0, zero_mul])
    have hd2 : d2 A s y = -(d2 A s x) := by
      have e : d1 A s x * d2 A s x = d1 A s y * d2 A s y := hpx.trans hpy.symm
      have hd'' : d1 A s y = -(d1 A s x) := by linarith
      rw [hd''] at e
      have h1 : d1 A s x * (d2 A s x + d2 A s y) = 0 := by linear_combination e
      have h2 : d2 A s x + d2 A s y = 0 := (mul_eq_zero.mp h1).resolve_left hne
      linarith
    simp only [d1, d2] at hd' hd2
    have hb1 : 1 ≤ b A x := by
      have h2 : (1 : ℤ) ≤ ((x 1 : ℕ) : ℤ) := by exact_mod_cast hA _ (x 1).2
      exact h2
    have hc1 : 1 ≤ c A x := by
      have h2 : (1 : ℤ) ≤ ((x 2 : ℕ) : ℤ) := by exact_mod_cast hA _ (x 2).2
      exact h2
    have hbc0 : b A x * c A x = 0 := by
      nlinarith [b_nonneg A x, c_nonneg A x, b_nonneg A y, c_nonneg A y]
    nlinarith

theorem fiber_le_divisors_of_pos (A : Finset ℕ) (hA : ∀ t ∈ A, 1 ≤ t) (s q : ℤ)
    (h : 2 * q ≠ s ^ 2) :
    (Finset.univ.filter (fun x : Fin 3 → ↥A => W A 2 x = s ∧ W A 4 x = q)).card ≤
      2 * (2 * q - s ^ 2).natAbs.divisors.card := by
  classical
  have hN : 2 * q - s ^ 2 ≠ 0 := sub_ne_zero.mpr h
  set F : Finset (Fin 3 → ↥A) :=
    Finset.univ.filter (fun x => W A 2 x = s ∧ W A 4 x = q)
  set n : ℕ := (2 * q - s ^ 2).natAbs
  let f : (Fin 3 → ↥A) → ℕ × Bool :=
    fun x => ((d1 A s x).natAbs, decide (b A x ≤ c A x))
  set T : Finset (ℕ × Bool) := n.divisors ×ˢ (Finset.univ : Finset Bool)
  have hmaps : Set.MapsTo f (F : Set (Fin 3 → ↥A)) (T : Set (ℕ × Bool)) := by
    intro x hx
    have hx' : W A 2 x = s ∧ W A 4 x = q := by simpa [F] using hx
    show f x ∈ T
    rw [Finset.mem_product]
    exact ⟨mem_divisors_of_fiber A s q hN x hx'.1 hx'.2, Finset.mem_univ _⟩
  have hinj : Set.InjOn f (F : Set (Fin 3 → ↥A)) := by
    intro x hx y hy hxy
    have hx' : W A 2 x = s ∧ W A 4 x = q := by simpa [F] using hx
    have hy' : W A 2 y = s ∧ W A 4 y = q := by simpa [F] using hy
    dsimp only [f] at hxy
    exact inj_core_pos A hA s q hN x y hx'.1 hx'.2 hy'.1 hy'.2
      (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)
  have hle : F.card ≤ T.card := Finset.card_le_card_of_injOn f hmaps hinj
  have hcard : T.card = 2 * n.divisors.card := by
    simp only [T, Finset.card_product, Finset.card_univ, Fintype.card_bool]
    ring
  rw [hcard] at hle
  exact hle


private theorem qsq_W_two (A : Finset ℕ) (x : Fin 3 → ↥A) :
    W A 2 x = ((x 0 : ℕ) : ℤ) ^ 2 + ((x 1 : ℕ) : ℤ) ^ 2 + ((x 2 : ℕ) : ℤ) ^ 2 := by
  simp [W, Fin.sum_univ_three]

private theorem qsq_W_four (A : Finset ℕ) (x : Fin 3 → ↥A) :
    W A 4 x = ((x 0 : ℕ) : ℤ) ^ 4 + ((x 1 : ℕ) : ℤ) ^ 4 + ((x 2 : ℕ) : ℤ) ^ 4 := by
  simp [W, Fin.sum_univ_three]

private theorem qsq_heron_int (a b c : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h : 2 * (a ^ 4 + b ^ 4 + c ^ 4) = (a ^ 2 + b ^ 2 + c ^ 2) ^ 2) :
    a = b + c ∨ b = a + c ∨ c = a + b := by
  have h' : a ^ 4 + b ^ 4 + c ^ 4 = 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) := by
    nlinarith [h]
  have hprod : (a + b + c) * ((-a + b + c) * ((a - b + c) * (a + b - c))) = 0 := by
    have hid : (a + b + c) * ((-a + b + c) * ((a - b + c) * (a + b - c))) =
        2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) - (a ^ 4 + b ^ 4 + c ^ 4) := by ring
    linarith
  have hpos : 0 < a + b + c := by linarith
  have h1 : (-a + b + c) * ((a - b + c) * (a + b - c)) = 0 := by
    rcases mul_eq_zero.mp hprod with h0 | h0
    · linarith
    · exact h0
  rcases mul_eq_zero.mp h1 with h0 | h0
  · left; linarith
  · rcases mul_eq_zero.mp h0 with h0 | h0
    · right; left; linarith
    · right; right; linarith

theorem heron (A : Finset ℕ) (x : Fin 3 → ↥A) (hx : ∀ i, 1 ≤ (x i : ℕ))
    (h : 2 * W A 4 x = (W A 2 x)^2) :
    (x 0 : ℕ) = (x 1 : ℕ) + (x 2 : ℕ) ∨ (x 1 : ℕ) = (x 0 : ℕ) + (x 2 : ℕ) ∨ (x 2 : ℕ) = (x 0 : ℕ) + (x 1 : ℕ) := by
  rw [qsq_W_two, qsq_W_four] at h
  have ha : (1 : ℤ) ≤ ((x 0 : ℕ) : ℤ) := by exact_mod_cast hx 0
  have hb : (1 : ℤ) ≤ ((x 1 : ℕ) : ℤ) := by exact_mod_cast hx 1
  have hc : (1 : ℤ) ≤ ((x 2 : ℕ) : ℤ) := by exact_mod_cast hx 2
  rcases qsq_heron_int _ _ _ ha hb hc h with h0 | h0 | h0
  · left; exact_mod_cast h0
  · right; left; exact_mod_cast h0
  · right; right; exact_mod_cast h0

private theorem qsq_card_le_of_coord_inj {A : Finset ℕ} {E : Finset (Fin 3 → ↥A)} {i : Fin 3}
    (h : ∀ x ∈ E, ∀ y ∈ E, x i = y i → x = y) : E.card ≤ A.card := by
  classical
  have hinj : Set.InjOn (fun x : Fin 3 → ↥A => x i) E := by
    intro x hx y hy hxy
    exact h x hx y hy hxy
  calc E.card = (E.image (fun x : Fin 3 → ↥A => x i)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset ↥A).card := Finset.card_le_card (Finset.subset_univ _)
    _ = A.card := by simp

private theorem qsq_card_le_of_two_coords_inj {A : Finset ℕ} {E : Finset (Fin 3 → ↥A)} {i j : Fin 3}
    (h : ∀ x ∈ E, ∀ y ∈ E, x i = y i → x j = y j → x = y) : E.card ≤ A.card * A.card := by
  classical
  have hinj : Set.InjOn (fun x : Fin 3 → ↥A => (x i, x j)) E := by
    intro x hx y hy hxy
    exact h x hx y hy (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)
  calc E.card = (E.image (fun x : Fin 3 → ↥A => (x i, x j))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset (↥A × ↥A)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = A.card * A.card := by simp

theorem deg_card_le (A : Finset ℕ) (hA : ∀ a ∈ A, 1 ≤ a) :
    (Finset.univ.filter (fun x : Fin 3 → ↥A => 2 * W A 4 x = (W A 2 x)^2)).card ≤ 3 * A.card^2 := by
  classical
  set E := Finset.univ.filter (fun x : Fin 3 → ↥A => 2 * W A 4 x = (W A 2 x)^2)
  set E1 := Finset.univ.filter (fun x : Fin 3 → ↥A => (x 0 : ℕ) = (x 1 : ℕ) + (x 2 : ℕ))
  set E2 := Finset.univ.filter (fun x : Fin 3 → ↥A => (x 1 : ℕ) = (x 0 : ℕ) + (x 2 : ℕ))
  set E3 := Finset.univ.filter (fun x : Fin 3 → ↥A => (x 2 : ℕ) = (x 0 : ℕ) + (x 1 : ℕ))
  have hsub : E ⊆ (E1 ∪ E2) ∪ E3 := by
    intro x hx
    have hx' : 2 * W A 4 x = (W A 2 x)^2 := (Finset.mem_filter.mp hx).2
    have hpos : ∀ i, 1 ≤ (x i : ℕ) := fun i => hA (x i).1 (x i).2
    rcases heron A x hpos hx' with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hE1 : E1.card ≤ A.card * A.card := by
    refine qsq_card_le_of_two_coords_inj (i := 1) (j := 2) ?_
    intro x hx y hy h1 h2
    have hx0 : (x 0 : ℕ) = (x 1 : ℕ) + (x 2 : ℕ) := (Finset.mem_filter.mp hx).2
    have hy0 : (y 0 : ℕ) = (y 1 : ℕ) + (y 2 : ℕ) := (Finset.mem_filter.mp hy).2
    have h1' : (x 1 : ℕ) = (y 1 : ℕ) := congrArg (fun t : ↥A => (t : ℕ)) h1
    have h2' : (x 2 : ℕ) = (y 2 : ℕ) := congrArg (fun t : ↥A => (t : ℕ)) h2
    have h0 : x 0 = y 0 := Subtype.ext (by omega)
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hE2 : E2.card ≤ A.card * A.card := by
    refine qsq_card_le_of_two_coords_inj (i := 0) (j := 2) ?_
    intro x hx y hy h1 h2
    have hx1 : (x 1 : ℕ) = (x 0 : ℕ) + (x 2 : ℕ) := (Finset.mem_filter.mp hx).2
    have hy1 : (y 1 : ℕ) = (y 0 : ℕ) + (y 2 : ℕ) := (Finset.mem_filter.mp hy).2
    have h1' : (x 0 : ℕ) = (y 0 : ℕ) := congrArg (fun t : ↥A => (t : ℕ)) h1
    have h2' : (x 2 : ℕ) = (y 2 : ℕ) := congrArg (fun t : ↥A => (t : ℕ)) h2
    have h0 : x 1 = y 1 := Subtype.ext (by omega)
    funext i
    fin_cases i
    · exact h1
    · exact h0
    · exact h2
  have hE3 : E3.card ≤ A.card * A.card := by
    refine qsq_card_le_of_two_coords_inj (i := 0) (j := 1) ?_
    intro x hx y hy h1 h2
    have hx2 : (x 2 : ℕ) = (x 0 : ℕ) + (x 1 : ℕ) := (Finset.mem_filter.mp hx).2
    have hy2 : (y 2 : ℕ) = (y 0 : ℕ) + (y 1 : ℕ) := (Finset.mem_filter.mp hy).2
    have h1' : (x 0 : ℕ) = (y 0 : ℕ) := congrArg (fun t : ↥A => (t : ℕ)) h1
    have h2' : (x 1 : ℕ) = (y 1 : ℕ) := congrArg (fun t : ↥A => (t : ℕ)) h2
    have h0 : x 2 = y 2 := Subtype.ext (by omega)
    funext i
    fin_cases i
    · exact h1
    · exact h2
    · exact h0
  calc E.card ≤ ((E1 ∪ E2) ∪ E3).card := Finset.card_le_card hsub
    _ ≤ (E1 ∪ E2).card + E3.card := Finset.card_union_le _ _
    _ ≤ E1.card + E2.card + E3.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ A.card * A.card + A.card * A.card + A.card * A.card := by gcongr
    _ = 3 * A.card ^ 2 := by ring

private theorem qsq_fiber_eq_of_eq (A : Finset ℕ) (hA : ∀ a ∈ A, 1 ≤ a) (s : ℤ)
    (x y : Fin 3 → ↥A) (hx0 : (x 0 : ℕ) = (x 1 : ℕ) + (x 2 : ℕ))
    (hy0 : (y 0 : ℕ) = (y 1 : ℕ) + (y 2 : ℕ)) (hx : W A 2 x = s) (hy : W A 2 y = s)
    (h1 : x 1 = y 1) : x = y := by
  have h1' : (x 1 : ℕ) = (y 1 : ℕ) := congrArg (fun t : ↥A => (t : ℕ)) h1
  have hx0' : ((x 0 : ℕ) : ℤ) = ((x 1 : ℕ) : ℤ) + ((x 2 : ℕ) : ℤ) := by exact_mod_cast hx0
  have hy0' : ((y 0 : ℕ) : ℤ) = ((y 1 : ℕ) : ℤ) + ((y 2 : ℕ) : ℤ) := by exact_mod_cast hy0
  have hb : ((y 1 : ℕ) : ℤ) = ((x 1 : ℕ) : ℤ) := by exact_mod_cast h1'.symm
  rw [qsq_W_two] at hx hy
  have hxe : 2 * (((x 1 : ℕ) : ℤ) ^ 2 + ((x 1 : ℕ) : ℤ) * ((x 2 : ℕ) : ℤ) +
      ((x 2 : ℕ) : ℤ) ^ 2) = s := by
    rw [← hx, hx0']
    ring
  have hye : 2 * (((x 1 : ℕ) : ℤ) ^ 2 + ((x 1 : ℕ) : ℤ) * ((y 2 : ℕ) : ℤ) +
      ((y 2 : ℕ) : ℤ) ^ 2) = s := by
    rw [← hy, hy0', hb]
    ring
  have hdiff : ((x 2 : ℕ) : ℤ) ^ 2 - ((y 2 : ℕ) : ℤ) ^ 2 +
      ((x 1 : ℕ) : ℤ) * (((x 2 : ℕ) : ℤ) - ((y 2 : ℕ) : ℤ)) = 0 := by
    linarith
  have hprod : (((x 2 : ℕ) : ℤ) - ((y 2 : ℕ) : ℤ)) *
      (((x 2 : ℕ) : ℤ) + ((y 2 : ℕ) : ℤ) + ((x 1 : ℕ) : ℤ)) = 0 := by
    linear_combination hdiff
  have hpos : (0 : ℤ) < ((x 2 : ℕ) : ℤ) + ((y 2 : ℕ) : ℤ) + ((x 1 : ℕ) : ℤ) := by
    have h2 : (1 : ℤ) ≤ ((x 2 : ℕ) : ℤ) := by exact_mod_cast hA (x 2).1 (x 2).2
    have h3 : (1 : ℤ) ≤ ((y 2 : ℕ) : ℤ) := by exact_mod_cast hA (y 2).1 (y 2).2
    have h4 : (1 : ℤ) ≤ ((x 1 : ℕ) : ℤ) := by exact_mod_cast hA (x 1).1 (x 1).2
    linarith
  have h2' : (x 2 : ℕ) = (y 2 : ℕ) := by
    rcases mul_eq_zero.mp hprod with h0 | h0
    · omega
    · linarith
  have h2 : x 2 = y 2 := Subtype.ext h2'
  have h0 : x 0 = y 0 := Subtype.ext (by omega)
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

private theorem qsq_fiber_eq_perm (A : Finset ℕ) (hA : ∀ a ∈ A, 1 ≤ a) (s : ℤ) (σ : Fin 3 ≃ Fin 3)
    (x y : Fin 3 → ↥A)
    (hx0 : (x (σ 0) : ℕ) = (x (σ 1) : ℕ) + (x (σ 2) : ℕ))
    (hy0 : (y (σ 0) : ℕ) = (y (σ 1) : ℕ) + (y (σ 2) : ℕ))
    (hx : W A 2 x = s) (hy : W A 2 y = s) (h1 : x (σ 1) = y (σ 1)) : x = y := by
  have hx' : W A 2 (fun i => x (σ i)) = s := by
    rw [← hx]
    exact Equiv.sum_comp σ (fun i => ((x i : ℕ) : ℤ) ^ 2)
  have hy' : W A 2 (fun i => y (σ i)) = s := by
    rw [← hy]
    exact Equiv.sum_comp σ (fun i => ((y i : ℕ) : ℤ) ^ 2)
  have hxy : (fun i => x (σ i)) = (fun i => y (σ i)) :=
    qsq_fiber_eq_of_eq A hA s _ _ hx0 hy0 hx' hy' h1
  funext i
  obtain ⟨j, rfl⟩ := σ.surjective i
  exact congrFun hxy j

theorem deg_fiber_le (A : Finset ℕ) (hA : ∀ a ∈ A, 1 ≤ a) (s : ℤ) :
    (Finset.univ.filter (fun x : Fin 3 → ↥A => 2 * W A 4 x = (W A 2 x)^2 ∧ W A 2 x = s)).card ≤ 3 * A.card := by
  classical
  set E := Finset.univ.filter
    (fun x : Fin 3 → ↥A => 2 * W A 4 x = (W A 2 x)^2 ∧ W A 2 x = s)
  set E1 := Finset.univ.filter
    (fun x : Fin 3 → ↥A => (x 0 : ℕ) = (x 1 : ℕ) + (x 2 : ℕ) ∧ W A 2 x = s)
  set E2 := Finset.univ.filter
    (fun x : Fin 3 → ↥A => (x 1 : ℕ) = (x 0 : ℕ) + (x 2 : ℕ) ∧ W A 2 x = s)
  set E3 := Finset.univ.filter
    (fun x : Fin 3 → ↥A => (x 2 : ℕ) = (x 0 : ℕ) + (x 1 : ℕ) ∧ W A 2 x = s)
  have hsub : E ⊆ (E1 ∪ E2) ∪ E3 := by
    intro x hx
    have hx' : 2 * W A 4 x = (W A 2 x)^2 ∧ W A 2 x = s := (Finset.mem_filter.mp hx).2
    have hpos : ∀ i, 1 ≤ (x i : ℕ) := fun i => hA (x i).1 (x i).2
    rcases heron A x hpos hx'.1 with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, hx'.2⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, hx'.2⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, hx'.2⟩)
  have hE1 : E1.card ≤ A.card := by
    refine qsq_card_le_of_coord_inj (i := 1) ?_
    intro x hx y hy h1
    exact qsq_fiber_eq_perm A hA s (Equiv.refl (Fin 3)) x y
      (Finset.mem_filter.mp hx).2.1 (Finset.mem_filter.mp hy).2.1
      (Finset.mem_filter.mp hx).2.2 (Finset.mem_filter.mp hy).2.2 h1
  have hE2 : E2.card ≤ A.card := by
    have hσ0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := Equiv.swap_apply_left 0 1
    have hσ1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := Equiv.swap_apply_right 0 1
    have hσ2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
    refine qsq_card_le_of_coord_inj (i := 0) ?_
    intro x hx y hy h1
    refine qsq_fiber_eq_perm A hA s (Equiv.swap (0 : Fin 3) 1) x y ?_ ?_ ?_ ?_ ?_
    · rw [hσ0, hσ1, hσ2]; exact (Finset.mem_filter.mp hx).2.1
    · rw [hσ0, hσ1, hσ2]; exact (Finset.mem_filter.mp hy).2.1
    · exact (Finset.mem_filter.mp hx).2.2
    · exact (Finset.mem_filter.mp hy).2.2
    · rw [hσ1]; exact h1
  have hE3 : E3.card ≤ A.card := by
    have hσ0 : (Equiv.swap (0 : Fin 3) 2) 0 = 2 := Equiv.swap_apply_left 0 2
    have hσ1 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := by decide
    have hσ2 : (Equiv.swap (0 : Fin 3) 2) 2 = 0 := Equiv.swap_apply_right 0 2
    refine qsq_card_le_of_coord_inj (i := 1) ?_
    intro x hx y hy h1
    refine qsq_fiber_eq_perm A hA s (Equiv.swap (0 : Fin 3) 2) x y ?_ ?_ ?_ ?_ ?_
    · rw [hσ0, hσ1, hσ2]; exact (Finset.mem_filter.mp hx).2.1.trans (Nat.add_comm _ _)
    · rw [hσ0, hσ1, hσ2]; exact (Finset.mem_filter.mp hy).2.1.trans (Nat.add_comm _ _)
    · exact (Finset.mem_filter.mp hx).2.2
    · exact (Finset.mem_filter.mp hy).2.2
    · rw [hσ1]; exact h1
  calc E.card ≤ ((E1 ∪ E2) ∪ E3).card := Finset.card_le_card hsub
    _ ≤ (E1 ∪ E2).card + E3.card := Finset.card_union_le _ _
    _ ≤ E1.card + E2.card + E3.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ A.card + A.card + A.card := by gcongr
    _ = 3 * A.card := by ring







/-! ### Helpers -/

private def Ind (A : Finset ℕ) (h : ℤ) (x y : Fin 3 → ↥A) : ℝ :=
  if (W A 4 x = W A 4 y ∧ W A 2 x - W A 2 y = h) then 1 else 0

private lemma ind_nonneg (A : Finset ℕ) (h : ℤ) (x y : Fin 3 → ↥A) : 0 ≤ Ind A h x y := by
  unfold Ind; split_ifs <;> norm_num

private lemma coord_bounds {A : Finset ℕ} {M : ℕ} (hA : A ⊆ Finset.Icc 1 M)
    (x : Fin 3 → ↥A) (i : Fin 3) : 1 ≤ (x i : ℕ) ∧ (x i : ℕ) ≤ M :=
  Finset.mem_Icc.mp (hA (x i).2)

private lemma W2_pos {A : Finset ℕ} (hA : ∀ a ∈ A, 1 ≤ a) (x : Fin 3 → ↥A) : 0 < W A 2 x := by
  have h0 : (1:ℤ) ≤ ((x 0 : ℕ) : ℤ) := by exact_mod_cast hA (x 0).1 (x 0).2
  have h1 : (1:ℤ) ≤ ((x 1 : ℕ) : ℤ) := by exact_mod_cast hA (x 1).1 (x 1).2
  have h2 : (1:ℤ) ≤ ((x 2 : ℕ) : ℤ) := by exact_mod_cast hA (x 2).1 (x 2).2
  unfold W
  rw [Fin.sum_univ_three]
  nlinarith

private lemma W2_le {A : Finset ℕ} {M : ℕ} (hA : A ⊆ Finset.Icc 1 M) (hM : 2 ≤ M)
    (x : Fin 3 → ↥A) : W A 2 x ≤ 3 * (M : ℤ)^2 := by
  have h0 := coord_bounds hA x 0
  have h1 := coord_bounds hA x 1
  have h2 := coord_bounds hA x 2
  have hM1 : (1:ℤ) ≤ (M : ℤ) := by omega
  have e0 : ((x 0 : ℕ) : ℤ) ≤ (M : ℤ) := by exact_mod_cast h0.2
  have e1 : ((x 1 : ℕ) : ℤ) ≤ (M : ℤ) := by exact_mod_cast h1.2
  have e2 : ((x 2 : ℕ) : ℤ) ≤ (M : ℤ) := by exact_mod_cast h2.2
  have p0 : (1:ℤ) ≤ ((x 0 : ℕ) : ℤ) := by exact_mod_cast h0.1
  have p1 : (1:ℤ) ≤ ((x 1 : ℕ) : ℤ) := by exact_mod_cast h1.1
  have p2 : (1:ℤ) ≤ ((x 2 : ℕ) : ℤ) := by exact_mod_cast h2.1
  unfold W
  rw [Fin.sum_univ_three]
  nlinarith

private lemma W4_le {A : Finset ℕ} {M : ℕ} (hA : A ⊆ Finset.Icc 1 M) (hM : 2 ≤ M)
    (x : Fin 3 → ↥A) : W A 4 x ≤ 3 * (M : ℤ)^4 := by
  have h0 := coord_bounds hA x 0
  have h1 := coord_bounds hA x 1
  have h2 := coord_bounds hA x 2
  have hM1 : (1:ℤ) ≤ (M : ℤ) := by omega
  have e0 : ((x 0 : ℕ) : ℤ) ≤ (M : ℤ) := by exact_mod_cast h0.2
  have e1 : ((x 1 : ℕ) : ℤ) ≤ (M : ℤ) := by exact_mod_cast h1.2
  have e2 : ((x 2 : ℕ) : ℤ) ≤ (M : ℤ) := by exact_mod_cast h2.2
  have p0 : (1:ℤ) ≤ ((x 0 : ℕ) : ℤ) := by exact_mod_cast h0.1
  have p1 : (1:ℤ) ≤ ((x 1 : ℕ) : ℤ) := by exact_mod_cast h1.1
  have p2 : (1:ℤ) ≤ ((x 2 : ℕ) : ℤ) := by exact_mod_cast h2.1
  have q0 : ((x 0 : ℕ) : ℤ)^4 ≤ (M : ℤ)^4 := pow_le_pow_left₀ (by linarith : (0:ℤ) ≤ _) e0 4
  have q1 : ((x 1 : ℕ) : ℤ)^4 ≤ (M : ℤ)^4 := pow_le_pow_left₀ (by linarith : (0:ℤ) ≤ _) e1 4
  have q2 : ((x 2 : ℕ) : ℤ)^4 ≤ (M : ℤ)^4 := pow_le_pow_left₀ (by linarith : (0:ℤ) ≤ _) e2 4
  unfold W
  rw [Fin.sum_univ_three]
  linarith

private lemma sum_ind_eq_card (A : Finset ℕ) (h : ℤ) (y : Fin 3 → ↥A) :
    (∑ x : Fin 3 → ↥A, Ind A h x y) =
      ((Finset.univ.filter (fun x => W A 2 x = W A 2 y + h ∧ W A 4 x = W A 4 y)).card : ℝ) := by
  have hcongr : ∀ x, Ind A h x y =
      (if (W A 2 x = W A 2 y + h ∧ W A 4 x = W A 4 y) then (1:ℝ) else 0) := by
    intro x
    unfold Ind
    by_cases hp : W A 4 x = W A 4 y ∧ W A 2 x - W A 2 y = h
    · rw [if_pos hp, if_pos (show W A 2 x = W A 2 y + h ∧ W A 4 x = W A 4 y from ⟨by linarith [hp.2], hp.1⟩)]
    · rw [if_neg hp, if_neg (by rintro ⟨h1, h2⟩; exact hp ⟨h2, by linarith⟩)]
  simp_rw [hcongr]
  rw [Finset.card_filter]
  push_cast
  rfl

private lemma sum_ind_eq_card' (A : Finset ℕ) (h : ℤ) (x : Fin 3 → ↥A) :
    (∑ y : Fin 3 → ↥A, Ind A h x y) =
      ((Finset.univ.filter (fun y => W A 2 y = W A 2 x - h ∧ W A 4 y = W A 4 x)).card : ℝ) := by
  have hcongr : ∀ y, Ind A h x y =
      (if (W A 2 y = W A 2 x - h ∧ W A 4 y = W A 4 x) then (1:ℝ) else 0) := by
    intro y
    unfold Ind
    by_cases hp : W A 4 x = W A 4 y ∧ W A 2 x - W A 2 y = h
    · rw [if_pos hp, if_pos (show W A 2 y = W A 2 x - h ∧ W A 4 y = W A 4 x from ⟨by linarith [hp.2], hp.1.symm⟩)]
    · rw [if_neg hp, if_neg (by rintro ⟨h1, h2⟩; exact hp ⟨h2.symm, by linarith⟩)]
  simp_rw [hcongr]
  rw [Finset.card_filter]
  push_cast
  rfl

private lemma fiber_real_bound {A : Finset ℕ} {M : ℕ} (hA : A ⊆ Finset.Icc 1 M) (hM : 2 ≤ M)
    {C0 δ : ℝ} (hC0 : 0 < C0) (hdiv : ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C0 * (n : ℝ)^δ)
    (hδ : 0 ≤ δ) (s q : ℤ) (hne : 2 * q ≠ s^2)
    (hne0 : (Finset.univ.filter (fun x : Fin 3 → ↥A => W A 2 x = s ∧ W A 4 x = q)).Nonempty) :
    ((Finset.univ.filter (fun x : Fin 3 → ↥A => W A 2 x = s ∧ W A 4 x = q)).card : ℝ) ≤
      2 * C0 * (15 * (M : ℝ)^4)^δ := by
  obtain ⟨x, hx⟩ := hne0
  have hxs : W A 2 x = s := (Finset.mem_filter.mp hx).2.1
  have hxq : W A 4 x = q := (Finset.mem_filter.mp hx).2.2
  have hA1 : ∀ a ∈ A, 1 ≤ a := fun a ha => (Finset.mem_Icc.mp (hA ha)).1
  have hs0 : 0 ≤ s := by rw [← hxs]; exact (W2_pos hA1 x).le
  have hq0 : 0 ≤ q := by
    rw [← hxq]; unfold W; rw [Fin.sum_univ_three]
    have h0 := coord_bounds hA x 0
    have h1 := coord_bounds hA x 1
    have h2 := coord_bounds hA x 2
    have p0 : (0:ℤ) ≤ ((x 0 : ℕ) : ℤ) := by omega
    have p1 : (0:ℤ) ≤ ((x 1 : ℕ) : ℤ) := by omega
    have p2 : (0:ℤ) ≤ ((x 2 : ℕ) : ℤ) := by omega
    positivity
  have hsM : s ≤ 3 * (M : ℤ)^2 := by rw [← hxs]; exact W2_le hA hM x
  have hqM : q ≤ 3 * (M : ℤ)^4 := by rw [← hxq]; exact W4_le hA hM x
  have hs2 : s^2 ≤ 9 * (M : ℤ)^4 := by
    have : s^2 ≤ (3 * (M : ℤ)^2)^2 := pow_le_pow_left₀ hs0 hsM 2
    have : (3 * (M : ℤ)^2)^2 = 9 * (M : ℤ)^4 := by ring
    linarith
  have hs2n : 0 ≤ s^2 := sq_nonneg s
  have hM4 : (0:ℤ) ≤ (M : ℤ)^4 := by positivity
  have hnat : (2 * q - s^2).natAbs ≤ 15 * M^4 := by
    have h1 : 2 * q - s^2 ≤ 15 * (M : ℤ)^4 := by linarith
    have h2 : -(15 * (M : ℤ)^4) ≤ 2 * q - s^2 := by linarith
    have h3 : ((15 * M^4 : ℕ) : ℤ) = 15 * (M : ℤ)^4 := by push_cast; ring
    have hsq : (2 * q - s^2)^2 ≤ ((15 * M^4 : ℕ) : ℤ)^2 := by nlinarith [h1, h2, h3]
    have h5 := Int.natAbs_le_iff_sq_le.mpr hsq
    rwa [Int.natAbs_natCast] at h5
  have hcard : (Finset.univ.filter (fun x : Fin 3 → ↥A => W A 2 x = s ∧ W A 4 x = q)).card ≤
      2 * (2 * q - s^2).natAbs.divisors.card := fiber_le_divisors_of_pos A hA1 s q hne
  have hdiv' : ((2 * q - s^2).natAbs.divisors.card : ℝ) ≤ C0 * ((2 * q - s^2).natAbs : ℝ)^δ :=
    hdiv _
  have hrpow : ((2 * q - s^2).natAbs : ℝ)^δ ≤ (15 * (M : ℝ)^4)^δ := by
    refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ hδ
    exact_mod_cast hnat
  have hcast : ((Finset.univ.filter (fun x : Fin 3 → ↥A => W A 2 x = s ∧ W A 4 x = q)).card : ℝ) ≤
      2 * ((2 * q - s^2).natAbs.divisors.card : ℝ) := by exact_mod_cast hcard
  have h15 : (0:ℝ) ≤ 15 * (M : ℝ)^4 := by positivity
  nlinarith [hdiv', hrpow, hcast, mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hC0.le,
    mul_nonneg hC0.le (by positivity : (0:ℝ) ≤ (15 * (M:ℝ)^4)^δ)]



theorem slice_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M → ∀ h : ℤ,
      let w := fun (k : ℕ) (x : Fin 3 → (↥A)) => ∑ i, ((x i : ℕ):ℤ)^k
      let triples := (Finset.univ : Finset ((Fin 3 → (↥A)) × (Fin 3 → (↥A))))
      ((triples.filter (fun z => w 4 z.1 = w 4 z.2 ∧ w 2 z.1 - w 2 z.2 = h)).card : ℝ) ≤
        C * (M:ℝ)^ε * (A.card : ℝ)^3 := by
  classical
  obtain ⟨C0, hC0, hdiv⟩ := divisor_bound (ε / 4) (by linarith)
  refine ⟨8 * C0 * (15:ℝ)^(ε/4) + 9, by positivity, ?_⟩
  intro M hM A hA h
  show ((Finset.univ : Finset ((Fin 3 → ↥A) × (Fin 3 → ↥A))).filter
    (fun z => W A 4 z.1 = W A 4 z.2 ∧ W A 2 z.1 - W A 2 z.2 = h)).card ≤
      (8 * C0 * (15:ℝ)^(ε/4) + 9) * (M:ℝ)^ε * (A.card:ℝ)^3
  rcases Finset.eq_empty_or_nonempty A with hAemp | hAne
  · rw [hAemp]
    have hcard : (Finset.univ : Finset ((Fin 3 → ↥(∅ : Finset ℕ)) × (Fin 3 → ↥(∅ : Finset ℕ)))).card = 0 := by
      simp
    have hle : ((Finset.univ : Finset ((Fin 3 → ↥(∅ : Finset ℕ)) × (Fin 3 → ↥(∅ : Finset ℕ)))).filter
        (fun z => W (∅ : Finset ℕ) 4 z.1 = W (∅ : Finset ℕ) 4 z.2 ∧
          W (∅ : Finset ℕ) 2 z.1 - W (∅ : Finset ℕ) 2 z.2 = h)).card ≤ 0 :=
      le_trans (Finset.card_le_card (Finset.subset_univ _)) (le_of_eq hcard)
    have hz : (((Finset.univ : Finset ((Fin 3 → ↥(∅ : Finset ℕ)) × (Fin 3 → ↥(∅ : Finset ℕ)))).filter
        (fun z => W (∅ : Finset ℕ) 4 z.1 = W (∅ : Finset ℕ) 4 z.2 ∧
          W (∅ : Finset ℕ) 2 z.1 - W (∅ : Finset ℕ) 2 z.2 = h)).card : ℝ) = 0 := by
      exact_mod_cast (Nat.le_zero.mp hle)
    rw [hz]
    simp
  have hAcard : 1 ≤ A.card := Finset.card_pos.mpr hAne
  have hA1 : ∀ a ∈ A, 1 ≤ a := fun a ha => (Finset.mem_Icc.mp (hA ha)).1
  set B : ℝ := 2 * C0 * (15 * (M : ℝ)^4)^(ε/4)
  have hB : 0 ≤ B := by positivity
  have hBrw : B = 2 * C0 * (15:ℝ)^(ε/4) * (M:ℝ)^ε := by
    dsimp [B]
    have hM4 : (0:ℝ) ≤ (M:ℝ)^4 := by positivity
    rw [Real.mul_rpow (by norm_num) hM4]
    have key : ((M:ℝ)^4)^(ε/4) = (M:ℝ)^ε := by
      rw [← Real.rpow_natCast (M:ℝ) 4, ← Real.rpow_mul (by positivity)]
      congr 1
      ring
    rw [key]
    ring
  have hMε : 1 ≤ (M:ℝ)^ε :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ M)) hε.le
  have h15d : 0 < (15:ℝ)^(ε/4) := Real.rpow_pos_of_pos (by norm_num) _
  have hA3 : 0 ≤ (A.card:ℝ)^3 := by positivity
  have hAcardR : 1 ≤ (A.card:ℝ) := by exact_mod_cast hAcard
  have hA2 : (A.card:ℝ)^2 ≤ (A.card:ℝ)^3 := by nlinarith
  have hT : (((Finset.univ : Finset ((Fin 3 → ↥A) × (Fin 3 → ↥A))).filter
      (fun z => W A 4 z.1 = W A 4 z.2 ∧ W A 2 z.1 - W A 2 z.2 = h)).card : ℝ) =
      ∑ y : (Fin 3 → ↥A), ∑ x : (Fin 3 → ↥A), Ind A h x y := by
    have h1 : (((Finset.univ : Finset ((Fin 3 → ↥A) × (Fin 3 → ↥A))).filter
        (fun z => W A 4 z.1 = W A 4 z.2 ∧ W A 2 z.1 - W A 2 z.2 = h)).card : ℝ) =
        ∑ z : (Fin 3 → ↥A) × (Fin 3 → ↥A), Ind A h z.1 z.2 := by
      rw [Finset.card_filter]
      push_cast
      rfl
    rw [h1, Fintype.sum_prod_type, Finset.sum_comm]
  rw [hT]
  have hpart2 : (∑ y ∈ Finset.univ.filter (fun y => ¬ (2 * W A 4 y = (W A 2 y + h)^2)),
      ∑ x : (Fin 3 → ↥A), Ind A h x y) ≤ (A.card : ℝ)^3 * B := by
    calc _ ≤ ∑ y ∈ Finset.univ.filter (fun y => ¬ (2 * W A 4 y = (W A 2 y + h)^2)), B := by
          refine Finset.sum_le_sum (fun y hy => ?_)
          have hy' : 2 * W A 4 y ≠ (W A 2 y + h)^2 := (Finset.mem_filter.mp hy).2
          rw [sum_ind_eq_card]
          by_cases hne : (Finset.univ.filter (fun x : Fin 3 → ↥A =>
              W A 2 x = W A 2 y + h ∧ W A 4 x = W A 4 y)).Nonempty
          · exact fiber_real_bound hA hM hC0 hdiv (by linarith) (W A 2 y + h) (W A 4 y) hy' hne
          · have hemp : (Finset.univ.filter (fun x : Fin 3 → ↥A =>
                W A 2 x = W A 2 y + h ∧ W A 4 x = W A 4 y)) = ∅ :=
              Finset.not_nonempty_iff_eq_empty.mp hne
            simp [hemp]
            exact hB
      _ = (Finset.univ.filter (fun y => ¬ (2 * W A 4 y = (W A 2 y + h)^2))).card * B := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Finset.univ : Finset (Fin 3 → ↥A)).card * B := by
          refine mul_le_mul_of_nonneg_right ?_ hB
          exact_mod_cast Finset.card_le_card (Finset.subset_univ _)
      _ = (A.card : ℝ)^3 * B := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
          push_cast
          ring
  have hpart1 : (∑ y ∈ Finset.univ.filter (fun y => 2 * W A 4 y = (W A 2 y + h)^2),
      ∑ x : (Fin 3 → ↥A), Ind A h x y) ≤
      ∑ x ∈ Finset.univ.filter (fun x : Fin 3 → ↥A => 2 * W A 4 x = (W A 2 x)^2),
        ∑ y : (Fin 3 → ↥A), Ind A h x y := by
    have h1 : (∑ y ∈ Finset.univ.filter (fun y => 2 * W A 4 y = (W A 2 y + h)^2),
        ∑ x : (Fin 3 → ↥A), Ind A h x y) =
        ∑ y ∈ Finset.univ.filter (fun y => 2 * W A 4 y = (W A 2 y + h)^2),
          ∑ x ∈ Finset.univ.filter (fun x : Fin 3 → ↥A => 2 * W A 4 x = (W A 2 x)^2),
            Ind A h x y := by
      refine Finset.sum_congr rfl (fun y hy => ?_)
      symm
      refine Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => ?_)
      have hyD : 2 * W A 4 y = (W A 2 y + h)^2 := (Finset.mem_filter.mp hy).2
      have hxD : 2 * W A 4 x ≠ (W A 2 x)^2 := by
        intro hh; exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hh⟩)
      have hz : Ind A h x y = 0 := by
        unfold Ind
        split_ifs with hc
        · exfalso
          apply hxD
          have e1 : W A 2 x = W A 2 y + h := by linarith [hc.2]
          rw [hc.1, hyD, e1]
        · rfl
      exact hz
    rw [h1, Finset.sum_comm]
    refine Finset.sum_le_sum (fun x hx => ?_)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun y _ _ => ind_nonneg A h x y)
  have hsplit : (∑ y : (Fin 3 → ↥A), ∑ x : (Fin 3 → ↥A), Ind A h x y) =
      (∑ y ∈ Finset.univ.filter (fun y => 2 * W A 4 y = (W A 2 y + h)^2), ∑ x, Ind A h x y) +
      (∑ y ∈ Finset.univ.filter (fun y => ¬ (2 * W A 4 y = (W A 2 y + h)^2)),
        ∑ x, Ind A h x y) :=
    (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin 3 → ↥A))
      (fun y => 2 * W A 4 y = (W A 2 y + h)^2) (fun y => ∑ x, Ind A h x y)).symm
  by_cases h0 : h = 0
  · subst h0
    have hdeg : (∑ x ∈ Finset.univ.filter (fun x : Fin 3 → ↥A => 2 * W A 4 x = (W A 2 x)^2),
        ∑ y : (Fin 3 → ↥A), Ind A 0 x y) ≤ 9 * (A.card : ℝ)^3 := by
      calc _ ≤ ∑ x ∈ Finset.univ.filter (fun x : Fin 3 → ↥A => 2 * W A 4 x = (W A 2 x)^2),
              3 * (A.card : ℝ) := by
            refine Finset.sum_le_sum (fun x hx => ?_)
            have hxD : 2 * W A 4 x = (W A 2 x)^2 := (Finset.mem_filter.mp hx).2
            rw [sum_ind_eq_card']
            have hsub : (Finset.univ.filter (fun y : Fin 3 → ↥A =>
                  W A 2 y = W A 2 x - 0 ∧ W A 4 y = W A 4 x)) ⊆
                (Finset.univ.filter (fun y : Fin 3 → ↥A =>
                  2 * W A 4 y = (W A 2 y)^2 ∧ W A 2 y = W A 2 x)) := by
              intro y hy
              have hy1 : W A 2 y = W A 2 x - 0 := (Finset.mem_filter.mp hy).2.1
              have hy2 : W A 4 y = W A 4 x := (Finset.mem_filter.mp hy).2.2
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ y, ?_⟩
              refine ⟨?_, by linarith⟩
              rw [hy2, hxD, hy1]
              ring
            have hc : (Finset.univ.filter (fun y : Fin 3 → ↥A =>
                  W A 2 y = W A 2 x - 0 ∧ W A 4 y = W A 4 x)).card ≤ 3 * A.card :=
              le_trans (Finset.card_le_card hsub) (deg_fiber_le A hA1 (W A 2 x))
            exact_mod_cast hc
        _ = (Finset.univ.filter (fun x : Fin 3 → ↥A => 2 * W A 4 x = (W A 2 x)^2)).card *
              (3 * (A.card : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (3 * (A.card : ℝ)^2) * (3 * (A.card : ℝ)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact_mod_cast deg_card_le A hA1
        _ = 9 * (A.card : ℝ)^3 := by ring
    have htot : (∑ y : (Fin 3 → ↥A), ∑ x : (Fin 3 → ↥A), Ind A 0 x y) ≤
        (A.card : ℝ)^3 * B + 9 * (A.card : ℝ)^3 := by
      rw [hsplit]
      linarith [hpart1, hpart2, hdeg]
    have hfin : (A.card : ℝ)^3 * B + 9 * (A.card : ℝ)^3 ≤
        (8 * C0 * (15:ℝ)^(ε/4) + 9) * (M:ℝ)^ε * (A.card:ℝ)^3 := by
      rw [hBrw]
      nlinarith [hMε, hA3, h15d, hC0]
    linarith
  · have hdeg : (∑ x ∈ Finset.univ.filter (fun x : Fin 3 → ↥A => 2 * W A 4 x = (W A 2 x)^2),
        ∑ y : (Fin 3 → ↥A), Ind A h x y) ≤ 3 * (A.card : ℝ)^2 * B := by
      calc _ ≤ ∑ x ∈ Finset.univ.filter (fun x : Fin 3 → ↥A => 2 * W A 4 x = (W A 2 x)^2), B := by
            refine Finset.sum_le_sum (fun x hx => ?_)
            have hxD : 2 * W A 4 x = (W A 2 x)^2 := (Finset.mem_filter.mp hx).2
            rw [sum_ind_eq_card']
            by_cases hne : (Finset.univ.filter (fun y : Fin 3 → ↥A =>
                W A 2 y = W A 2 x - h ∧ W A 4 y = W A 4 x)).Nonempty
            · refine fiber_real_bound hA hM hC0 hdiv (by linarith) (W A 2 x - h) (W A 4 x) ?_ hne
              intro heq
              have hprod : h * (2 * W A 2 x - h) = 0 := by nlinarith [heq, hxD]
              rcases mul_eq_zero.mp hprod with hh | hh
              · exact h0 hh
              · obtain ⟨y, hy⟩ := hne
                have hy1 : W A 2 y = W A 2 x - h := (Finset.mem_filter.mp hy).2.1
                have hypos : 0 < W A 2 y := W2_pos hA1 y
                have hxpos : 0 < W A 2 x := W2_pos hA1 x
                linarith
            · have hemp : (Finset.univ.filter (fun y : Fin 3 → ↥A =>
                  W A 2 y = W A 2 x - h ∧ W A 4 y = W A 4 x)) = ∅ :=
                Finset.not_nonempty_iff_eq_empty.mp hne
              simp [hemp]
              exact hB
        _ = (Finset.univ.filter (fun x : Fin 3 → ↥A => 2 * W A 4 x = (W A 2 x)^2)).card * B := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (3 * (A.card : ℝ)^2) * B := by
            refine mul_le_mul_of_nonneg_right ?_ hB
            exact_mod_cast deg_card_le A hA1
    have htot : (∑ y : (Fin 3 → ↥A), ∑ x : (Fin 3 → ↥A), Ind A h x y) ≤
        (A.card : ℝ)^3 * B + 3 * (A.card : ℝ)^2 * B := by
      rw [hsplit]
      linarith [hpart1, hpart2, hdeg]
    have hfin : (A.card : ℝ)^3 * B + 3 * (A.card : ℝ)^2 * B ≤
        (8 * C0 * (15:ℝ)^(ε/4) + 9) * (M:ℝ)^ε * (A.card:ℝ)^3 := by
      rw [hBrw]
      nlinarith [hMε, hA3, h15d, hC0, hA2, hB]
    linarith

end Conjectures.Goldbach.QuarticSquareSlice_aux

theorem Conjectures.Goldbach.QuarticSquareSlice :
    ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧ ∀ M : ℕ, 2≤M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M →
      ∀ h : ℤ, let w := fun (k : ℕ) (x : Fin 3 → (↥A)) => ∑ i, ((x i : ℕ):ℤ)^k;
      let triples := (Finset.univ : Finset ((Fin 3 → (↥A)) × (Fin 3 → (↥A))));
      ((triples.filter (fun z => w 4 z.1=w 4 z.2 ∧ w 2 z.1-w 2 z.2=h)).card:ℝ) ≤
        C*(M:ℝ)^ε*(A.card:ℝ)^3 :=
  Conjectures.Goldbach.QuarticSquareSlice_aux.slice_bound
