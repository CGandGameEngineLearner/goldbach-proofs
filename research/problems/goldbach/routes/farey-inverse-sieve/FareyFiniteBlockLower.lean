import Mathlib

/-! # Bonferroni lower bound for the Farey initial sieve

The final theorem is FareyBrun.finite_block_lower. It takes finite intersection-count
remainders and a reciprocal-mass tail. These hypotheses still need to be specialized
to the Farey window before the initial-sieve task can be submitted.

The upper block expansions use material by Sushaan Kandukoori (copyright 2026)
under Apache-2.0. The source revision is recorded below. The lower-bound combination
and count/model transfer are derived in this file. -/


/- Adapted from ErdosStraus/Estimates/BrunHooley.lean (Apache-2.0),
   sushaan-k/erdos-straus-lean, revision f6c99eaaca6ec7a7226a7a16bef1cd2b09e36660.
   This excerpt retains the finite combinatorial identities and omits the progression application. -/

lemma fareyProdLe {ι : Type*} {s : Finset ι} {f g : ι → ℝ}
    (hf0 : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
      ih (fun i hi => hf0 i (by simp [hi])) (fun i hi => hfg i (by simp [hi]))
    have h2 : (0:ℝ) ≤ ∏ i ∈ s, f i := Finset.prod_nonneg (fun i hi => hf0 i (by simp [hi]))
    have h3 : f a ≤ g a := hfg a (by simp)
    have h4 : (0:ℝ) ≤ f a := hf0 a (by simp)
    have h5 : (0:ℝ) ≤ g a := le_trans h4 h3
    exact mul_le_mul h3 h1 h2 h5

lemma fareyProdOne {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hprod : ∏ i ∈ s, f i ≤ 1 :=
      ih (fun i hi => h0 i (by simp [hi])) (fun i hi => h1 i (by simp [hi]))
    have hnonneg : (0:ℝ) ≤ ∏ i ∈ s, f i := Finset.prod_nonneg (fun i hi => h0 i (by simp [hi]))
    have ha1 : f a ≤ 1 := h1 a (by simp)
    calc f a * (∏ i ∈ s, f i) ≤ 1 * 1 := mul_le_mul ha1 hprod hnonneg (by norm_num)
      _ = 1 := by norm_num

namespace ErdosStraus.RoughEstimates

open scoped BigOperators

section

attribute [local instance] Classical.propDecidable

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

/-- The number of `n ∈ A` with `hit i n` for every `i ∈ u`. -/
noncomputable def intersectionCount (A : Finset α) (hit : ι → α → Prop)
    (u : Finset ι) : ℝ := by
  classical
  exact ((A.filter (fun n => ∀ i ∈ u, hit i n)).card : ℝ)

end

/-! ## Bonferroni inequalities -/

variable {ι : Type*} [DecidableEq ι]

/-- The elementary symmetric sum `e_m(w) = ∑_{u ⊆ s, |u| = m} ∏_{i ∈ u} w i`. -/
noncomputable def elementary (s : Finset ι) (w : ι → ℝ) (m : ℕ) : ℝ :=
  ∑ u ∈ s.powersetCard m, ∏ i ∈ u, w i

/-- The truncation `∑_{j ≤ m} (-1)^j e_j(w)` of the expansion of `∏_{i ∈ s} (1 - w i)`. -/
noncomputable def truncation (s : Finset ι) (w : ι → ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ j * elementary s w j

omit [DecidableEq ι] in
@[simp] theorem elementary_zero (s : Finset ι) (w : ι → ℝ) :
    elementary s w 0 = 1 := by
  simp [elementary]

omit [DecidableEq ι] in
@[simp] theorem elementary_empty_succ (w : ι → ℝ) (m : ℕ) :
    elementary ∅ w (m + 1) = 0 := by
  have h : (∅ : Finset ι).powersetCard (m + 1) = ∅ := by
    rw [Finset.powersetCard_eq_empty]
    simp
  simp [elementary, h]

theorem elementary_insert {s : Finset ι} {a : ι} (ha : a ∉ s)
    (w : ι → ℝ) (m : ℕ) :
    elementary (insert a s) w (m + 1) =
      elementary s w (m + 1) + w a * elementary s w m := by
  unfold elementary
  rw [Finset.powersetCard_succ_insert ha]
  have hdis : Disjoint (s.powersetCard (m + 1))
      ((s.powersetCard m).image (insert a)) := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    rcases Finset.mem_image.mp hv with ⟨v, hv, rfl⟩
    exact ha ((Finset.mem_powersetCard.mp hu).1 (Finset.mem_insert_self a v))
  rw [Finset.sum_union hdis, Finset.sum_image]
  · congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    have hau : a ∉ u := fun h => ha ((Finset.mem_powersetCard.mp hu).1 h)
    rw [Finset.prod_insert hau]
  · intro u hu v hv huv
    have hau : a ∉ u := fun h => ha ((Finset.mem_powersetCard.mp hu).1 h)
    have hav : a ∉ v := fun h => ha ((Finset.mem_powersetCard.mp hv).1 h)
    have he := congrArg (fun t : Finset ι => t.erase a) huv
    simpa [Finset.erase_insert hau, Finset.erase_insert hav] using he

omit [DecidableEq ι] in
@[simp] theorem truncation_zero (s : Finset ι) (w : ι → ℝ) :
    truncation s w 0 = 1 := by
  simp [truncation]

omit [DecidableEq ι] in
@[simp] theorem truncation_empty (w : ι → ℝ) (m : ℕ) :
    truncation ∅ w m = 1 := by
  induction m with
  | zero => simp
  | succ m ih => simpa [truncation, Finset.sum_range_succ] using ih

theorem truncation_insert {s : Finset ι} {a : ι} (ha : a ∉ s)
    (w : ι → ℝ) (m : ℕ) :
    truncation (insert a s) w (m + 1) =
      truncation s w (m + 1) - w a * truncation s w m := by
  have hsucc (t : Finset ι) (j : ℕ) :
      truncation t w (j + 1) = truncation t w j +
        (-1 : ℝ) ^ (j + 1) * elementary t w (j + 1) := by
    simp [truncation, Finset.sum_range_succ]
  induction m with
  | zero =>
    rw [hsucc, hsucc, elementary_insert ha]
    simp only [truncation_zero, elementary_zero, zero_add, pow_one, neg_one_mul,
      mul_one]
    ring
  | succ m ih =>
    rw [hsucc (insert a s), ih, elementary_insert ha w (m + 1),
      hsucc s (m + 1), hsucc s m]
    rw [pow_succ, pow_succ]
    ring

omit [DecidableEq ι] in
theorem elementary_nonneg (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (m : ℕ) : 0 ≤ elementary s w m := by
  apply Finset.sum_nonneg
  intro u hu
  apply Finset.prod_nonneg
  intro i hi
  exact hw i ((Finset.mem_powersetCard.mp hu).1 hi)

omit [DecidableEq ι] in
theorem prod_one_sub_mem_unit (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ 1) :
    0 ≤ (∏ i ∈ s, (1 - w i)) ∧ (∏ i ∈ s, (1 - w i)) ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun i hi => sub_nonneg.mpr (hw i hi).2)
  · exact fareyProdOne (fun i hi => sub_nonneg.mpr (hw i hi).2)
      (fun i hi => by linarith [(hw i hi).1])

theorem one_sub_prod_le_elementary_one (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ 1) :
    1 - (∏ i ∈ s, (1 - w i)) ≤ elementary s w 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hwa := hw a (Finset.mem_insert_self a s)
    have hws : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ 1 :=
      fun i hi => hw i (Finset.mem_insert_of_mem hi)
    have hp := prod_one_sub_mem_unit s w hws
    have hh := ih hws
    rw [Finset.prod_insert ha, elementary_insert ha]
    simp only [elementary_zero, mul_one]
    nlinarith

/-- Bonferroni's inequalities: for weights `0 ≤ w i ≤ 1` and the truncation `T_m` at rank `m`,
`0 ≤ (-1)^m (T_m - ∏_{i ∈ s} (1 - w i)) ≤ e_{m+1}(w)`. -/
theorem bonferroni (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ 1) (m : ℕ) :
    0 ≤ (-1 : ℝ) ^ m * (truncation s w m - ∏ i ∈ s, (1 - w i)) ∧
      (-1 : ℝ) ^ m * (truncation s w m - ∏ i ∈ s, (1 - w i)) ≤
        elementary s w (m + 1) := by
  induction s using Finset.induction_on generalizing m with
  | empty => simp
  | @insert a s ha ih =>
    have hwa := hw a (Finset.mem_insert_self a s)
    have hws : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ 1 :=
      fun i hi => hw i (Finset.mem_insert_of_mem hi)
    cases m with
    | zero =>
      simp only [pow_zero, truncation_zero, one_mul, zero_add]
      exact ⟨by linarith [(prod_one_sub_mem_unit (insert a s) w hw).2],
        one_sub_prod_le_elementary_one (insert a s) w hw⟩
    | succ m =>
      have h₁ := ih hws (m + 1)
      have h₀ := ih hws m
      rw [truncation_insert ha, Finset.prod_insert ha,
        elementary_insert ha w (m + 1)]
      have hidentity : (-1 : ℝ) ^ (m + 1) *
          (truncation s w (m + 1) - w a * truncation s w m -
            (1 - w a) * ∏ i ∈ s, (1 - w i)) =
          (-1 : ℝ) ^ (m + 1) *
            (truncation s w (m + 1) - ∏ i ∈ s, (1 - w i)) +
          w a * ((-1 : ℝ) ^ m *
            (truncation s w m - ∏ i ∈ s, (1 - w i))) := by
        rw [pow_succ]
        ring
      rw [hidentity]
      constructor
      · exact add_nonneg h₁.1 (mul_nonneg hwa.1 h₀.1)
      · exact add_le_add h₁.2 (mul_le_mul_of_nonneg_left h₀.2 hwa.1)

/-! ## Bounds for elementary symmetric sums -/

theorem elementary_one (P : Finset ι) (w : ι → ℝ) :
    elementary P w 1 = ∑ i ∈ P, w i := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert a P ha ih =>
    rw [elementary_insert ha, elementary_zero, ih, Finset.sum_insert ha]
    ring

theorem elementary_succ_mul_le (P : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ P, 0 ≤ w i) (m : ℕ) :
    ((m + 1 : ℕ) : ℝ) * elementary P w (m + 1) ≤
      (∑ i ∈ P, w i) * elementary P w m := by
  induction P using Finset.induction_on generalizing m with
  | empty => simp
  | @insert a P ha ih =>
    have hwa : 0 ≤ w a := hw a (Finset.mem_insert_self _ _)
    have hwp : ∀ i ∈ P, 0 ≤ w i := fun i hi => hw i (Finset.mem_insert_of_mem hi)
    cases m with
    | zero => simp [elementary_one]
    | succ m =>
      have h1 := ih hwp (m + 1)
      have h0 := ih hwp m
      have he := elementary_nonneg P w hwp m
      rw [elementary_insert ha w (m + 1), elementary_insert ha w m,
        Finset.sum_insert ha]
      have hd :
          (w a + ∑ i ∈ P, w i) *
              (elementary P w (m + 1) + w a * elementary P w m) -
              ((m + 1 + 1 : ℕ) : ℝ) *
                (elementary P w (m + 1 + 1) + w a * elementary P w (m + 1)) =
            ((∑ i ∈ P, w i) * elementary P w (m + 1) -
              ((m + 1 + 1 : ℕ) : ℝ) * elementary P w (m + 1 + 1)) +
            w a * ((∑ i ∈ P, w i) * elementary P w m -
              ((m + 1 : ℕ) : ℝ) * elementary P w (m + 1)) +
            w a * w a * elementary P w m := by
        push_cast
        ring
      apply sub_nonneg.mp
      rw [hd]
      exact add_nonneg
        (add_nonneg (sub_nonneg.mpr h1) (mul_nonneg hwa (sub_nonneg.mpr h0)))
        (mul_nonneg (mul_nonneg hwa hwa) he)

theorem elementary_le_sum_pow_div_factorial (P : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ P, 0 ≤ w i) (m : ℕ) :
    elementary P w m ≤ (∑ i ∈ P, w i) ^ m / (Nat.factorial m : ℝ) := by
  have hsum : 0 ≤ ∑ i ∈ P, w i := Finset.sum_nonneg hw
  have hmul : ∀ m : ℕ,
      (Nat.factorial m : ℝ) * elementary P w m ≤ (∑ i ∈ P, w i) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hrec := elementary_succ_mul_le P w hw m
      calc
        (Nat.factorial (m + 1) : ℝ) * elementary P w (m + 1) =
            (Nat.factorial m : ℝ) *
              (((m + 1 : ℕ) : ℝ) * elementary P w (m + 1)) := by
          rw [Nat.factorial_succ, Nat.cast_mul]
          ring
        _ ≤ (Nat.factorial m : ℝ) * ((∑ i ∈ P, w i) * elementary P w m) :=
          mul_le_mul_of_nonneg_left hrec (Nat.cast_nonneg _)
        _ = (∑ i ∈ P, w i) * ((Nat.factorial m : ℝ) * elementary P w m) := by ring
        _ ≤ (∑ i ∈ P, w i) * (∑ i ∈ P, w i) ^ m :=
          mul_le_mul_of_nonneg_left ih hsum
        _ = (∑ i ∈ P, w i) ^ (m + 1) := by rw [pow_succ]; ring
  apply (le_div_iff₀ (show (0 : ℝ) < Nat.factorial m by positivity)).mpr
  simpa [mul_comm] using hmul m

end ErdosStraus.RoughEstimates

namespace ErdosStraus.BrunHooley

open Classical RoughEstimates
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]

/-! ## The block sieve -/

/-- The subsets of `P` with at most `r` elements. -/
noncomputable def smallSubsets (P : Finset α) (r : ℕ) : Finset (Finset α) :=
  P.powerset.filter (fun s => s.card ≤ r)

/-- The families `f` with `f j ⊆ P j` and `|f j| ≤ r j` for every block `j`. -/
noncomputable def choices (P : ι → Finset α) (r : ι → ℕ) :
    Finset (ι → Finset α) := Fintype.piFinset (fun j => smallSubsets (P j) (r j))

/-- The union `⋃_j f j` of a family of subsets. -/
noncomputable def selected (f : ι → Finset α) : Finset α := Finset.univ.biUnion f

/-- The sign `∏_j (-1)^{|f j|}` of a family of subsets. -/
noncomputable def sign (f : ι → Finset α) : ℝ := ∏ j, (-1 : ℝ) ^ (f j).card

omit [DecidableEq α] in
theorem mem_choices {P : ι → Finset α} {r : ι → ℕ} {f : ι → Finset α} :
    f ∈ choices P r ↔ ∀ j, f j ⊆ P j ∧ (f j).card ≤ r j := by
  simp [choices, smallSubsets]

omit [DecidableEq α] in
theorem truncation_eq_smallSubsets (P : Finset α) (w : α → ℝ) (r : ℕ) :
    truncation P w r = ∑ s ∈ smallSubsets P r,
      (-1 : ℝ) ^ s.card * ∏ p ∈ s, w p := by
  have hm : ∀ s ∈ smallSubsets P r, s.card ∈ Finset.range (r + 1) := by
    intro s hs
    exact Finset.mem_range.mpr (by
      have := (Finset.mem_filter.mp hs).2
      omega)
  have hf := Finset.sum_fiberwise_of_maps_to hm
    (fun s : Finset α => (-1 : ℝ) ^ s.card * ∏ p ∈ s, w p)
  rw [← hf]
  unfold truncation elementary
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  have hset : (smallSubsets P r).filter (fun s => s.card = j) = P.powersetCard j := by
    ext s
    simp only [smallSubsets, Finset.mem_filter, Finset.mem_powerset,
      Finset.mem_powersetCard]
    have hjr : j ≤ r := by have := Finset.mem_range.mp hj; omega
    constructor
    · rintro ⟨⟨hs, _⟩, he⟩
      exact ⟨hs, he⟩
    · rintro ⟨hs, he⟩
      exact ⟨⟨hs, he.le.trans hjr⟩, he⟩
  rw [hset]
  apply Finset.sum_congr rfl
  intro s hs
  rw [(Finset.mem_powersetCard.mp hs).2]

omit [DecidableEq α] in
theorem prod_truncation_eq_sum_choices (P : ι → Finset α) (w : α → ℝ) (r : ι → ℕ) :
    (∏ j, truncation (P j) w (r j)) =
      ∑ f ∈ choices P r, sign f * ∏ j, ∏ p ∈ f j, w p := by
  simp_rw [truncation_eq_smallSubsets]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro f hf
  exact Finset.prod_mul_distrib

theorem even_truncation_nonneg (P : Finset α) (w : α → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p ∧ w p ≤ 1) (r : ℕ) :
    0 ≤ truncation P w (2 * r) := by
  have hb := (bonferroni P w hw (2 * r)).1
  have hv : 0 ≤ ∏ p ∈ P, (1 - w p) :=
    Finset.prod_nonneg (fun p hp => sub_nonneg.mpr (hw p hp).2)
  simp only [pow_mul, neg_one_sq, one_pow, one_mul] at hb
  linarith

omit [DecidableEq ι] in
theorem product_even_truncations_ge_product (P : ι → Finset α) (w : α → ℝ)
    (hw : ∀ j p, p ∈ P j → 0 ≤ w p ∧ w p ≤ 1) (r : ι → ℕ) :
    (∏ j, ∏ p ∈ P j, (1 - w p)) ≤
      ∏ j, truncation (P j) w (2 * r j) := by
  apply fareyProdLe
  · intro j hj
    exact Finset.prod_nonneg (fun p hp => sub_nonneg.mpr (hw j p hp).2)
  · intro j hj
    have hb := (bonferroni (P j) w (hw j) (2 * r j)).1
    simp only [pow_mul, neg_one_sq, one_pow, one_mul] at hb
    linarith

omit [DecidableEq ι] [DecidableEq α] in
theorem product_indicator (P : ι → Finset α) (hit : α → Prop) :
    (∏ j, ∏ p ∈ P j, (1 - if hit p then (1 : ℝ) else 0)) =
      if ∀ j p, p ∈ P j → ¬ hit p then 1 else 0 := by
  classical
  by_cases h : ∀ j p, p ∈ P j → ¬ hit p
  · have he : (∏ j, ∏ p ∈ P j, (1 - if hit p then (1 : ℝ) else 0)) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      exact Finset.prod_eq_one (fun p hp => by simp [h j p hp])
    exact he.trans (if_pos h).symm
  · have hn := h
    push Not at h
    obtain ⟨j, p, hp, hhit⟩ := h
    have he : (∏ j, ∏ p ∈ P j, (1 - if hit p then (1 : ℝ) else 0)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      exact Finset.prod_eq_zero hp (by simp [hhit])
    exact he.trans (if_neg hn).symm

omit [DecidableEq ι] in
theorem sift_indicator_le_weight (P : ι → Finset α) (hit : α → Prop) (r : ι → ℕ) :
    (if ∀ j p, p ∈ P j → ¬ hit p then (1 : ℝ) else 0) ≤
      ∏ j, truncation (P j) (fun p => if hit p then 1 else 0) (2 * r j) := by
  rw [← product_indicator]
  apply product_even_truncations_ge_product
  intro j p hp
  split_ifs <;> norm_num

omit [DecidableEq ι] [DecidableEq α] in
theorem abs_sign (f : ι → Finset α) : |sign f| = 1 := by
  simp [sign, Finset.abs_prod]

theorem block_truncation_upper (P : Finset α) (w : α → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p ∧ w p ≤ 1) (r : ℕ) :
    truncation P w (2 * r) ≤ (∏ p ∈ P, (1 - w p)) +
      (∑ p ∈ P, w p) ^ (2 * r + 1) / ((2 * r + 1).factorial : ℝ) := by
  have hb := (bonferroni P w hw (2 * r)).2
  simp only [pow_mul, neg_one_sq, one_pow, one_mul] at hb
  have he := elementary_le_sum_pow_div_factorial P w
    (fun p hp => (hw p hp).1) (2 * r + 1)
  linarith

theorem selected_inter_block (P : ι → Finset α)
    (hP : Pairwise (fun j k => Disjoint (P j) (P k))) (r : ι → ℕ)
    {f : ι → Finset α} (hf : f ∈ choices P r) (j : ι) :
    selected f ∩ P j = f j := by
  have hmem := mem_choices.mp hf
  ext p
  simp only [Finset.mem_inter, selected, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨k, hpk⟩, hpj⟩
    by_cases hkj : k = j
    · simpa [hkj] using hpk
    · exact False.elim (Finset.disjoint_left.mp (hP hkj) ((hmem k).1 hpk) hpj)
  · intro hp
    exact ⟨⟨j, hp⟩, (hmem j).1 hp⟩

theorem choices_selected_injOn (P : ι → Finset α)
    (hP : Pairwise (fun j k => Disjoint (P j) (P k))) (r : ι → ℕ) :
    Set.InjOn selected (choices P r : Set (ι → Finset α)) := by
  intro f hf g hg he
  funext j
  rw [← selected_inter_block P hP r hf j, ← selected_inter_block P hP r hg j, he]

/-- The product of the selected primes, the divisor `d = ∏_j d_j` of the expansion. -/
noncomputable def selectedProduct (f : ι → Finset ℕ) : ℕ := ∏ p ∈ selected f, p

theorem selected_primes {P : ι → Finset ℕ} {r : ι → ℕ}
    (hP : ∀ j p, p ∈ P j → Nat.Prime p) {f : ι → Finset ℕ}
    (hf : f ∈ choices P r) : ∀ p ∈ selected f, Nat.Prime p := by
  intro p hp
  obtain ⟨j, _, hp⟩ := Finset.mem_biUnion.mp hp
  exact hP j p ((mem_choices.mp hf j).1 hp)

theorem selectedProduct_pos {P : ι → Finset ℕ} {r : ι → ℕ}
    (hP : ∀ j p, p ∈ P j → Nat.Prime p) {f : ι → Finset ℕ}
    (hf : f ∈ choices P r) : 0 < selectedProduct f :=
  Finset.prod_pos (fun p hp => (selected_primes hP hf p hp).pos)

theorem choices_product_injOn (P : ι → Finset ℕ)
    (hP : ∀ j p, p ∈ P j → Nat.Prime p)
    (hdisj : Pairwise (fun j k => Disjoint (P j) (P k))) (r : ι → ℕ) :
    Set.InjOn selectedProduct (choices P r : Set (ι → Finset ℕ)) := by
  intro f hf g hg he
  apply choices_selected_injOn P hdisj r hf hg
  have hpf := Nat.primeFactors_prod (selected_primes hP hf)
  have hpg := Nat.primeFactors_prod (selected_primes hP hg)
  exact hpf.symm.trans ((congrArg Nat.primeFactors he).trans hpg)

theorem choices_card_le_of_product_le (P : ι → Finset ℕ)
    (hP : ∀ j p, p ∈ P j → Nat.Prime p)
    (hdisj : Pairwise (fun j k => Disjoint (P j) (P k))) (r : ι → ℕ) (W : ℕ)
    (hW : ∀ f ∈ choices P r, selectedProduct f ≤ W) :
    (choices P r).card ≤ W := by
  have hsub : (choices P r).image selectedProduct ⊆ Finset.Icc 1 W := by
    intro d hd
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_Icc.mpr ⟨selectedProduct_pos hP hf, hW f hf⟩
  calc
    _ = ((choices P r).image selectedProduct).card :=
      (Finset.card_image_of_injOn (choices_product_injOn P hP hdisj r)).symm
    _ ≤ (Finset.Icc 1 W).card := Finset.card_le_card hsub
    _ = W := by simp

theorem selectedProduct_eq_block_products (P : ι → Finset ℕ)
    (hdisj : Pairwise (fun j k => Disjoint (P j) (P k))) (r : ι → ℕ)
    {f : ι → Finset ℕ} (hf : f ∈ choices P r) :
    selectedProduct f = ∏ j, ∏ p ∈ f j, p := by
  apply Finset.prod_biUnion
  intro j hj k hk hjk
  exact Finset.disjoint_left.mpr (fun p hpj hpk =>
    Finset.disjoint_left.mp (hdisj hjk) ((mem_choices.mp hf j).1 hpj)
      ((mem_choices.mp hf k).1 hpk))

theorem selectedProduct_le_block_budget (P : ι → Finset ℕ)
    (hdisj : Pairwise (fun j k => Disjoint (P j) (P k))) (r : ι → ℕ)
    (B : ι → ℝ) (hB : ∀ j, 1 ≤ B j)
    (hbound : ∀ j p, p ∈ P j → (p : ℝ) ≤ B j)
    {f : ι → Finset ℕ} (hf : f ∈ choices P r) :
    (selectedProduct f : ℝ) ≤ ∏ j, (B j) ^ (r j) := by
  rw [selectedProduct_eq_block_products P hdisj r hf]
  push_cast
  apply fareyProdLe
  · intro j hj
    exact Finset.prod_nonneg (fun p hp => Nat.cast_nonneg p)
  · intro j hj
    calc
      _ ≤ ∏ _p ∈ f j, B j := fareyProdLe
        (fun p hp => Nat.cast_nonneg p)
        (fun p hp => hbound j p ((mem_choices.mp hf j).1 hp))
      _ = (B j) ^ (f j).card := by simp
      _ ≤ (B j) ^ r j := pow_le_pow_right₀ (hB j) (mem_choices.mp hf j).2

omit [DecidableEq ι] [DecidableEq α] in
theorem product_hit_indicator (P : ι → Finset α) (hit : α → Prop) :
    (∏ j, ∏ p ∈ P j, if hit p then (1 : ℝ) else 0) =
      if ∀ j p, p ∈ P j → hit p then 1 else 0 := by
  by_cases h : ∀ j p, p ∈ P j → hit p
  · have he : (∏ j, ∏ p ∈ P j, if hit p then (1 : ℝ) else 0) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      exact Finset.prod_eq_one (fun p hp => by simp [h j p hp])
    exact he.trans (if_pos h).symm
  · have hn := h
    push Not at h
    obtain ⟨j, p, hp, hhit⟩ := h
    have he : (∏ j, ∏ p ∈ P j, if hit p then (1 : ℝ) else 0) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      exact Finset.prod_eq_zero hp (by simp [hhit])
    exact he.trans (if_neg hn).symm

theorem sum_block_weights {β : Type*} [DecidableEq β] (A : Finset β)
    (P : ι → Finset α) (hit : α → β → Prop) (r : ι → ℕ) :
    (∑ n ∈ A, ∏ j, truncation (P j) (fun p => if hit p n then 1 else 0) (r j)) =
      ∑ f ∈ choices P r, sign f * intersectionCount A hit (selected f) := by
  simp_rw [prod_truncation_eq_sum_choices]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f hf
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [product_hit_indicator]
  have he (n : β) : (∀ j p, p ∈ f j → hit p n) ↔
      (∀ p ∈ selected f, hit p n) := by
    simp only [selected, Finset.mem_biUnion, Finset.mem_univ, true_and]
    aesop
  simp_rw [he]
  simp [intersectionCount]

theorem weighted_geometric_budget (n : ℕ) :
    ∑ j ∈ Finset.range n, (2 * (j + 1 : ℝ)) / 2 ^ j ≤ 8 := by
  have he : (∑ j ∈ Finset.range n, (2 * (j + 1 : ℝ)) / 2 ^ j) =
      8 - (4 * (n : ℝ) + 8) / 2 ^ n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      push_cast
      field_simp
      ring
  rw [he]
  exact sub_le_self 8 (by positivity)

/-- For blocks with `p ≤ w^{2^{-j}}` and ranks `2(j+1)`, every expanded divisor is at most
`∏_j w^{2(j+1)/2^j} ≤ w^8`. -/
theorem geometric_block_support (n : ℕ) (P : Fin n → Finset ℕ)
    (hdisj : Pairwise (fun j k => Disjoint (P j) (P k))) (w : ℝ) (hw : 1 ≤ w)
    (hbound : ∀ j p, p ∈ P j → (p : ℝ) ≤ w ^ ((2 : ℝ) ^ (j : ℕ))⁻¹)
    {f : Fin n → Finset ℕ}
    (hf : f ∈ choices P (fun j => 2 * ((j : ℕ) + 1))) :
    (selectedProduct f : ℝ) ≤ w ^ 8 := by
  have hwpos : 0 < w := zero_lt_one.trans_le hw
  have hb (j : Fin n) : 1 ≤ w ^ ((2 : ℝ) ^ (j : ℕ))⁻¹ :=
    Real.one_le_rpow hw (by positivity)
  have hh := selectedProduct_le_block_budget P hdisj (fun j => 2 * ((j : ℕ) + 1))
    (fun j => w ^ ((2 : ℝ) ^ (j : ℕ))⁻¹) hb hbound hf
  have he : (∏ j : Fin n, (w ^ ((2 : ℝ) ^ (j : ℕ))⁻¹) ^ (2 * ((j : ℕ) + 1))) =
      w ^ (∑ j ∈ Finset.range n, (2 * (j + 1 : ℝ)) / 2 ^ j) := by
    have hexp (j : Fin n) : (w ^ ((2 : ℝ) ^ (j : ℕ))⁻¹) ^ (2 * ((j : ℕ) + 1)) =
        w ^ (((2 : ℝ) ^ (j : ℕ))⁻¹ * (2 * ((j : ℕ) + 1) : ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hwpos.le]
    simp_rw [hexp]
    rw [← Real.rpow_sum_of_pos hwpos]
    congr 1
    calc
      _ = ∑ j : Fin n, (2 * ((j : ℕ) + 1 : ℝ)) / 2 ^ (j : ℕ) := by
        apply Finset.sum_congr rfl
        intro j hj
        push_cast
        ring
      _ = _ := Fin.sum_univ_eq_sum_range
        (fun j : ℕ => 2 * ((j : ℝ) + 1) / (2 : ℝ) ^ j) n
  rw [he] at hh
  apply hh.trans
  rw [← Real.rpow_natCast w 8]
  exact Real.rpow_le_rpow_of_exponent_le hw (weighted_geometric_budget n)

/-! ## Comparison with the Euler product -/

omit [DecidableEq ι] in
theorem product_truncation_upper (P : ι → Finset α) (w : α → ℝ)
    (hw : ∀ j p, p ∈ P j → 0 ≤ w p ∧ w p < 1) (r : ι → ℕ) :
    (∏ j, truncation (P j) w (2 * r j)) ≤
      (∏ j, ∏ p ∈ P j, (1 - w p)) * Real.exp
        (∑ j, ((∑ p ∈ P j, w p) ^ (2 * r j + 1) /
          ((2 * r j + 1).factorial : ℝ)) / (∏ p ∈ P j, (1 - w p))) := by
  let V : ι → ℝ := fun j => ∏ p ∈ P j, (1 - w p)
  let F : ι → ℝ := fun j => (∑ p ∈ P j, w p) ^ (2 * r j + 1) /
    ((2 * r j + 1).factorial : ℝ)
  have hV (j : ι) : 0 < V j :=
    Finset.prod_pos (fun p hp => sub_pos.mpr (hw j p hp).2)
  have hprod : (∏ j, truncation (P j) w (2 * r j)) ≤
      ∏ j, V j * Real.exp (F j / V j) := by
    apply fareyProdLe
    · intro j hj
      exact even_truncation_nonneg _ _ (fun p hp => ⟨(hw j p hp).1,
        (hw j p hp).2.le⟩) _
    · intro j hj
      have hb := block_truncation_upper (P j) w
        (fun p hp => ⟨(hw j p hp).1, (hw j p hp).2.le⟩) (r j)
      apply hb.trans
      have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (F j / V j)) (hV j).le
      have hcancel : V j * (F j / V j + 1) = V j + F j := by
        field_simp [(hV j).ne']
        ring
      rwa [hcancel] at he
  rw [Finset.prod_mul_distrib, ← Real.exp_sum] at hprod
  exact hprod

theorem factorial_odd_tail_sum_le_exp (n : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    (∑ j : Fin n, H ^ (2 * (j : ℕ) + 3) /
      ((2 * (j : ℕ) + 3).factorial : ℝ)) ≤ Real.exp H := by
  let S := (Finset.range n).image (fun j => 2 * j + 3)
  have hinj : Function.Injective (fun j : ℕ => 2 * j + 3) := by
    intro j k h
    change 2 * j + 3 = 2 * k + 3 at h
    omega
  have hsub : S ⊆ Finset.range (2 * n + 3) := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega)
  calc
    _ = ∑ j ∈ Finset.range n, H ^ (2 * j + 3) / ((2 * j + 3).factorial : ℝ) :=
      Fin.sum_univ_eq_sum_range _ _
    _ = ∑ k ∈ S, H ^ k / (k.factorial : ℝ) := by
      rw [Finset.sum_image (fun a _ b _ hab => hinj hab)]
    _ ≤ ∑ k ∈ Finset.range (2 * n + 3), H ^ k / (k.factorial : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
    _ ≤ Real.exp H := Real.sum_le_exp_of_nonneg hH _

/-- With truncation ranks `t_j = 2(j+1)`, `∏_j T_j ≤ ∏_j W_j · exp(e^H/v)` when every
block has `∑ w(p) ≤ H` and Euler factor `W_j = ∏ (1 - w(p)) ≥ v`. -/
theorem product_truncation_le_uniform_factor (n : ℕ) (P : Fin n → Finset α)
    (w : α → ℝ) (hw : ∀ j p, p ∈ P j → 0 ≤ w p ∧ w p < 1)
    (H v : ℝ) (hH : 0 ≤ H) (hv : 0 < v)
    (hSum : ∀ j, (∑ p ∈ P j, w p) ≤ H)
    (hEuler : ∀ j, v ≤ ∏ p ∈ P j, (1 - w p)) :
    (∏ j, truncation (P j) w (2 * ((j : ℕ) + 1))) ≤
      (∏ j, ∏ p ∈ P j, (1 - w p)) * Real.exp (Real.exp H / v) := by
  apply (product_truncation_upper P w hw (fun j => (j : ℕ) + 1)).trans
  apply mul_le_mul_of_nonneg_left _
    (Finset.prod_nonneg (fun j hj => Finset.prod_nonneg
      (fun p hp => (sub_pos.mpr (hw j p hp).2).le)))
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ∑ j : Fin n, (H ^ (2 * (j : ℕ) + 3) /
        ((2 * (j : ℕ) + 3).factorial : ℝ)) / v := by
      apply Finset.sum_le_sum
      intro j hj
      have hdeg : 2 * ((j : ℕ) + 1) + 1 = 2 * (j : ℕ) + 3 := by omega
      rw [hdeg]
      apply div_le_div₀
      · positivity
      · exact div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (Finset.sum_nonneg (fun p hp => (hw j p hp).1)) (hSum j) _)
          (by positivity)
      · exact hv
      · exact hEuler j
    _ = (∑ j : Fin n, H ^ (2 * (j : ℕ) + 3) /
        ((2 * (j : ℕ) + 3).factorial : ℝ)) / v := (Finset.sum_div _ _ _).symm
    _ ≤ Real.exp H / v := div_le_div_of_nonneg_right
      (factorial_odd_tail_sum_le_exp n H hH) hv.le

omit [DecidableEq α] in
theorem euler_product_lower_of_sum_bound (P : Finset α) (w : α → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p ∧ w p ≤ 1 / 2) (H : ℝ)
    (hSum : (∑ p ∈ P, w p) ≤ H) :
    Real.exp (-2 * H) ≤ ∏ p ∈ P, (1 - w p) := by
  have hpoint (p : α) (hp : p ∈ P) : Real.exp (-2 * w p) ≤ 1 - w p := by
    have hpos : 0 < 1 - w p := by linarith [(hw p hp).2]
    have hinv : (1 - w p)⁻¹ ≤ 2 := by
      have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2)
        (by linarith [(hw p hp).2] : (1 / 2 : ℝ) ≤ 1 - w p)
      norm_num only [one_div, inv_div, inv_one, mul_one] at hh
      exact hh
    have hmul := inv_mul_cancel₀ hpos.ne'
    have hh := mul_le_mul_of_nonneg_left hinv (hw p hp).1
    have hlog := Real.one_sub_inv_le_log_of_pos hpos
    apply (Real.le_log_iff_exp_le hpos).mp
    nlinarith
  calc
    _ ≤ Real.exp (∑ p ∈ P, -2 * w p) := by
      apply Real.exp_le_exp.mpr
      rw [← Finset.mul_sum]
      linarith
    _ = ∏ p ∈ P, Real.exp (-2 * w p) := Real.exp_sum _ _
    _ ≤ _ := fareyProdLe (fun p hp => (Real.exp_pos _).le) hpoint

end ErdosStraus.BrunHooley

namespace FareyBrun
open Finset ErdosStraus.RoughEstimates ErdosStraus.BrunHooley
open scoped BigOperators
noncomputable section
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]

def box (P : ι → Finset α) (w : α → ℝ) (r : ι → ℕ) : ℝ :=
  ∏ j, truncation (P j) w (r j)

def lower (P : ι → Finset α) (w : α → ℝ) (r : ι → ℕ) : ℝ :=
  let k := fun j => 2 * r j
  box P w k - ∑ j, (box P w k - box P w (Function.update k j (k j + 1)))

theorem box_difference (P : ι → Finset α) (w : α → ℝ) (r : ι → ℕ) (j : ι) :
    let k := fun j => 2 * r j
    box P w k - box P w (Function.update k j (k j + 1)) =
      elementary (P j) w (k j + 1) *
      ∏ i ∈ univ.erase j, truncation (P i) w (k i) := by
  dsimp only
  let k := fun j => 2 * r j
  change box P w k - box P w (Function.update k j (k j + 1)) = _
  unfold box
  rw [← mul_prod_erase univ _ (mem_univ j), ← mul_prod_erase univ
    (fun i => truncation (P i) w (Function.update k j (k j + 1) i)) (mem_univ j)]
  simp only [Function.update_self]
  have he : (∏ i ∈ univ.erase j, truncation (P i) w (Function.update k j (k j + 1) i)) =
      ∏ i ∈ univ.erase j, truncation (P i) w (k i) := by
    apply prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (ne_of_mem_erase hi)]
  rw [he]
  have ht : truncation (P j) w (k j + 1) =
      truncation (P j) w (k j) - elementary (P j) w (k j + 1) := by
    unfold truncation
    rw [sum_range_succ]
    simp [k, pow_succ, pow_mul, sub_eq_add_neg]
  rw [ht]
  ring

theorem lower_as_error (P : ι → Finset α) (w : α → ℝ) (r : ι → ℕ) :
    lower P w r = box P w (fun j => 2*r j) -
      ∑ j, elementary (P j) w (2*r j+1) *
        ∏ i ∈ univ.erase j, truncation (P i) w (2*r i) := by
  unfold lower
  dsimp only
  congr 1
  exact sum_congr rfl (fun j _ => box_difference P w r j)

theorem lower_indicator (P : ι → Finset α) (hit : α → Prop) [DecidablePred hit]
    (r : ι → ℕ) :
    lower P (fun p => if hit p then 1 else 0) r ≤
      if ∀ j p, p ∈ P j → ¬ hit p then (1:ℝ) else 0 := by
  classical
  let w := fun p => if hit p then (1:ℝ) else 0
  have hw (p : α) : 0 ≤ w p ∧ w p ≤ 1 := by simp only [w]; split <;> norm_num
  let T := fun j => truncation (P j) w (2*r j)
  let E := fun j => elementary (P j) w (2*r j+1)
  have ht (j : ι) : 0 ≤ T j := even_truncation_nonneg _ _ (fun p _ => hw p) _
  have he (j : ι) : 0 ≤ E j := elementary_nonneg _ _ (fun p _ => (hw p).1) _
  rw [lower_as_error]
  change (∏ j, T j) - ∑ j, E j * (∏ i ∈ univ.erase j, T i) ≤ _
  split_ifs with hall
  · have htone (j : ι) : T j ≤ 1 := by
      have hzero : E j = 0 := by
        apply le_antisymm _ (he j)
        apply (elementary_le_sum_pow_div_factorial _ _ (fun p _ => (hw p).1) _).trans
        have hz : ∑ p ∈ P j, w p = 0 := sum_eq_zero (fun p hp => if_neg (hall j p hp))
        rw [hz, zero_pow (by omega : 2*r j+1 ≠ 0), zero_div]
      have hb := (bonferroni (P j) w (fun p _ => hw p) (2*r j)).2
      change _ ≤ E j at hb
      rw [hzero] at hb
      simp only [pow_mul, neg_one_sq, one_pow, one_mul] at hb
      exact (sub_nonpos.mp hb).trans (prod_one_sub_mem_unit _ _ (fun p _ => hw p)).2
    exact (sub_le_self _ (sum_nonneg (fun j _ => mul_nonneg (he j) (prod_nonneg (fun i _ => ht i))))).trans
      (fareyProdOne (fun j _ => ht j) (fun j _ => htone j))
  · push Not at hall
    obtain ⟨j,p,hp,hh⟩ := hall
    have hz : ∏ i ∈ P j, (1-w i) = 0 := prod_eq_zero hp (by simp [w,hh])
    have hb := (bonferroni (P j) w (fun p _ => hw p) (2*r j)).2
    simp only [pow_mul, neg_one_sq, one_pow, one_mul, hz, sub_zero] at hb
    have hsingle := single_le_sum (f := fun j => E j * ∏ i ∈ univ.erase j, T i)
      (fun j _ => mul_nonneg (he j) (prod_nonneg (fun i _ => ht i))) (mem_univ j)
    have hcross := mul_le_mul_of_nonneg_right hb (prod_nonneg (fun i (_ : i ∈ univ.erase j) => ht i))
    apply sub_nonpos.mpr
    rw [← mul_prod_erase univ T (mem_univ j)]
    exact hcross.trans hsingle
end
end FareyBrun
namespace FareyBrun
open Finset ErdosStraus.RoughEstimates ErdosStraus.BrunHooley
open scoped BigOperators
noncomputable section
variable {ι α β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α] [DecidableEq β]
attribute [local instance] Classical.propDecidable

theorem box_mean (A : Finset β) (P : ι → Finset α) (hit : α → β → Prop)
    (r : ι → ℕ) (w : α → ℝ) (X E : ℝ)
    (hround : ∀ f ∈ choices P r, |intersectionCount A hit (selected f) -
      X * ∏ j, ∏ p ∈ f j, w p| ≤ E) :
    |(∑ u ∈ A, box P (fun p => if hit p u then 1 else 0) r) - X * box P w r| ≤
      (choices P r).card * E := by
  unfold box
  rw [sum_block_weights, prod_truncation_eq_sum_choices, Finset.mul_sum, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _f ∈ choices P r, E := by
      apply sum_le_sum
      intro f hf
      rw [show sign f * intersectionCount A hit (selected f) -
        X * (sign f * ∏ j, ∏ p ∈ f j, w p) =
        sign f * (intersectionCount A hit (selected f) - X * ∏ j, ∏ p ∈ f j, w p) by ring,
        abs_mul, abs_sign, one_mul]
      exact hround f hf
    _ = _ := by simp

theorem lower_count (A : Finset β) (P : ι → Finset α) (hit : α → β → Prop)
    (r : ι → ℕ) (w : α → ℝ) (X D : ℝ)
    (hbox : ∀ k : ι → ℕ, (∀ j, k j ≤ 2*r j+1) →
      |(∑ u ∈ A, box P (fun p => if hit p u then 1 else 0) k) - X * box P w k| ≤ D) :
    X * lower P w r - (1+2*(Fintype.card ι:ℝ))*D ≤
      ((A.filter (fun u => ∀ j p, p ∈ P j → ¬ hit p u)).card:ℝ) := by
  let k := fun j => 2*r j
  let v := fun j => Function.update k j (k j+1)
  let emp := fun l : ι → ℕ => ∑ u ∈ A, box P (fun p => if hit p u then 1 else 0) l
  let modl := fun l => X * box P w l
  have he0 := abs_le.mp (hbox k (fun j => Nat.le_succ _))
  have he1 (j : ι) : -(D:ℝ) ≤ emp (v j) - modl (v j) := by
    apply (abs_le.mp (hbox _ ?_)).1
    intro i
    by_cases hi : i = j
    · subst i; simp [v,k]
    · simp [v,k,Function.update_of_ne hi]
  have hh (j : ι) : emp k - emp (v j) ≤ (modl k - modl (v j)) + 2*D := by
    change -D ≤ emp k - modl k ∧ emp k - modl k ≤ D at he0
    linarith [he1 j]
  have hs := sum_le_sum (s := univ) (fun j _ => hh j)
  rw [sum_add_distrib] at hs
  simp only [sum_const,card_univ,nsmul_eq_mul] at hs
  have hpoint : ∑ u ∈ A, lower P (fun p => if hit p u then 1 else 0) r ≤
      ((A.filter (fun u => ∀ j p, p ∈ P j → ¬ hit p u)).card:ℝ) := by
    simpa using (sum_le_sum (s:=A) (fun u _ => lower_indicator P (fun p => hit p u) r))
  apply le_trans _ hpoint
  unfold lower
  dsimp only
  conv_rhs =>
    rw [sum_sub_distrib, sum_comm]
  simp_rw [Finset.sum_sub_distrib (s := A)]
  rw [mul_sub,Finset.mul_sum]
  simp_rw [mul_sub]
  change modl k - (∑ j, (modl k - modl (v j))) - _ ≤
    emp k - (∑ j, (emp k - emp (v j)))
  change -D ≤ emp k - modl k ∧ emp k - modl k ≤ D at he0
  linarith

theorem lower_model (P : ι → Finset α) (r : ι → ℕ) (w : α → ℝ)
    (hw : ∀ j p, p ∈ P j → 0 ≤ w p ∧ w p < 1) (e : ℝ)
    (he : (∑ j, ((∑ p ∈ P j, w p) ^ (2*r j+1) / ((2*r j+1).factorial : ℝ)) /
       (∏ p ∈ P j, (1-w p))) ≤ e) :
    (∏ j, ∏ p ∈ P j, (1-w p)) * (1-e*Real.exp e) ≤ lower P w r := by
  let T := fun j => truncation (P j) w (2*r j)
  let V := fun j => ∏ p ∈ P j, (1-w p)
  let F := fun j => (∑ p ∈ P j, w p) ^ (2*r j+1) / ((2*r j+1).factorial : ℝ)
  have hV (j : ι) : 0 < V j := prod_pos (fun p hp => sub_pos.mpr (hw j p hp).2)
  have hF (j : ι) : 0 ≤ F j := div_nonneg (pow_nonneg (sum_nonneg (fun p hp => (hw j p hp).1)) _) (by positivity)
  have hVT (j : ι) : V j ≤ T j := by
    have hb := (bonferroni (P j) w (fun p hp => ⟨(hw j p hp).1,(hw j p hp).2.le⟩) (2*r j)).1
    simpa [pow_mul,sub_nonneg] using hb
  have hT (j : ι) := (hV j).le.trans (hVT j)
  have hErr (j : ι) : elementary (P j) w (2*r j+1) * (∏ i ∈ univ.erase j, T i) ≤
      (F j / V j) * ∏ i, T i := by
    have hE := elementary_le_sum_pow_div_factorial (P j) w (fun p hp => (hw j p hp).1) (2*r j+1)
    rw [← mul_prod_erase univ T (mem_univ j), ← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (prod_nonneg (fun i _ => hT i))
    apply hE.trans
    calc F j = F j / V j * V j := (div_mul_cancel₀ _ (hV j).ne').symm
         _ ≤ _ := mul_le_mul_of_nonneg_left (hVT j) (div_nonneg (hF j) (hV j).le)
  have hs := sum_le_sum (s:=univ) (fun j _ => hErr j)
  rw [←sum_mul] at hs
  have hprod := product_truncation_upper P w hw r
  have hp0 : 0 ≤ ∏ j, V j := prod_nonneg (fun j _ => (hV j).le)
  have htotal : ∏ j, T j ≤ (∏ j, V j) * Real.exp e := hprod.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hp0)
  have he0 : 0 ≤ e := (sum_nonneg (fun j _ => div_nonneg (hF j) (hV j).le)).trans he
  have htot := mul_le_mul he htotal (prod_nonneg (fun j _ => hT j)) he0
  have hgood := fareyProdLe (s:=univ) (fun j _ => (hV j).le) (fun j _ => hVT j)
  rw [lower_as_error]
  change (∏ j, V j) * _ ≤ (∏ j, T j) - _
  linarith only [hs,htot,hgood]
end
end FareyBrun
namespace FareyBrun
open Finset ErdosStraus.RoughEstimates ErdosStraus.BrunHooley
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Finite lower sieve for blocks. The remainder is paid on squarefree selections;
the deterministic loss is controlled by the first omitted symmetric sum in each block. -/
theorem finite_block_lower {ι α β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    [DecidableEq β] (A : Finset β) (P : ι → Finset α) (hit : α → β → Prop)
    (r : ι → ℕ) (w : α → ℝ) (X D e : ℝ) (hX : 0 ≤ X)
    (hw : ∀ j p, p ∈ P j → 0 ≤ w p ∧ w p < 1)
    (htail : (∑ j, ((∑ p ∈ P j, w p) ^ (2*r j+1) / ((2*r j+1).factorial : ℝ)) /
       (∏ p ∈ P j, (1-w p))) ≤ e)
    (hround : ∀ k : ι → ℕ, (∀ j, k j ≤ 2*r j+1) →
      ∃ E : ℝ, (choices P k).card * E ≤ D ∧ ∀ f ∈ choices P k,
        |intersectionCount A hit (selected f) - X * ∏ j, ∏ p ∈ f j, w p| ≤ E) :
    X * ((∏ j, ∏ p ∈ P j, (1-w p)) * (1-e*Real.exp e)) -
      (1+2*(Fintype.card ι:ℝ))*D ≤
      ((A.filter (fun u => ∀ j p, p ∈ P j → ¬ hit p u)).card:ℝ) := by
  apply le_trans (sub_le_sub_right
    (mul_le_mul_of_nonneg_left (lower_model P r w hw e htail) hX) _)
  apply lower_count
  intro k hk
  obtain ⟨E,hE,hf⟩ := hround k hk
  exact (box_mean A P hit k w X E hf).trans hE

end
end FareyBrun
#print axioms FareyBrun.finite_block_lower
