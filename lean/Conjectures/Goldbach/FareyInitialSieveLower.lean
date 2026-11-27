import Mathlib
import Conjectures.Goldbach.FareyFullSieveRemainder
import Conjectures.Goldbach.FareySieveRootTotal
import Conjectures.Goldbach.FareySieveTerminalFloor
import Conjectures.Goldbach.FareySieveCutoffRatio

/-! # Farey initial lower sieve

We partition the sieving primes into geometric blocks and bound the Bonferroni
tail in each using its reciprocal prime mass. Squarefree divisors in the
truncated blocks have controlled total size. The four project inputs give the
intersection-count remainders, their sum, and comparison with the terminal mass.

The finite lower block inequality is adapted from GitHub user 34245621,
goldbach-proofs PR 2970, revision 3b518a72099d34f835e06c15f1f79b2400ae2732.
The Mertens estimates, prime block definitions and upper block combinatorics
adapt material copyrighted 2026 by Sushaan Kandukoori, licensed under Apache-2.0,
from erdos-straus-lean revision f6c99eaaca6ec7a7226a7a16bef1cd2b09e36660.
We specialize the lower bound to the Farey numerator window, with ranks varying
with the cutoff exponent and a uniform bound on the total rounding error. -/

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

open scoped Classical

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
open scoped Classical

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
open scoped Classical

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
open scoped Classical

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

/-! Mertens estimates adapted from sushaan-k/erdos-straus-lean (Apache 2.0),
    ErdosStraus/Estimates/{Chebyshev,PartialSummation,Mertens}. -/

namespace ErdosStraus.Estimates

open scoped BigOperators

/-- `∑_{p ≤ N} log p ≤ N log 4`, from the primorial bound `∏_{p ≤ N} p ≤ 4^N`
(proof of Lemma 3.1). -/
theorem primeLogSum_le_log_four_mul (N : ℕ) :
    (∑ p ∈ (Finset.Icc (1 : ℕ) N).filter (fun p => Nat.Prime p),
        Real.log (p : ℝ)) ≤
      Real.log (4 : ℝ) * (N : ℝ) := by
  classical
  let s := (Finset.range (N + 1)).filter Nat.Prime
  have hs_eq :
      (∑ p ∈ (Finset.Icc (1 : ℕ) N).filter (fun p => Nat.Prime p),
          Real.log (p : ℝ)) =
        ∑ p ∈ s, Real.log (p : ℝ) := by
    apply Finset.sum_congr
    · ext p
      by_cases hp : Nat.Prime p
      · simp [s, hp, hp.one_le]
      · simp [s, hp]
    · intro p _hp
      rfl
  have hlog_prod :
      Real.log (∏ p ∈ s, (p : ℝ)) = ∑ p ∈ s, Real.log (p : ℝ) := by
    rw [Real.log_prod]
    intro p hp
    have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2
    exact_mod_cast hpPrime.ne_zero
  have hprod_cast :
      (∏ p ∈ s, (p : ℝ)) = ((primorial N : ℕ) : ℝ) := by
    unfold primorial
    simp [s]
  have hprim : ((primorial N : ℕ) : ℝ) ≤ (4 : ℝ) ^ N := by
    exact_mod_cast primorial_le_four_pow N
  have hprod_pos : 0 < (∏ p ∈ s, (p : ℝ)) := by
    rw [hprod_cast]
    exact_mod_cast primorial_pos N
  have hlog_le :
      Real.log (∏ p ∈ s, (p : ℝ)) ≤ Real.log ((4 : ℝ) ^ N) := by
    exact Real.log_le_log hprod_pos (by simpa [hprod_cast] using hprim)
  have hlog_pow : Real.log ((4 : ℝ) ^ N) = (N : ℝ) * Real.log (4 : ℝ) := by
    rw [Real.log_pow]
  rw [hs_eq, ← hlog_prod]
  calc
    Real.log (∏ p ∈ s, (p : ℝ)) ≤ Real.log ((4 : ℝ) ^ N) := hlog_le
    _ = (N : ℝ) * Real.log (4 : ℝ) := hlog_pow
    _ = Real.log (4 : ℝ) * (N : ℝ) := by ring

end ErdosStraus.Estimates

/-! ## Primes up to `x` and the Euler product

The set of primes `p ≤ x`, the sum `∑_{p ≤ x} 1/p`, the product `∏_{p ≤ x} (1 - 1/p)`, and
the local estimate `|log(1 - 1/p) + 1/p| ≤ 2/p²`.
-/

namespace ErdosStraus.PrimeEstimates.Mertens

open Finset Real

/-- The set of primes `p ≤ x`. -/
def primesUpTo (x : ℕ) : Finset ℕ :=
  (range (x + 1)).filter Nat.Prime

@[simp]
theorem mem_primesUpTo {p x : ℕ} : p ∈ primesUpTo x ↔ p.Prime ∧ p ≤ x := by
  simp [primesUpTo, and_comm]

theorem primesUpTo_eq_empty_of_le_one {x : ℕ} (hx : x ≤ 1) : primesUpTo x = ∅ := by
  ext p
  simp only [mem_primesUpTo, Finset.notMem_empty, iff_false]
  intro hp'
  have hp2 := hp'.1.two_le
  omega

/-- The sum `∑_{p ≤ x} 1/p`. -/
noncomputable def primeReciprocalSum (x : ℕ) : ℝ :=
  (primesUpTo x).sum fun p => 1 / (p : ℝ)

/-- The Euler product `∏_{p ≤ x} (1 - 1/p)`. -/
noncomputable def primeProduct (x : ℕ) : ℝ :=
  (primesUpTo x).prod fun p => 1 - 1 / (p : ℝ)

theorem primeFactor_pos {p : ℕ} (hp : p.Prime) :
    0 < 1 - 1 / (p : ℝ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact sub_pos.mpr ((div_lt_one (zero_lt_one.trans hp1)).mpr hp1)

theorem primeProduct_pos (x : ℕ) : 0 < primeProduct x := by
  unfold primeProduct
  exact Finset.prod_pos fun p hp => primeFactor_pos (mem_primesUpTo.mp hp).1

theorem log_primeProduct (x : ℕ) :
    log (primeProduct x) =
      (primesUpTo x).sum (fun p => log (1 - 1 / (p : ℝ))) := by
  unfold primeProduct
  rw [Real.log_prod]
  intro p hp
  exact (primeFactor_pos (mem_primesUpTo.mp hp).1).ne'

theorem abs_log_one_sub_add_le {t : ℝ} (ht0 : 0 < t) (htle : t ≤ 1 / 2) :
    |log (1 - t) + t| ≤ 2 * t ^ 2 := by
  have hpos : 0 < 1 - t := by linarith
  have hne : 1 - t ≠ 0 := ne_of_gt hpos
  have hub : log (1 - t) ≤ -t := by
    have h := Real.log_le_sub_one_of_pos hpos
    linarith
  have hlb : -t - 2 * t ^ 2 ≤ log (1 - t) := by
    have hrec2 : 1 / (1 - t) ≤ 1 + 2 * t := by
      rw [div_le_iff₀ hpos]
      nlinarith
    have hmul : t / (1 - t) ≤ t * (1 + 2 * t) := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hrec2 (le_of_lt ht0)
    calc
      -t - 2 * t ^ 2 = -(t * (1 + 2 * t)) := by ring
      _ ≤ -(t / (1 - t)) := neg_le_neg hmul
      _ = 1 - (1 - t)⁻¹ := by field_simp [hne]; ring
      _ ≤ log (1 - t) := Real.one_sub_inv_le_log_of_pos hpos
  rw [abs_le]
  constructor <;> nlinarith

theorem abs_log_primeFactor_add_le {p : ℕ} (hp : p.Prime) :
    |log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)| ≤ 2 / (p : ℝ) ^ 2 := by
  have ht0 : 0 < 1 / (p : ℝ) := by
    exact div_pos one_pos (by exact_mod_cast hp.pos)
  have htle : 1 / (p : ℝ) ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (by exact_mod_cast hp.two_le)
  simpa only [div_pow, one_pow, mul_one_div] using
    abs_log_one_sub_add_le ht0 htle

end ErdosStraus.PrimeEstimates.Mertens

/-! ## Chebyshev's functions

The bounds `θ(x) ≤ x log 4`, `ψ(N) - θ(N) ≤ √N log N` and `ψ(x) ≤ (log 4 + 2) x`.
-/

namespace ErdosStraus.PrimeEstimates.Mertens

open Filter Finset Real
open scoped BigOperators ArithmeticFunction

/-- Chebyshev's function `θ(x) = ∑_{p ≤ x} log p`. -/
noncomputable def theta (x : ℝ) : ℝ := ∑ p ∈ primesUpTo ⌊x⌋₊, log p

/-- Chebyshev's function `ψ(x) = ∑_{n ≤ x} Λ(n)`. -/
noncomputable def psi (x : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n

theorem primesUpTo_eq_filter_Icc_one (N : ℕ) :
    primesUpTo N = (Icc 1 N).filter Nat.Prime := by
  ext p
  simp only [mem_primesUpTo, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hp, hpN⟩; exact ⟨⟨hp.one_le, hpN⟩, hp⟩
  · rintro ⟨⟨_, hpN⟩, hp⟩; exact ⟨hp, hpN⟩

theorem theta_floor (x : ℝ) : theta (⌊x⌋₊ : ℝ) = theta x := by
  simp only [theta, Nat.floor_natCast]

theorem psi_floor (x : ℝ) : psi (⌊x⌋₊ : ℝ) = psi x := by
  simp only [psi, Nat.floor_natCast]

/-- Grouping the prime powers `p^k ≤ N` according to the prime `p`. -/
theorem sum_vonMangoldt_mul (N : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, Λ n * f n =
      ∑ p ∈ primesUpTo N, log p * ∑ k ∈ Icc 1 (Nat.log p N), f (p ^ k) := by
  classical
  have hrestrict : ∑ n ∈ Icc 1 N, Λ n * f n =
      ∑ n ∈ (Icc 1 N).filter IsPrimePow, log (n.minFac : ℝ) * f n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    rw [ArithmeticFunction.vonMangoldt_apply]
    split_ifs <;> simp
  have hmaps : ∀ n ∈ (Icc 1 N).filter IsPrimePow, n.minFac ∈ primesUpTo N := by
    intro n hn
    obtain ⟨hnI, hpow⟩ := mem_filter.mp hn
    obtain ⟨h1n, hnN⟩ := mem_Icc.mp hnI
    exact mem_primesUpTo.mpr ⟨Nat.minFac_prime hpow.ne_one,
      (Nat.minFac_le (by omega)).trans hnN⟩
  rw [hrestrict, ← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpp, hpN⟩ := mem_primesUpTo.mp hp
  have hN0 : N ≠ 0 := by have := hpp.two_le; omega
  have hfib : ((Icc 1 N).filter IsPrimePow).filter (fun n => n.minFac = p) =
      (Icc 1 (Nat.log p N)).image (fun k => p ^ k) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨⟨_, hnN⟩, hpow⟩, hmin⟩
      obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpow
      rw [hq.pow_minFac hk.ne'] at hmin
      subst hmin
      exact ⟨k, ⟨hk, Nat.le_log_of_pow_le hq.one_lt hnN⟩, rfl⟩
    · rintro ⟨k, ⟨hk, hkN⟩, rfl⟩
      refine ⟨⟨⟨Nat.one_le_pow _ _ hpp.pos,
        (Nat.pow_le_pow_right hpp.pos hkN).trans (Nat.pow_log_le_self p hN0)⟩,
        hpp.isPrimePow.pow (by omega)⟩, hpp.pow_minFac (by omega)⟩
  have hcongr : ∀ n ∈ ((Icc 1 N).filter IsPrimePow).filter (fun n => n.minFac = p),
      log (n.minFac : ℝ) * f n = log p * f n := by
    intro n hn
    rw [(mem_filter.mp hn).2]
  rw [Finset.sum_congr rfl hcongr, hfib, Finset.sum_image, Finset.mul_sum]
  intro x _ y _ hxy
  exact Nat.pow_right_injective hpp.two_le hxy

/-- `ψ(N) = ∑_{p ≤ N} ⌊log N / log p⌋ log p`. -/
theorem psi_nat (N : ℕ) :
    psi N = ∑ p ∈ primesUpTo N, (Nat.log p N : ℝ) * log p := by
  have h := sum_vonMangoldt_mul N (fun _ => 1)
  simp only [mul_one, sum_const, Nat.card_Icc, nsmul_eq_mul] at h
  rw [psi, Nat.floor_natCast, h]
  apply Finset.sum_congr rfl
  intro p _
  rw [Nat.add_sub_cancel, mul_comm]

/-- Chebyshev's bound `θ(x) ≤ x log 4`. -/
theorem theta_le {x : ℝ} (hx : 0 ≤ x) : theta x ≤ log 4 * x := by
  rw [← theta_floor]
  have h := Estimates.primeLogSum_le_log_four_mul ⌊x⌋₊
  rw [← primesUpTo_eq_filter_Icc_one] at h
  simp only [theta, Nat.floor_natCast]
  exact h.trans (mul_le_mul_of_nonneg_left (Nat.floor_le hx) (log_pos (by norm_num)).le)

/-- The prime powers `p^k ≤ N` with `k ≥ 2` contribute `ψ(N) - θ(N) ≤ √N log N`. -/
theorem psi_sub_theta_nat_le (N : ℕ) :
    psi N - theta N ≤ Real.sqrt N * log N := by
  classical
  rw [psi_nat, theta, Nat.floor_natCast, ← sum_sub_distrib]
  have hlogN : 0 ≤ log (N : ℝ) := Real.log_natCast_nonneg N
  have hterm : ∀ p ∈ primesUpTo N, (Nat.log p N : ℝ) * log p - log p ≤
      if p ≤ Nat.sqrt N then log (N : ℝ) else 0 := by
    intro p hp
    obtain ⟨hpp, hpN⟩ := mem_primesUpTo.mp hp
    have hN0 : N ≠ 0 := by have := hpp.two_le; omega
    have hlogp : 0 ≤ log (p : ℝ) := Real.log_natCast_nonneg p
    have hpow : (Nat.log p N : ℝ) * log p ≤ log N := by
      rw [← Real.log_pow]
      exact log_le_log (by have := hpp.pos; positivity)
        (by exact_mod_cast Nat.pow_log_le_self p hN0)
    split_ifs with hsq
    · linarith
    · have hlt : N < p * p := by
        by_contra h
        exact hsq (Nat.le_sqrt.mpr (not_lt.mp h))
      have hL : Nat.log p N = 1 := Nat.log_eq_one_iff.mpr ⟨hlt, hpp.one_lt, hpN⟩
      simp [hL]
  have hcard : (((primesUpTo N).filter (fun p => p ≤ Nat.sqrt N)).card : ℝ) ≤
      Nat.sqrt N := by
    have hsub : (primesUpTo N).filter (fun p => p ≤ Nat.sqrt N) ⊆ Icc 1 (Nat.sqrt N) := by
      intro p hp
      obtain ⟨hp', hps⟩ := mem_filter.mp hp
      exact mem_Icc.mpr ⟨(mem_primesUpTo.mp hp').1.one_le, hps⟩
    have h := card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at h
    exact_mod_cast h
  calc
    _ ≤ ∑ p ∈ primesUpTo N, (if p ≤ Nat.sqrt N then log (N : ℝ) else 0) :=
      Finset.sum_le_sum hterm
    _ = (((primesUpTo N).filter (fun p => p ≤ Nat.sqrt N)).card : ℝ) * log N := by
      rw [← Finset.sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ (Nat.sqrt N : ℝ) * log N := mul_le_mul_of_nonneg_right hcard hlogN
    _ ≤ Real.sqrt N * log N :=
      mul_le_mul_of_nonneg_right Real.nat_sqrt_le_real_sqrt hlogN

theorem sqrt_mul_log_le {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x * log x ≤ 2 * x := by
  have hlog : log x ≤ 2 * Real.sqrt x := by
    have h := Real.log_le_rpow_div hx (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    linarith
  rcases le_or_gt (log x) 0 with hl | hl
  · nlinarith [Real.sqrt_nonneg x]
  · calc
      Real.sqrt x * log x ≤ Real.sqrt x * (2 * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg x)
      _ = 2 * x := by rw [← mul_assoc, mul_comm _ 2, mul_assoc, Real.mul_self_sqrt hx]

/-- Chebyshev's bound `ψ(x) ≤ (log 4 + 2) x`. -/
theorem psi_le {x : ℝ} (hx : 0 ≤ x) : psi x ≤ (log 4 + 2) * x := by
  rw [← psi_floor]
  have hle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have h0 : (0 : ℝ) ≤ ⌊x⌋₊ := Nat.cast_nonneg _
  have h1 := psi_sub_theta_nat_le ⌊x⌋₊
  have h2 := theta_le h0
  have h3 := sqrt_mul_log_le h0
  have h4 : (log 4 + 2) * (⌊x⌋₊ : ℝ) ≤ (log 4 + 2) * x :=
    mul_le_mul_of_nonneg_left hle (by have := log_pos (by norm_num : (1 : ℝ) < 4); linarith)
  linarith

end ErdosStraus.PrimeEstimates.Mertens
namespace ErdosStraus.PrimeEstimates

open scoped BigOperators
open Finset
theorem sum_Ico_weight_differences (u : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    (∑ k ∈ Ico m n, (u k - u (k + 1))) = u m - u n := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih => rw [Finset.sum_Ico_succ_top hmn, ih]; ring

theorem sum_Ioc_eq_prefix_sub (c : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    (∑ j ∈ Ioc m n, c j) =
      (∑ j ∈ Icc 0 n, c j) - (∑ j ∈ Icc 0 m, c j) := by
  have hsplit : (∑ j ∈ Icc 0 n, c j) =
      (∑ j ∈ Icc 0 m, c j) + (∑ j ∈ Ioc m n, c j) := by
    rw [← Finset.add_sum_Ioc_eq_sum_Icc (f := c) (Nat.zero_le n),
      ← Finset.add_sum_Ioc_eq_sum_Icc (f := c) (Nat.zero_le m),
      ← Finset.sum_Ioc_consecutive c (Nat.zero_le m) hmn]
    ring
  linarith


end ErdosStraus.PrimeEstimates

namespace ErdosStraus.PrimeEstimates.Mertens

open Filter MeasureTheory Real Set
open scoped Topology

theorem hasDerivAt_neg_inv_log {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t : ℝ => -(log t)⁻¹) (x⁻¹ / (log x) ^ 2) x := by
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hl0 : log x ≠ 0 := (log_pos hx).ne'
  refine ((Real.hasDerivAt_log hx0).inv hl0).neg.congr_deriv ?_
  simp [div_eq_mul_inv]

theorem inv_log_tendsto_zero :
    Tendsto (fun t : ℝ => -(log t)⁻¹) atTop (𝓝 0) := by
  simpa using Real.tendsto_log_atTop.inv_tendsto_atTop.neg

theorem integrableOn_inv_div_log_sq_Ioi {x : ℝ} (hx : 1 < x) :
    IntegrableOn (fun t : ℝ => t⁻¹ / (log t) ^ 2) (Ioi x) := by
  apply integrableOn_Ioi_deriv_of_nonneg' (g := fun t : ℝ => -(log t)⁻¹)
    (l := 0) (fun t ht => hasDerivAt_neg_inv_log (hx.trans_le ht))
    (fun t ht => div_nonneg (inv_nonneg.mpr (zero_lt_one.trans (hx.trans ht)).le)
      (sq_nonneg _)) inv_log_tendsto_zero

theorem integral_inv_div_log_sq_Ioi {x : ℝ} (hx : 1 < x) :
    (∫ t in Ioi x, t⁻¹ / (log t) ^ 2) = 1 / log x := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (g := fun t : ℝ => -(log t)⁻¹)
    (l := 0) (fun t ht => hasDerivAt_neg_inv_log (hx.trans_le ht))
    (fun t ht => div_nonneg (inv_nonneg.mpr (zero_lt_one.trans (hx.trans ht)).le)
      (sq_nonneg _)) inv_log_tendsto_zero
  simpa using h

theorem integral_interval_sub_Ioi {f : ℝ → ℝ} {a x : ℝ}
    (hf : IntegrableOn f (Ioi a)) (hx : a ≤ x) :
    (∫ t in a..x, f t) - (∫ t in Ioi a, f t) = -(∫ t in Ioi x, f t) := by
  have hdisj : Disjoint (Ioc a x) (Ioi x) := by
    apply Set.disjoint_left.mpr
    intro t ht ht'
    exact (not_lt_of_ge ht.2) ht'
  have h := setIntegral_union hdisj measurableSet_Ioi
    (hf.mono_set Ioc_subset_Ioi_self) (hf.mono_set (Ioi_subset_Ioi hx))
  rw [Ioc_union_Ioi_eq_Ioi hx] at h
  rw [intervalIntegral.integral_of_le hx]
  linarith

end ErdosStraus.PrimeEstimates.Mertens

/-! ## Legendre's identity and Mertens' first theorem at integers

Counting prime factors of `n!` gives `log n! = ∑_{d ≤ n} Λ(d) ⌊n/d⌋`, hence
`0 ≤ n ∑_{d ≤ n} Λ(d)/d - log n! ≤ ψ(n)`. Together with
`log n! = n log n + O(n)`, `ψ(n) ≪ n` and the bounded contribution of proper
prime powers this gives `∑_{p ≤ n} log p / p = log n + O(1)`.
-/

namespace ErdosStraus.PrimeEstimates.Mertens

open Finset Real
open scoped BigOperators ArithmeticFunction Nat

/-- `log n! = ∑_{m ≤ n} log m`. -/
theorem log_factorial_eq_sum_log (n : ℕ) :
    log (n ! : ℝ) = ∑ m ∈ Icc 1 n, log (m : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity), ih,
      Finset.sum_Icc_succ_top (by omega)]
    ring

/-- Legendre's identity `log n! = ∑_{d ≤ n} Λ(d) ⌊n/d⌋`. -/
theorem log_factorial_eq (n : ℕ) :
    log (n ! : ℝ) = ∑ d ∈ Icc 1 n, Λ d * ((n / d : ℕ) : ℝ) := by
  rw [log_factorial_eq_sum_log]
  have hdiv : ∀ m ∈ Icc 1 n, log (m : ℝ) = ∑ d ∈ m.divisors, Λ d := fun m _ =>
    ArithmeticFunction.vonMangoldt_sum.symm
  rw [Finset.sum_congr rfl hdiv,
    Finset.sum_comm' (t' := Icc 1 n) (s' := fun d => (Icc 1 n).filter (fun m => d ∣ m))]
  · apply Finset.sum_congr rfl
    intro d _
    have hIcc : Icc 1 n = Ioc 0 n := Finset.Icc_add_one_left_eq_Ioc 0 n
    rw [sum_const, nsmul_eq_mul, hIcc, Nat.Ioc_filter_dvd_card_eq_div, mul_comm]
  · intro m d
    simp only [mem_Icc, Nat.mem_divisors, mem_filter]
    constructor
    · rintro ⟨⟨h1, hm⟩, hdm, -⟩
      exact ⟨⟨⟨h1, hm⟩, hdm⟩, Nat.pos_of_dvd_of_pos hdm h1, (Nat.le_of_dvd h1 hdm).trans hm⟩
    · rintro ⟨⟨⟨h1, hm⟩, hdm⟩, -, -⟩
      exact ⟨⟨h1, hm⟩, hdm, by omega⟩

/-- `⌊n/d⌋ ≤ n/d ≤ ⌊n/d⌋ + 1`. -/
theorem natDiv_le_div_le (n d : ℕ) (hd : 0 < d) :
    ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d ∧ (n : ℝ) / d ≤ ((n / d : ℕ) : ℝ) + 1 := by
  refine ⟨Nat.cast_div_le, ?_⟩
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_le_iff₀ hdr]
  have h3 : (n : ℝ) = d * (n / d : ℕ) + (n % d : ℕ) := by exact_mod_cast (Nat.div_add_mod n d).symm
  have h4 : ((n % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt n hd).le
  nlinarith

/-- `0 ≤ n ∑_{d ≤ n} Λ(d)/d - log n! ≤ ψ(n)`. -/
theorem legendre_bounds (n : ℕ) :
    0 ≤ n * ∑ d ∈ Icc 1 n, Λ d / d - log (n ! : ℝ) ∧
      n * ∑ d ∈ Icc 1 n, Λ d / d - log (n ! : ℝ) ≤ psi n := by
  have heq : (n : ℝ) * ∑ d ∈ Icc 1 n, Λ d / d - log (n ! : ℝ) =
      ∑ d ∈ Icc 1 n, Λ d * ((n : ℝ) / d - ((n / d : ℕ) : ℝ)) := by
    rw [log_factorial_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [heq]
  constructor
  · apply Finset.sum_nonneg
    intro d hd
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (sub_nonneg.mpr (natDiv_le_div_le n d (mem_Icc.mp hd).1).1)
  · rw [psi, Nat.floor_natCast]
    apply Finset.sum_le_sum
    intro d hd
    have h := natDiv_le_div_le n d (mem_Icc.mp hd).1
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (by linarith)

/-- `log n! = n log n + O(n)`. -/
theorem log_factorial_bounds (n : ℕ) :
    n * log n - n ≤ log (n ! : ℝ) ∧ log (n ! : ℝ) ≤ n * log n := by
  have hfpos : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  constructor
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have h := Real.pow_div_factorial_le_exp (n : ℝ) hnpos.le n
      have hl := Real.log_le_log (by positivity) h
      rw [Real.log_exp, Real.log_div (by positivity) hfpos.ne', Real.log_pow] at hl
      linarith
  · rw [← Real.log_pow]
    exact Real.log_le_log hfpos (by exact_mod_cast Nat.factorial_le_pow n)

/-- The proper prime powers `p ^ k ≤ N`, `k ≥ 2`, weighted by `log p / p ^ k`. -/
noncomputable def primePowerTail (N : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo N, ∑ k ∈ Icc 2 (Nat.log p N), log p / (p : ℝ) ^ k

/-- `∑_{d ≤ N} Λ(d)/d` splits into the primes and the proper prime powers. -/
theorem sum_vonMangoldt_div_eq (N : ℕ) :
    ∑ d ∈ Icc 1 N, Λ d / d = (∑ p ∈ primesUpTo N, log p / p) + primePowerTail N := by
  have h := sum_vonMangoldt_mul N (fun d => 1 / (d : ℝ))
  simp only [mul_one_div] at h
  rw [h, primePowerTail, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpp, hpN⟩ := mem_primesUpTo.mp hp
  have hL : 1 ≤ Nat.log p N := Nat.log_pos hpp.one_lt hpN
  rw [← Finset.insert_Icc_add_one_left_eq_Icc hL, Finset.sum_insert (by simp), mul_add,
    Finset.mul_sum]
  push_cast
  simp only [pow_one, mul_one_div]

/-- `log n / (n (n - 1)) ≥ 0`. -/
theorem primePowerWeight_nonneg (n : ℕ) :
    0 ≤ log (n : ℝ) / (n * ((n : ℝ) - 1)) := by
  apply div_nonneg (Real.log_natCast_nonneg n)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith

/-- `log n / (n (n - 1)) ≤ 4 n^{-3/2}`. -/
theorem primePowerWeight_le (n : ℕ) :
    log (n : ℝ) / (n * ((n : ℝ) - 1)) ≤ 4 * (1 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hpos : (0 : ℝ) < n := by linarith
    have hlog := Real.log_le_rpow_div hpos.le (by norm_num : (0 : ℝ) < 1 / 2)
    have hnn : (n : ℝ) * n = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_add hpos]; norm_num; ring
    have h32 : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hpos _
    have h12 : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hpos _
    rw [div_le_iff₀ (by nlinarith)]
    calc
      log (n : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) := hlog
      _ = 4 * (1 / (n : ℝ) ^ (3 / 2 : ℝ)) * (n * n / 2) := by
        rw [hnn]; field_simp; ring
      _ ≤ 4 * (1 / (n : ℝ) ^ (3 / 2 : ℝ)) * (n * ((n : ℝ) - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith

/-- `∑_{n ≥ 2} log n / (n (n - 1)) < ∞`. -/
theorem summable_primePowerWeight :
    Summable fun n : ℕ => log (n : ℝ) / (n * ((n : ℝ) - 1)) :=
  Summable.of_nonneg_of_le primePowerWeight_nonneg primePowerWeight_le
    ((Real.summable_one_div_nat_rpow.mpr (by norm_num)).mul_left 4)

/-- The proper prime powers contribute a bounded amount:
`∑_p ∑_{j ≥ 2} log p / p ^ j ≤ ∑_{n ≥ 2} log n / (n (n - 1))`. -/
theorem primePowerTail_bounds (N : ℕ) :
    0 ≤ primePowerTail N ∧
      primePowerTail N ≤ ∑' n : ℕ, log (n : ℝ) / (n * ((n : ℝ) - 1)) := by
  constructor
  · apply Finset.sum_nonneg
    intro p _
    apply Finset.sum_nonneg
    intro k _
    exact div_nonneg (Real.log_natCast_nonneg p) (by positivity)
  · calc
      primePowerTail N ≤ ∑ p ∈ primesUpTo N, log (p : ℝ) / (p * ((p : ℝ) - 1)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpp := (mem_primesUpTo.mp hp).1
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
        have hlogp : 0 ≤ log (p : ℝ) := Real.log_natCast_nonneg p
        have hset : Icc 2 (Nat.log p N) = Ico 2 (Nat.log p N + 1) := by
          ext k; simp only [mem_Icc, mem_Ico]; omega
        have hgeom : ∑ k ∈ Icc 2 (Nat.log p N), (1 / (p : ℝ)) ^ k ≤
            (1 / (p : ℝ)) ^ 2 / (1 - 1 / p) := by
          rw [hset]
          have hx : (0 : ℝ) ≤ 1 / p := by positivity
          have h'x : 1 / (p : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
          rcases le_or_gt 2 (Nat.log p N + 1) with hmn | hmn
          · rw [geom_sum_Ico' h'x.ne hmn]
            apply div_le_div₀ (pow_nonneg hx _) _ (sub_pos.2 h'x) le_rfl
            exact sub_le_self _ (pow_nonneg hx _)
          · rw [Ico_eq_empty (by omega), sum_empty]
            exact div_nonneg (pow_nonneg hx _) (sub_nonneg.2 h'x.le)
        have hval : (1 / (p : ℝ)) ^ 2 / (1 - 1 / p) = 1 / (p * ((p : ℝ) - 1)) := by
          have hp0 : (p : ℝ) ≠ 0 := by linarith
          have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
          field_simp
        calc
          ∑ k ∈ Icc 2 (Nat.log p N), log (p : ℝ) / (p : ℝ) ^ k =
              log (p : ℝ) * ∑ k ∈ Icc 2 (Nat.log p N), (1 / (p : ℝ)) ^ k := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            rw [one_div_pow, mul_one_div]
          _ ≤ log (p : ℝ) * (1 / (p * ((p : ℝ) - 1))) :=
            mul_le_mul_of_nonneg_left (hgeom.trans hval.le) hlogp
          _ = log (p : ℝ) / (p * ((p : ℝ) - 1)) := mul_one_div _ _
      _ ≤ ∑' n : ℕ, log (n : ℝ) / (n * ((n : ℝ) - 1)) :=
        summable_primePowerWeight.sum_le_tsum _ (fun n _ => primePowerWeight_nonneg n)

/-- Mertens' first theorem at integers: `∑_{p ≤ n} log p / p = log n + O(1)`. -/
theorem mertensFirst_nat :
    ∃ C > 0, ∀ n : ℕ, |(∑ p ∈ primesUpTo n, log p / p) - log n| ≤ C := by
  set D := ∑' n : ℕ, log (n : ℝ) / (n * ((n : ℝ) - 1))
  have hD0 : 0 ≤ D := tsum_nonneg primePowerWeight_nonneg
  have hlog4 : 0 < log (4 : ℝ) := log_pos (by norm_num)
  refine ⟨log 4 + 3 + D, by linarith, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [primesUpTo_eq_empty_of_le_one (by norm_num)]
    simp only [sum_empty, Nat.cast_zero, log_zero, sub_zero, abs_zero]
    linarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hL0, hL1⟩ := legendre_bounds n
  obtain ⟨hF0, hF1⟩ := log_factorial_bounds n
  have hpsi := psi_le hnr.le
  have hsplit := sum_vonMangoldt_div_eq n
  obtain ⟨hT0, hT1⟩ := primePowerTail_bounds n
  set S := ∑ d ∈ Icc 1 n, Λ d / d
  set B := ∑ p ∈ primesUpTo n, log (p : ℝ) / p
  have hS_lo : log n - 1 ≤ S := by
    have h : (n : ℝ) * (log n - 1) ≤ n * S := by nlinarith
    exact le_of_mul_le_mul_left h hnr
  have hS_hi : S ≤ log n + (log 4 + 2) := by
    have h : (n : ℝ) * S ≤ n * (log n + (log 4 + 2)) := by nlinarith
    exact le_of_mul_le_mul_left h hnr
  rw [abs_le]
  constructor <;> linarith

end ErdosStraus.PrimeEstimates.Mertens

/-! ## Mertens' first theorem for real `x`

`B₁(x) = ∑_{p ≤ x} log p / p = log x + O(1)` for all real `x ≥ 2`, deduced from
the integer case, and the bounded remainder `R(x) = B₁(x) - log x`.
-/

namespace ErdosStraus.PrimeEstimates.Mertens

open Finset Real
open scoped BigOperators

/-- Comparison of `log x` with `log ⌊x⌋` for `x ≥ 2`. -/
theorem floor_log_bounds {x : ℝ} (hx : 2 ≤ x) :
    0 < log (⌊x⌋₊ : ℝ) ∧ log (⌊x⌋₊ : ℝ) ≤ log x ∧
      log x ≤ 2 * log (⌊x⌋₊ : ℝ) ∧ log x - log (⌊x⌋₊ : ℝ) ≤ log 2 := by
  let n := ⌊x⌋₊
  have hn : 2 ≤ n := Nat.le_floor hx
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn2 : (2 : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hnx : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxn : x ≤ 2 * (n : ℝ) := by have hh := Nat.lt_floor_add_one x; dsimp [n] at *; linarith
  have hln : 0 < log (n : ℝ) := log_pos (by linarith)
  have hlog2 : log (2 : ℝ) ≤ log n := log_le_log (by norm_num) hn2
  have hup : log x ≤ log 2 + log n := by
    have hh := log_le_log (by linarith : 0 < x) hxn
    rwa [log_mul (by norm_num) hnp.ne'] at hh
  exact ⟨hln, log_le_log hnp hnx, by linarith, by linarith⟩

/-- Mertens' first theorem: `∑_{p ≤ x} log p / p = log x + O(1)` for real `x ≥ 2`. -/
theorem mertensFirst :
    ∃ C > 0, ∀ x : ℝ, 2 ≤ x →
      |(∑ p ∈ primesUpTo ⌊x⌋₊, log p / p) - log x| ≤ C := by
  obtain ⟨C, hC, h⟩ := mertensFirst_nat
  refine ⟨C + log 2 + 1, by positivity, ?_⟩
  intro x hx
  obtain ⟨hlp, hle, h2, hgap⟩ := floor_log_bounds hx
  have heq : (∑ p ∈ primesUpTo ⌊x⌋₊, log p / p) - log x =
      ((∑ p ∈ primesUpTo ⌊x⌋₊, log p / p) - log (⌊x⌋₊ : ℝ)) -
        (log x - log (⌊x⌋₊ : ℝ)) := by ring
  rw [heq]
  exact (abs_sub _ _).trans (by rw [abs_of_nonneg (sub_nonneg.mpr hle)]; linarith [h ⌊x⌋₊])

/-- `B₁(x) = ∑_{p ≤ x} log p / p`. -/
noncomputable def primeLogReciprocal (x : ℝ) : ℝ := ∑ p ∈ primesUpTo ⌊x⌋₊, log p / p

/-- The remainder `R(x) = B₁(x) - log x` in Mertens' first theorem. -/
noncomputable def mertensRemainder (x : ℝ) : ℝ := primeLogReciprocal x - log x

/-- `R(x) = B₁(x) - log x` is bounded on `[2, ∞)`. -/
theorem mertensRemainder_bound :
    ∃ C > 0, ∀ x : ℝ, 2 ≤ x → |mertensRemainder x| ≤ C :=
  mertensFirst

/-- `B₁(x)` as a sum of prime-supported coefficients up to the given bound. -/
theorem primeLogReciprocal_eq_sum_Icc (x : ℝ) :
    primeLogReciprocal x =
      ∑ n ∈ Icc 0 ⌊x⌋₊, if n.Prime then log (n : ℝ) / n else 0 := by
  rw [primeLogReciprocal, primesUpTo, sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext n
  simp only [mem_range, mem_Icc]
  omega

theorem measurable_primeLogReciprocal : Measurable primeLogReciprocal :=
  (measurable_of_countable
    (fun N : ℕ => ∑ p ∈ primesUpTo N, log (p : ℝ) / p)).comp Nat.measurable_floor

theorem measurable_mertensRemainder : Measurable mertensRemainder :=
  measurable_primeLogReciprocal.sub measurable_log

end ErdosStraus.PrimeEstimates.Mertens

/-! ## Mertens' second theorem

Abel summation against `B₁` gives
`∑_{p ≤ x} 1/p = B₁(x)/log x + ∫_2^x B₁(t)/(t (log t)²) dt`.
Writing `B₁(t) = log t + R(t)` with `R` bounded, the error integral converges
with tail `O(1/log x)`, so `∑_{p ≤ x} 1/p = log log x + B + O(1/log x)`.
-/

namespace ErdosStraus.PrimeEstimates.Mertens

open Filter Finset MeasureTheory Real
open scoped BigOperators

/-- A function dominated by `C / (t (log t)²)` has tail integral at most `C / log x`. -/
theorem norm_integral_Ioi_le_div_log {f : ℝ → ℝ} {x C : ℝ} (hx : 1 < x)
    (hbound : ∀ t ∈ Set.Ioi x, ‖f t‖ ≤ C * (t⁻¹ / (log t) ^ 2)) :
    ‖∫ t in Set.Ioi x, f t‖ ≤ C / log x := by
  have hk : IntegrableOn (fun t : ℝ => t⁻¹ / (log t) ^ 2) (Set.Ioi x) volume :=
    integrableOn_inv_div_log_sq_Ioi hx
  have hCk : IntegrableOn (fun t : ℝ => C * (t⁻¹ / (log t) ^ 2)) (Set.Ioi x) volume :=
    hk.const_mul C
  calc
    ‖∫ t in Set.Ioi x, f t‖ ≤ ∫ t in Set.Ioi x, C * (t⁻¹ / (log t) ^ 2) := by
      apply MeasureTheory.norm_integral_le_of_norm_le hCk
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hbound t ht
    _ = C * ∫ t in Set.Ioi x, t⁻¹ / (log t) ^ 2 := by rw [integral_const_mul]
    _ = C / log x := by rw [integral_inv_div_log_sq_Ioi hx]; ring

/-- `(1 / log t)' = -1 / (t (log t)²)`. -/
theorem hasDerivAt_inv_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun u : ℝ => (log u)⁻¹) (-(t⁻¹ / (log t) ^ 2)) t := by
  simpa only [Pi.neg_def, neg_neg] using (hasDerivAt_neg_inv_log ht).neg

/-- Abel summation against `B₁`:
`∑_{p ≤ x} 1/p = B₁(x)/log x + ∫_2^x B₁(t)/(t (log t)²) dt`. -/
theorem primeReciprocalSum_abel {x : ℝ} (hx : 2 ≤ x) :
    primeReciprocalSum ⌊x⌋₊ =
      primeLogReciprocal x / log x +
        ∫ t in (2 : ℝ)..x, primeLogReciprocal t / (t * (log t) ^ 2) := by
  let c : ℕ → ℝ := fun n => if n.Prime then log (n : ℝ) / n else 0
  let f : ℝ → ℝ := fun u => (log u)⁻¹
  have hderiv : ∀ t : ℝ, 1 < t → deriv f t = -(t⁻¹ / (log t) ^ 2) :=
    fun t ht => (hasDerivAt_inv_log ht).deriv
  have hf : ∀ t ∈ Set.Icc 2 x, DifferentiableAt ℝ f t :=
    fun t ht => (hasDerivAt_inv_log (by linarith [ht.1])).differentiableAt
  have hfi : IntegrableOn (deriv f) (Set.Icc 2 x) := by
    have hc : ContinuousOn (fun t : ℝ => -(t⁻¹ / (log t) ^ 2)) (Set.Icc 2 x) := by
      have hlog : ContinuousOn log (Set.Icc 2 x) := fun t ht =>
        (Real.continuousAt_log (by linarith [ht.1])).continuousWithinAt
      refine (((continuousOn_id' _).inv₀ fun t ht => ?_).div (hlog.pow 2) fun t ht => ?_).neg
      · exact (show (0 : ℝ) < t by linarith [ht.1]).ne'
      · exact pow_ne_zero 2 (log_pos (by linarith [ht.1])).ne'
    exact hc.integrableOn_Icc.congr_fun
      (fun t ht => (hderiv t (by linarith [ht.1])).symm) measurableSet_Icc
  have h := sum_mul_eq_sub_sub_integral_mul c (by norm_num : (0 : ℝ) ≤ 2) hx hf hfi
  have hfloor : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
  simp only [Nat.floor_ofNat] at h
  rw [sum_Ioc_eq_prefix_sub (fun n => f n * c n) hfloor] at h
  have hinit : (∑ n ∈ Icc (0 : ℕ) 2, f n * c n) = f 2 * ∑ n ∈ Icc (0 : ℕ) 2, c n := by
    norm_num [c, Finset.sum_Icc_succ_top]
  have hB : ∀ t : ℝ, (∑ n ∈ Icc 0 ⌊t⌋₊, c n) = primeLogReciprocal t :=
    fun t => (primeLogReciprocal_eq_sum_Icc t).symm
  have hsum : (∑ n ∈ Icc 0 ⌊x⌋₊, f n * c n) = primeReciprocalSum ⌊x⌋₊ := by
    unfold primeReciprocalSum primesUpTo
    have hset : range (⌊x⌋₊ + 1) = Icc 0 ⌊x⌋₊ := by
      ext n
      simp only [mem_range, mem_Icc]
      omega
    rw [hset, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hp : n.Prime
    · have hl : log (n : ℝ) ≠ 0 := (log_pos (by exact_mod_cast hp.one_lt)).ne'
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      simp only [c, f, hp, ite_true]
      field_simp
    · simp [c, hp]
  rw [hinit, hsum] at h
  simp_rw [hB] at h
  rw [← intervalIntegral.integral_of_le hx] at h
  have hint : -(∫ t in (2 : ℝ)..x, deriv f t * primeLogReciprocal t) =
      ∫ t in (2 : ℝ)..x, primeLogReciprocal t / (t * (log t) ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht1 : 1 < t := by linarith [ht.1]
    have ht0 : t ≠ 0 := by linarith
    have hl0 : log t ≠ 0 := (log_pos ht1).ne'
    simp only [hderiv t ht1]
    field_simp
  have hfx : f x * primeLogReciprocal x = primeLogReciprocal x / log x := by
    simp only [f]; ring
  linarith

/-- The integrand `R(t) / (t (log t)²)` of the remainder in Mertens' second theorem. -/
noncomputable def mertensKernel (t : ℝ) : ℝ := mertensRemainder t * (t⁻¹ / (log t) ^ 2)

theorem measurable_mertensKernel : Measurable mertensKernel :=
  measurable_mertensRemainder.mul (measurable_inv.div (measurable_log.pow_const 2))

/-- `|R(t) / (t (log t)²)| ≤ C / (t (log t)²)` whenever `|R(t)| ≤ C`. -/
theorem norm_mertensKernel_le {C t : ℝ} (ht : 0 ≤ t) (hR : |mertensRemainder t| ≤ C) :
    ‖mertensKernel t‖ ≤ C * (t⁻¹ / (log t) ^ 2) := by
  have hpos : 0 ≤ t⁻¹ / (log t) ^ 2 := by positivity
  rw [Real.norm_eq_abs, mertensKernel, abs_mul, abs_of_nonneg hpos]
  exact mul_le_mul_of_nonneg_right hR hpos

/-- The error integral `∫_2^∞ R(t) / (t (log t)²) dt` converges. -/
theorem integrableOn_mertensKernel : IntegrableOn mertensKernel (Set.Ioi 2) := by
  obtain ⟨C, _, hR⟩ := mertensRemainder_bound
  have hg : IntegrableOn (fun t : ℝ => C * (t⁻¹ / (log t) ^ 2)) (Set.Ioi 2) :=
    (integrableOn_inv_div_log_sq_Ioi (by norm_num)).const_mul C
  refine hg.mono' measurable_mertensKernel.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht2 : (2 : ℝ) ≤ t := le_of_lt ht
  exact norm_mertensKernel_le (by linarith) (hR t ht2)

/-- The constant `B` in `∑_{p ≤ x} 1/p = log log x + B + O(1/log x)`. -/
noncomputable def mertensSecondConstant : ℝ :=
  1 - log (log 2) + ∫ t in Set.Ioi (2 : ℝ), mertensKernel t

/-- The remainder in Mertens' second theorem:
`∑_{p ≤ x} 1/p - log log x - B = R(x)/log x - ∫_x^∞ R(t)/(t (log t)²) dt`. -/
theorem mertensSecond_error_eq {x : ℝ} (hx : 2 ≤ x) :
    primeReciprocalSum ⌊x⌋₊ - (log (log x) + mertensSecondConstant) =
      mertensRemainder x / log x - ∫ t in Set.Ioi x, mertensKernel t := by
  have hlx : 0 < log x := log_pos (by linarith)
  have hlog : ContinuousOn log (Set.Icc 2 x) := fun t ht =>
    (Real.continuousAt_log (by linarith [ht.1])).continuousWithinAt
  have hK : IntervalIntegrable mertensKernel volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mpr
      (integrableOn_mertensKernel.mono_set Set.Ioc_subset_Ioi_self)
  have hL : IntervalIntegrable (fun t : ℝ => t⁻¹ / log t) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    refine ((continuousOn_id' _).inv₀ fun t ht => ?_).div hlog fun t ht => ?_
    · exact (show (0 : ℝ) < t by linarith [ht.1]).ne'
    · exact (log_pos (by linarith [ht.1])).ne'
  have hsplit : (∫ t in (2 : ℝ)..x, primeLogReciprocal t / (t * (log t) ^ 2)) =
      (∫ t in (2 : ℝ)..x, t⁻¹ / log t) + ∫ t in (2 : ℝ)..x, mertensKernel t := by
    rw [← intervalIntegral.integral_add hL hK]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl0 : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
    simp only [mertensKernel, mertensRemainder]
    field_simp
    ring
  have hloglog : (∫ t in (2 : ℝ)..x, t⁻¹ / log t) = log (log x) - log (log 2) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hL
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl0 : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
    exact (Real.hasDerivAt_log ht0).log hl0
  have htail := integral_interval_sub_Ioi integrableOn_mertensKernel hx
  have hBx : primeLogReciprocal x / log x = 1 + mertensRemainder x / log x := by
    unfold mertensRemainder
    field_simp
    ring
  rw [primeReciprocalSum_abel hx, hsplit, hloglog, hBx]
  unfold mertensSecondConstant
  linarith

/-- Mertens' second theorem: `∑_{p ≤ x} 1/p = log log x + B + O(1/log x)`. -/
theorem mertensSecond :
    ∃ C > 0, ∀ x : ℝ, 2 ≤ x →
      |primeReciprocalSum ⌊x⌋₊ - (log (log x) + mertensSecondConstant)| ≤ C / log x := by
  obtain ⟨C, hC, hR⟩ := mertensRemainder_bound
  refine ⟨2 * C, by positivity, fun x hx => ?_⟩
  have hlx : 0 < log x := log_pos (by linarith)
  rw [mertensSecond_error_eq hx]
  have h1 : |mertensRemainder x / log x| ≤ C / log x := by
    rw [abs_div, abs_of_pos hlx]
    exact div_le_div_of_nonneg_right (hR x hx) hlx.le
  have h2 : ‖∫ t in Set.Ioi x, mertensKernel t‖ ≤ C / log x :=
    norm_integral_Ioi_le_div_log (by linarith) fun t ht =>
      norm_mertensKernel_le (by linarith [ht.out]) (hR t (hx.trans ht.out.le))
  rw [Real.norm_eq_abs] at h2
  calc
    _ ≤ |mertensRemainder x / log x| + |∫ t in Set.Ioi x, mertensKernel t| := abs_sub _ _
    _ ≤ C / log x + C / log x := add_le_add h1 h2
    _ = 2 * C / log x := by ring

/-- Natural-number form of Mertens' second theorem. -/
theorem mertensSecond_nat :
    ∃ C > 0, ∀ n : ℕ, 2 ≤ n →
      |primeReciprocalSum n - (log (log n) + mertensSecondConstant)| ≤
        C / log n := by
  obtain ⟨C, hC, h⟩ := mertensSecond
  exact ⟨C, hC, fun n hn => by simpa [Nat.floor_natCast] using h n (by exact_mod_cast hn)⟩

end ErdosStraus.PrimeEstimates.Mertens

namespace ErdosStraus.PrimeEstimates

open Finset
open scoped BigOperators

/-- `∑_{k ≤ K} 1/k² ≤ 2`, by telescoping against `2(1/k - 1/(k+1))`. -/
theorem sum_reciprocal_sq_le_two (K : ℕ) :
    (∑ k ∈ Icc 1 K, (1 : ℝ) / (k : ℝ) ^ 2) ≤ 2 := by
  have hdom : (∑ k ∈ Icc 1 K, (1 : ℝ) / (k : ℝ) ^ 2) ≤
      ∑ k ∈ Icc 1 K, 2 * (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
    have hnextpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    calc
      (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 / ((k : ℝ) * ((k : ℝ) + 1)) := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hkpos) (mul_pos hkpos hnextpos)).mpr
        nlinarith
      _ = 2 * (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) := by
        field_simp
        ring
  have hset : Icc 1 K = Ico 1 (K + 1) := by ext k; simp only [mem_Icc, mem_Ico]; omega
  have htel : (∑ k ∈ Icc 1 K, 2 * (1 / (k : ℝ) - 1 / ((k : ℝ) + 1))) =
      2 * (1 - 1 / ((K + 1 : ℕ) : ℝ)) := by
    rw [hset, ← Finset.mul_sum]
    have hh := sum_Ico_weight_differences (fun k : ℕ => (1 : ℝ) / k)
      (m := 1) (n := K + 1) (by omega)
    simpa only [Nat.cast_add, Nat.cast_one, div_one] using
      congrArg (fun y : ℝ => 2 * y) hh
  rw [htel] at hdom
  have hnonneg : (0 : ℝ) ≤ 1 / ((K + 1 : ℕ) : ℝ) := by positivity
  linarith

end ErdosStraus.PrimeEstimates

/-! ## Euler products at integers -/

namespace ErdosStraus.PrimeEstimates.Mertens

open Filter Finset Real
open scoped BigOperators

theorem primesUpTo_eq_filter_Icc (n : ℕ) :
    primesUpTo n = (Icc 0 n).filter Nat.Prime := by
  ext p
  simp only [mem_primesUpTo, mem_filter, mem_Icc, Nat.zero_le, true_and]
  tauto

theorem prime_square_sum_le_two (n : ℕ) :
    (∑ p ∈ primesUpTo n, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 2 := by
  apply le_trans _ (sum_reciprocal_sq_le_two n)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp', hpn⟩ := mem_primesUpTo.mp hp
    exact mem_Icc.mpr ⟨hp'.pos, hpn⟩
  · intro p _ _; positivity

/-- `∑_{p ≤ n} 1/p - log log n` is bounded for `n ≥ 2`. -/
theorem reciprocal_defect_bounded :
    ∃ E > 0, ∀ n : ℕ, 2 ≤ n →
      |primeReciprocalSum n - log (log n)| ≤ E := by
  obtain ⟨C, hC, h⟩ := mertensSecond_nat
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  refine ⟨C / log 2 + |mertensSecondConstant| + 1, by positivity, ?_⟩
  intro n hn
  have hln : log (2 : ℝ) ≤ log n := log_le_log (by norm_num) (by exact_mod_cast hn)
  have hh := (h n hn).trans (div_le_div_of_nonneg_left hC.le hl2 hln)
  have heq : primeReciprocalSum n - log (log n) =
      (primeReciprocalSum n - (log (log n) + mertensSecondConstant)) +
        mertensSecondConstant := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith)

/-- The difference `∑_{p ≤ n} (-log(1 - 1/p) - 1/p)` between `-log ∏_{p ≤ n} (1 - 1/p)` and
`∑_{p ≤ n} 1/p`. -/
noncomputable def correction (n : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo n, (-log (1 - 1 / (p : ℝ)) - 1 / p)

theorem correction_bounds (n : ℕ) : 0 ≤ correction n ∧ correction n ≤ 4 := by
  have hlocal : ∀ p ∈ primesUpTo n,
      0 ≤ -log (1 - 1 / (p : ℝ)) - 1 / p ∧
        -log (1 - 1 / (p : ℝ)) - 1 / p ≤ 2 / (p : ℝ) ^ 2 := by
    intro p hp
    have hp' := (mem_primesUpTo.mp hp).1
    have hu := Real.log_le_sub_one_of_pos (primeFactor_pos hp')
    have ha := (abs_le.mp (abs_log_primeFactor_add_le hp')).1
    constructor <;> linarith
  constructor
  · exact Finset.sum_nonneg (fun p hp => (hlocal p hp).1)
  · calc
      correction n ≤ ∑ p ∈ primesUpTo n, 2 / (p : ℝ) ^ 2 :=
        Finset.sum_le_sum (fun p hp => (hlocal p hp).2)
      _ = 2 * ∑ p ∈ primesUpTo n, (1 : ℝ) / (p : ℝ) ^ 2 := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p hp; ring
      _ ≤ 2 * 2 := mul_le_mul_of_nonneg_left (prime_square_sum_le_two n) (by norm_num)
      _ = 4 := by norm_num

theorem log_product_identity (n : ℕ) :
    log (primeProduct n) = -primeReciprocalSum n - correction n := by
  rw [log_primeProduct]
  unfold primeReciprocalSum correction
  rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- `∏_{p ≤ n} (1 - 1/p) ≍ 1/log n` for `n ≥ 2`. -/
theorem product_bounds_nat :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      c / log n ≤ primeProduct n ∧ primeProduct n ≤ C / log n := by
  obtain ⟨E, hE, h⟩ := reciprocal_defect_bounded
  refine ⟨exp (-(E + 4)), exp (E + 4), exp_pos _, exp_pos _, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hln := log_pos hn1
  have hP := primeProduct_pos n
  have hcorr := correction_bounds n
  have hlog : |log (primeProduct n) + log (log n)| ≤ E + 4 := by
    rw [log_product_identity]
    have heq : -primeReciprocalSum n - correction n + log (log n) =
        -(primeReciprocalSum n - log (log n)) - correction n := by ring
    rw [heq]
    exact (abs_sub _ _).trans (by rw [abs_neg, abs_of_nonneg hcorr.1]; linarith [h n hn])
  have hlow := Real.exp_le_exp.mpr (abs_le.mp hlog).1
  have hupp := Real.exp_le_exp.mpr (abs_le.mp hlog).2
  rw [exp_add, exp_log hP, exp_log hln] at hlow hupp
  exact ⟨(div_le_iff₀ hln).mpr hlow, (le_div_iff₀ hln).mpr hupp⟩

end ErdosStraus.PrimeEstimates.Mertens

namespace FareyHD8011Estimates
open Filter Real
open scoped BigOperators Topology
open ErdosStraus.PrimeEstimates.Mertens

def window (n : ℕ) := Finset.Icc ((n+2)/3) ((2*n)/3)
def primes (z : ℕ) := (Finset.Icc 2 z).filter Nat.Prime
noncomputable def mass (n z : ℕ) : ℝ := ((window n).card:ℝ)*(n.totient:ℝ)/n *
    ∏ p ∈ (primes z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ))
noncomputable def initial (n U : ℕ) := ⌊(n:ℝ)^((1:ℝ)/(U:ℝ))⌋₊

theorem local_product (z : ℕ) : (∏ p ∈ primes z, (1-(p:ℝ)⁻¹)) = primeProduct z := by
  have heq : primes z = primesUpTo z := by
    ext p
    simp only [primes, Finset.mem_filter, Finset.mem_Icc, mem_primesUpTo]
    constructor
    · intro h; exact ⟨h.2,h.1.2⟩
    · intro h; exact ⟨⟨h.1.two_le,h.2⟩,h.1⟩
  simp only [heq, primeProduct, one_div]

theorem terminal_floor {n : ℕ} (hn : 12 ≤ n) (hnE : Even n) :
    (2/3:ℝ) * ((window n).card:ℝ) * (primeProduct (Nat.sqrt n))^2 ≤ mass n (Nat.sqrt n) := by
  rw [← local_product]
  exact Conjectures.Goldbach.FareySieveTerminalFloor n hn hnE

theorem cutoff_ratio : ∃ K : ℝ, 0 < K ∧ ∀ U : ℕ, 8 ≤ U →
    ∀ᶠ n : ℕ in atTop, Even n →
      mass n (initial n U) ≤ K * (U:ℝ)^2 * mass n (Nat.sqrt n) := by
  obtain ⟨c,C,hc,hC,h⟩ := product_bounds_nat
  refine ⟨2*(2*C/c)^2, by positivity, ?_⟩
  intro U hU
  have hu : (0:ℝ) < U := by exact_mod_cast (by omega : 0<U)
  have hu2 : (2:ℝ) ≤ U := by exact_mod_cast (by omega : 2 ≤ U)
  have hlim := (tendsto_rpow_atTop (one_div_pos.mpr hu)).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hlim.eventually_ge_atTop 2, eventually_ge_atTop 12] with n hnroot hn hnE
  change 2 ≤ (n:ℝ)^((1:ℝ)/U) at hnroot
  have hpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  let z := initial n U
  let y := Nat.sqrt n
  have hz : 2 ≤ z := Nat.le_floor hnroot
  have hzy : z ≤ y := by
    dsimp [z, y, initial]
    rw [← Real.nat_floor_real_sqrt_eq_nat_sqrt, Real.sqrt_eq_rpow]
    apply Nat.floor_mono
    exact Real.rpow_le_rpow_of_exponent_le hn1 (one_div_le_one_div_of_le (by norm_num) hu2)
  have hyl : 0 < Real.log (y:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  obtain ⟨hzl, _, hlog, _⟩ := floor_log_bounds hnroot
  change 0 < Real.log (z:ℝ) at hzl
  change Real.log ((n:ℝ)^(1/(U:ℝ))) ≤ 2 * Real.log (z:ℝ) at hlog
  rw [Real.log_rpow hpos] at hlog
  have hl : Real.log (n:ℝ) ≤ 2*(U:ℝ)*Real.log (z:ℝ) := by
    field_simp at hlog
    nlinarith [hlog]
  have hyl' : Real.log (y:ℝ) ≤ Real.log (n:ℝ) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0<y)) (by exact_mod_cast Nat.sqrt_le_self n)
  have hratio : primeProduct z / primeProduct y ≤ 2*C/c * (U:ℝ) := by
    apply le_trans (div_le_div₀ (by positivity : 0 ≤ C / Real.log (z:ℝ)) (h z hz).2
      (by positivity : 0 < c / Real.log (y:ℝ)) (h y (hz.trans hzy)).1)
    rw [div_div_eq_mul_div]
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left (hyl'.trans hl) hC.le]
  have hv := (terminal_floor hn hnE)
  have hv0 : 0 ≤ mass n y := le_trans (by positivity) hv
  have hratio0 : 0 ≤ primeProduct z / primeProduct y :=
    div_nonneg (primeProduct_pos _).le (primeProduct_pos _).le
  have raw := Conjectures.Goldbach.FareySieveCutoffRatio n z y hn hnE hz hzy
  change mass n z ≤ 2*((∏ p ∈ primes z, (1-(p:ℝ)⁻¹))/(∏ p ∈ primes y, (1-(p:ℝ)⁻¹)))^2*mass n y at raw
  simp only [local_product] at raw
  calc
    mass n (initial n U) ≤ 2*(primeProduct z/primeProduct y)^2*mass n y := raw
    _ ≤ 2*(2*C/c*(U:ℝ))^2*mass n y := by gcongr
    _ = _ := by ring

theorem terminal_domination : ∀ᶠ n : ℕ in atTop, Even n →
    (n:ℝ)^(9/10:ℝ) ≤ mass n (Nat.sqrt n) := by
  obtain ⟨c,C,hc,_,h⟩ := product_bounds_nat
  have hε : 0 < c^2/6 := by positivity
  have small := (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ)<1/10)).bound hε
  have bounds := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually small
  filter_upwards [bounds,eventually_ge_atTop 12] with n hlog hn hnE
  have hn' : (1:ℝ)<n := by exact_mod_cast (by omega : 1<n)
  have hpos : (0:ℝ)<n := by linarith
  have hl := Real.log_pos hn'
  change ‖Real.log (n:ℝ) ^ (2:ℝ)‖ ≤ c^2/6 * ‖(n:ℝ) ^ (1/10:ℝ)‖ at hlog
  rw [show (2:ℝ)=(2:ℕ) by norm_num, Real.rpow_natCast, Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _)] at hlog
  have hexp : (n:ℝ)^(9/10:ℝ) * (n:ℝ)^(1/10:ℝ) = n := by
    rw [← Real.rpow_add hpos]; norm_num
  have htarget : (n:ℝ)^(9/10:ℝ) ≤ (2/3:ℝ)*((n:ℝ)/4)*(c/Real.log (n:ℝ))^2 := by
    have hh := mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hpos.le (9/10:ℝ))
    rw [← mul_assoc, mul_comm ((n:ℝ)^(9/10:ℝ)) (c^2/6), mul_assoc, hexp] at hh
    field_simp
    nlinarith
  have hcard : (n:ℝ)/4 ≤ ((window n).card:ℝ) := by
    have hnat : n ≤ 4 * (window n).card := by
      rw [window, Nat.card_Icc]; omega
    exact (div_le_iff₀ (by norm_num : (0:ℝ)<4)).mpr (by simpa [mul_comm] using (Nat.cast_le.mpr hnat : (n:ℝ) ≤ ↑(4*(window n).card)))
  have hy : 2 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  have hyl : 0 < Real.log (Nat.sqrt n:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Nat.sqrt n))
  have hylog : Real.log (Nat.sqrt n:ℝ) ≤ Real.log (n:ℝ) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0<Nat.sqrt n)) (by exact_mod_cast Nat.sqrt_le_self n)
  have hm : c/Real.log (n:ℝ) ≤ primeProduct (Nat.sqrt n) :=
    (div_le_div_of_nonneg_left hc.le hyl hylog).trans (h _ hy).1
  calc
    _ ≤ _ := htarget
    _ ≤ (2/3:ℝ)*((window n).card:ℝ)*(primeProduct (Nat.sqrt n))^2 := by
      gcongr
    _ ≤ mass n (Nat.sqrt n) := terminal_floor hn hnE
end FareyHD8011Estimates

/- The block-scale and prime partition lemmas are by Sushaan Kandukoori,
  ErdosStraus/Estimates/PrimeCounts.lean (Apache-2.0), revision
  f6c99eaaca6ec7a7226a7a16bef1cd2b09e36660. -/
namespace ErdosStraus.BrunHooley

/-! ## Blocks of small primes -/

section

open Classical Filter
open scoped BigOperators Topology

/-- The block scales `w_j = w^{2^{-j}}`. -/
noncomputable def blockScale (w : ℝ) (j : ℕ) : ℝ :=
  w ^ ((2 : ℝ) ^ j)⁻¹

@[simp] theorem blockScale_zero (w : ℝ) : blockScale w 0 = w := by
  simp [blockScale]

theorem blockScale_antitone (w : ℝ) (hw : 1 ≤ w) : Antitone (blockScale w) := by
  intro i j hij
  apply Real.rpow_le_rpow_of_exponent_le hw
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hij)

theorem blockScale_square (w : ℝ) (hw : 0 ≤ w) (j : ℕ) :
    blockScale w (j + 1) ^ 2 = blockScale w j := by
  rw [blockScale, ← Real.rpow_natCast, ← Real.rpow_mul hw]
  congr 1
  rw [pow_succ]
  field_simp
  ring

theorem exists_blockScale_le_two (w : ℝ) (hw : 0 < w) :
    ∃ j, blockScale w j ≤ 2 := by
  have hp : Tendsto (fun j : ℕ => ((2 : ℝ) ^ j)⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1))
  have ht : Tendsto (blockScale w) atTop (𝓝 1) := by
    unfold blockScale
    simpa [Function.comp_def] using (Real.continuousAt_const_rpow hw.ne').tendsto.comp hp
  have he := ht.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2))
  obtain ⟨j, hj⟩ := he.exists
  exact ⟨j, hj.le⟩

/-- The first `J` with `w_J ≤ 2`. -/
noncomputable def blockStop (w : ℝ) (hw : 0 < w) : ℕ :=
  Nat.find (exists_blockScale_le_two w hw)

theorem blockStop_terminal (w : ℝ) (hw : 0 < w) :
    blockScale w (blockStop w hw) ≤ 2 :=
  Nat.find_spec (exists_blockScale_le_two w hw)

/-- The primes `p < w` with `p ∤ q`. -/
noncomputable def primeSupport (w : ℝ) (q : ℕ) : Finset ℕ :=
  (Finset.range (⌊w⌋₊ + 1)).filter
    (fun p => Nat.Prime p ∧ (p : ℝ) < w ∧ ¬p ∣ q)

@[simp] theorem mem_primeSupport {w : ℝ} {q p : ℕ} :
    p ∈ primeSupport w q ↔ Nat.Prime p ∧ (p : ℝ) < w ∧ ¬p ∣ q := by
  simp only [primeSupport, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact And.right
  · intro h
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor h.2.1.le), h⟩

/-- The block of primes `p < w` with `p ∤ q` and `max(2, w_{j+1}) ≤ p < w_j`, for `j < J`. -/
noncomputable def primeBlocks (w : ℝ) (q J : ℕ) (j : Fin J) : Finset ℕ :=
  (primeSupport w q).filter (fun p =>
    max 2 (blockScale w ((j : ℕ) + 1)) ≤ (p : ℝ) ∧ (p : ℝ) < blockScale w j)

@[simp] theorem mem_primeBlocks {w : ℝ} {q J p : ℕ} {j : Fin J} :
    p ∈ primeBlocks w q J j ↔
      Nat.Prime p ∧ (p : ℝ) < w ∧ ¬p ∣ q ∧
        max 2 (blockScale w ((j : ℕ) + 1)) ≤ (p : ℝ) ∧
          (p : ℝ) < blockScale w j := by
  simp only [primeBlocks, Finset.mem_filter, mem_primeSupport]
  tauto

theorem primeBlocks_disjoint (w : ℝ) (hw : 1 ≤ w) (q J : ℕ) :
    Pairwise (fun j k => Disjoint (primeBlocks w q J j) (primeBlocks w q J k)) := by
  intro j k hjk
  apply Finset.disjoint_left.mpr
  intro p hpj hpk
  have hj := (mem_primeBlocks.mp hpj).2.2.2
  have hk := (mem_primeBlocks.mp hpk).2.2.2
  have hne : (j : ℕ) ≠ k := fun h => hjk (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hscale := blockScale_antitone w hw (Nat.succ_le_iff.mpr hlt)
    have hlower := (le_max_right 2 (blockScale w ((j : ℕ) + 1))).trans hj.1
    linarith [hk.2]
  · have hscale := blockScale_antitone w hw (Nat.succ_le_iff.mpr hgt)
    have hlower := (le_max_right 2 (blockScale w ((k : ℕ) + 1))).trans hk.1
    linarith [hj.2]

theorem primeBlocks_cover (w : ℝ) (q J : ℕ) (hstop : blockScale w J ≤ 2) :
    (Finset.univ.biUnion (primeBlocks w q J)) = primeSupport w q := by
  ext p
  constructor
  · intro hp
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_filter.mp hj).1
  · intro hp
    have hp' := mem_primeSupport.mp hp
    have htwo : (2 : ℝ) ≤ p := by exact_mod_cast hp'.1.two_le
    have hex : ∃ k, blockScale w k ≤ (p : ℝ) := ⟨J, hstop.trans htwo⟩
    let k := Nat.find hex
    have hk : blockScale w k ≤ (p : ℝ) := Nat.find_spec hex
    have hkpos : 0 < k := by
      by_contra h
      have he : k = 0 := by omega
      simpa [he] using hk.trans_lt hp'.2.1
    have hkJ : k ≤ J := Nat.find_min' hex (hstop.trans htwo)
    have hprev : (p : ℝ) < blockScale w (k - 1) :=
      lt_of_not_ge (Nat.find_min hex (by omega : k - 1 < k))
    refine Finset.mem_biUnion.mpr ⟨⟨k - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨hp, ?_, hprev⟩
    rw [show k - 1 + 1 = k by omega]
    exact max_le htwo hk

theorem primeBlocks_primes (w : ℝ) (q J : ℕ) :
    ∀ j p, p ∈ primeBlocks w q J j → Nat.Prime p :=
  fun _ _ hp => (mem_primeBlocks.mp hp).1

theorem primeBlocks_coprime (w : ℝ) (q J : ℕ) :
    ∀ j p, p ∈ primeBlocks w q J j → Nat.Coprime q p := by
  intro j p hp
  have h := mem_primeBlocks.mp hp
  exact h.1.coprime_iff_not_dvd.mpr h.2.2.1 |>.symm

theorem primeBlocks_bound (w : ℝ) (q J : ℕ) :
    ∀ j p, p ∈ primeBlocks w q J j →
      (p : ℝ) ≤ w ^ ((2 : ℝ) ^ (j : ℕ))⁻¹ :=
  fun _ _ hp => (mem_primeBlocks.mp hp).2.2.2.2.le

end
theorem primeBlocks_in_square (w : ℝ) (hw : 0 ≤ w) (q J : ℕ) (j : Fin J) :
    ∀ p ∈ primeBlocks w q J j,
      Nat.Prime p ∧ max 2 (blockScale w ((j : ℕ) + 1)) ≤ (p : ℝ) ∧
        (p : ℝ) < (max 2 (blockScale w ((j : ℕ) + 1))) ^ 2 := by
  intro p hp
  have hp' := mem_primeBlocks.mp hp
  refine ⟨hp'.1, hp'.2.2.2.1, hp'.2.2.2.2.trans_le ?_⟩
  rw [← blockScale_square w hw j]
  apply pow_le_pow_left₀
  · exact Real.rpow_nonneg hw _
  · exact le_max_right _ _

end ErdosStraus.BrunHooley

namespace HD8011
open Finset ErdosStraus.BrunHooley
open scoped BigOperators
noncomputable section

theorem rank_budget (J R : ℕ) (P : Fin J → Finset ℕ)
    (hd : Pairwise (fun j k => Disjoint (P j) (P k))) (w : ℝ) (hw : 1 ≤ w)
    (hb : ∀ j p, p ∈ P j → (p : ℝ) ≤ w ^ ((2 : ℝ) ^ (j : ℕ))⁻¹)
    (k : Fin J → ℕ) (hk : ∀ j : Fin J, k j ≤ 2*(R+j.val)+1)
    {f : Fin J → Finset ℕ} (hf : f ∈ choices P k) :
    (selectedProduct f : ℝ) ≤ w ^ (8*(R+1)) := by
  have hbase (j : Fin J) : 1 ≤ w ^ ((2 : ℝ) ^ (j : ℕ))⁻¹ :=
    Real.one_le_rpow hw (by positivity)
  have hh := selectedProduct_le_block_budget P hd k
    (fun j => w ^ ((2 : ℝ) ^ (j : ℕ))⁻¹) hbase hb hf
  have mon (j : Fin J) : k j ≤ (R+1)*(2*(j.val+1)) := by
    have := hk j
    nlinarith [Nat.zero_le (R*j.val)]
  apply hh.trans
  calc
    (∏ j : Fin J, (w ^ ((2 : ℝ) ^ (j : ℕ))⁻¹) ^ k j)
      ≤ ∏ j : Fin J, (w ^ ((2:ℝ)^j.val)⁻¹) ^ ((R+1)*(2*(j.val+1))) := by
        gcongr with j <;> first | exact hbase j | exact mon j
    _ = w ^ (∑ j : Fin J, ((R:ℝ)+1) * (2*(j.val+1:ℝ)/2^j.val)) := by
      rw [Real.rpow_sum_of_pos (by linarith : 0<w)]
      apply Finset.prod_congr rfl
      intro j _
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0≤w)]
      congr 1
      push_cast
      ring
    _ ≤ w ^ (8*(R+1)) := by
      rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun j : ℕ => 2*(j+1:ℝ)/2^j) J,
          ← Real.rpow_natCast w (8*(R+1))]
      apply Real.rpow_le_rpow_of_exponent_le hw
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left (weighted_geometric_budget J) (show 0 ≤ (R:ℝ)+1 by positivity)]

theorem terminal_scale (z : ℕ) : blockScale ((z:ℝ)+1) (z+1) ≤ 2 := by
  have hz : 0 < (z:ℝ)+1 := by positivity
  have hpow : z+1 ≤ 2^(z+1) := by
    have := Nat.lt_two_pow_self (n := z+1)
    omega
  have hbase : (z:ℝ)+1 ≤ (2:ℝ)^(2^(z+1) : ℕ) := by
    have h := hpow.trans (Nat.lt_two_pow_self (n:=2^(z+1))).le
    exact_mod_cast h
  unfold blockScale
  calc
    _ ≤ ((2:ℝ)^(2^(z+1) : ℕ)) ^ ((2:ℝ)^(z+1))⁻¹ :=
      Real.rpow_le_rpow hz.le hbase (by positivity)
    _ = 2 := by
      rw [← Real.rpow_natCast (2:ℝ) (2^(z+1) : ℕ), ← Real.rpow_mul (by norm_num : 0≤(2:ℝ))]
      push_cast
      rw [mul_inv_cancel₀ (by positivity), Real.rpow_one]

end
end HD8011

namespace HD8011
open Finset Filter
open scoped Topology
noncomputable section

theorem card_divisors_sqrt (n : ℕ) : n.divisors.card ≤ 2*(n.sqrt + 1) := by
 classical
 let T := Finset.range (n.sqrt+1)
 have hs : n.divisors ⊆ T ∪ T.image (fun d => n/d) := by
   intro a ha
   by_cases h : a ≤ n.sqrt
   · exact mem_union_left _ (mem_range.mpr (by omega))
   · have hd := Nat.dvd_of_mem_divisors ha
     have hmul := Nat.div_mul_cancel hd
     have hsq := Nat.lt_succ_sqrt n
     have hb : n / a ≤ n.sqrt := by
       by_contra! hbad
       have hh := Nat.mul_le_mul (show n.sqrt+1 ≤ n/a by omega) (show n.sqrt+1 ≤ a by omega)
       nlinarith
     apply mem_union_right
     apply mem_image.mpr
     exact ⟨n/a, mem_range.mpr (by omega), Nat.div_div_self hd (Nat.ne_zero_of_mem_divisors ha)⟩
 calc
    _ ≤ (T ∪ T.image (fun d => n/d)).card := card_le_card hs
    _ ≤ T.card + (T.image (fun d => n/d)).card := card_union_le _ _
    _ ≤ T.card + T.card := Nat.add_le_add_left card_image_le _
    _ = _ := by simp [T, two_mul]

/-- The number of terms in a block choice is small enough for the available
    single-intersection error. -/
theorem relative_degree (U : ℕ) (hU : 1024 ≤ U) :
    (8 : ℝ) * ((U / 1024 : ℕ) + 1) * (2 / U) ≤ 1/16 := by
 have h := Nat.div_mul_le_self U 1024
 have hr : ((U/1024 : ℕ):ℝ)*1024 ≤ U := by exact_mod_cast h
 have hu : (1024:ℝ) ≤ U := by exact_mod_cast hU
 have hu0 : 0 < (U:ℝ) := by linarith
 field_simp
 nlinarith

theorem bounds_eventually (U : ℕ) (hu : 1024 ≤ U) :
    ∀ᶠ n : ℕ in atTop, let z := ⌊(n:ℝ)^(1/(U:ℝ))⌋₊
      let w := z+1
      let m := w^(8*(U/1024+1))
      (w:ℝ) ≤ (n:ℝ)^(1/16:ℝ) ∧ (m:ℝ) ≤ (n:ℝ)^(1/16:ℝ) := by
 have hu' : (1024:ℝ) ≤ U := by exact_mod_cast hu
 have hu0 : 0 < (U:ℝ) := by linarith
 have hlim : Tendsto (fun n : ℕ => (n:ℝ)^(1/(U:ℝ))) atTop atTop :=
   (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
 filter_upwards [hlim.eventually_ge_atTop 2, eventually_ge_atTop 1] with n hn hn1
 let x : ℝ := (n:ℝ)^(1/(U:ℝ))
 have hx : 2 ≤ x := hn
 have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn1
 have hnn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
 have hfloor := Nat.floor_le (show 0 ≤ x by positivity [x])
 have hw : (⌊x⌋₊:ℝ) + 1 ≤ (n:ℝ)^(2/(U:ℝ)) := by
   rw [show (2:ℝ)/(U:ℝ) = (1/(U:ℝ))*2 by ring,Real.rpow_mul hnn,Real.rpow_two]
   change (⌊x⌋₊:ℝ) + 1 ≤ x^2
   nlinarith
 dsimp only
 push_cast
 change (⌊x⌋₊:ℝ) + 1 ≤ _ ∧ ((⌊x⌋₊:ℝ) + 1)^_ ≤ _
 constructor
 · exact hw.trans (Real.rpow_le_rpow_of_exponent_le hnR ((div_le_iff₀ hu0).2 (by linarith)))
 · have ht := pow_le_pow_left₀ (show 0 ≤ (⌊x⌋₊:ℝ) + 1 by positivity) hw (8*(U/1024+1))
   apply ht.trans
   rw [← Real.rpow_natCast _ (8*(U/1024+1)), ← Real.rpow_mul hnn]
   apply Real.rpow_le_rpow_of_exponent_le hnR
   push_cast
   simpa only [mul_comm, mul_left_comm, mul_assoc] using relative_degree U hu
end
end HD8011

namespace HD8011
open Finset Filter
open scoped Topology
noncomputable section

theorem absorb_rounding :
    ∀ᶠ n : ℕ in atTop, ∀ J D : ℕ, (J:ℝ) ≤ (n:ℝ)^(1/16:ℝ) →
      (D:ℝ) ≤ (n:ℝ)^(1/16:ℝ) → 1 ≤ D →
      (1+2*(J:ℝ))*((D:ℝ)*(1+Real.log D)*n.divisors.card) ≤
        (n:ℝ)^(9/10:ℝ)/16 := by
 have hlim : Tendsto (fun n : ℕ => (n:ℝ)^(17/80:ℝ)) atTop atTop :=
   (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
 filter_upwards [hlim.eventually_ge_atTop 384, eventually_ge_atTop 1] with n hn hn1
 intro J D hJ hD hD1
 have hx : (1:ℝ) ≤ n := by exact_mod_cast hn1
 have hX : (0:ℝ) < n := by linarith
 have h16 := Real.one_le_rpow hx (by norm_num : (0:ℝ)≤1/16)
 have hsqrt : (n.sqrt:ℝ) ≤ Real.sqrt n := by
   apply Real.le_sqrt_of_sq_le
   exact_mod_cast (show n.sqrt ^ 2 ≤ n by simpa [pow_two] using Nat.sqrt_le n)
 have ht : (n.divisors.card:ℝ) ≤ 4*(n:ℝ)^(1/2:ℝ) := by
   have hh : (n.divisors.card:ℝ) ≤ 2*((n.sqrt:ℝ)+1) := by exact_mod_cast card_divisors_sqrt n
   rw [← Real.sqrt_eq_rpow]
   have h1 : (1:ℝ) ≤ Real.sqrt n := (Real.le_sqrt (by norm_num) hX.le).2 (by simpa using hx)
   linarith
 have hlog : 0 ≤ 1+Real.log D := by
   have := Real.log_nonneg (show 1 ≤ (D:ℝ) by exact_mod_cast hD1)
   linarith
 have hlog' : 1+Real.log D ≤ 2*(n:ℝ)^(1/16:ℝ) := by
   have := Real.log_le_sub_one_of_pos (show (0:ℝ)< D by exact_mod_cast (show 0<D by omega))
   linarith
 have hJ' : 1+2*(J:ℝ) ≤ 3*(n:ℝ)^(1/16:ℝ) := by linarith
 calc
   _ ≤ (3*(n:ℝ)^(1/16:ℝ))*((n:ℝ)^(1/16:ℝ)*(2*(n:ℝ)^(1/16:ℝ))*(4*(n:ℝ)^(1/2:ℝ))) := by gcongr
   _ = 24 * (n:ℝ)^(11/16:ℝ) := by
     rw [show (11/16:ℝ) = 1/16 + 1/16 + 1/16 + 1/2 by norm_num,
       Real.rpow_add hX, Real.rpow_add hX, Real.rpow_add hX]
     ring
   _ ≤ _ := by
     rw [show (9/10:ℝ) = 11/16 + 17/80 by norm_num, Real.rpow_add hX]
     nlinarith [mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg hX.le (11/16:ℝ))]
end
end HD8011

/-! The three Legendre identities below are adapted from Sushaan Kandukoori,
ErdosStraus/Estimates/Mertens.lean (Apache-2.0), at commit f6c99eaaca6ec7a7226a7a16bef1cd2b09e36660.
The block bound uses the elementary inequality x ≤ 2 floor(x) for x ≥ 1. -/

namespace FareyMass
open Finset Real
open scoped BigOperators ArithmeticFunction Nat
/-- `log n! = ∑_{m ≤ n} log m`. -/
theorem log_factorial_eq_sum_log (n : ℕ) :
    log (n ! : ℝ) = ∑ m ∈ Icc 1 n, log (m : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity), ih,
      Finset.sum_Icc_succ_top (by omega)]
    ring

/-- Legendre's identity `log n! = ∑_{d ≤ n} Λ(d) ⌊n/d⌋`. -/
theorem log_factorial_eq (n : ℕ) :
    log (n ! : ℝ) = ∑ d ∈ Icc 1 n, Λ d * ((n / d : ℕ) : ℝ) := by
  rw [log_factorial_eq_sum_log]
  have hdiv : ∀ m ∈ Icc 1 n, log (m : ℝ) = ∑ d ∈ m.divisors, Λ d := fun m _ =>
    ArithmeticFunction.vonMangoldt_sum.symm
  rw [Finset.sum_congr rfl hdiv,
    Finset.sum_comm' (t' := Icc 1 n) (s' := fun d => (Icc 1 n).filter (fun m => d ∣ m))]
  · apply Finset.sum_congr rfl
    intro d _
    have hIcc : Icc 1 n = Ioc 0 n := Finset.Icc_add_one_left_eq_Ioc 0 n
    rw [sum_const, nsmul_eq_mul, hIcc, Nat.Ioc_filter_dvd_card_eq_div, mul_comm]
  · intro m d
    simp only [mem_Icc, Nat.mem_divisors, mem_filter]
    constructor
    · rintro ⟨⟨h1, hm⟩, hdm, -⟩
      exact ⟨⟨⟨h1, hm⟩, hdm⟩, Nat.pos_of_dvd_of_pos hdm h1, (Nat.le_of_dvd h1 hdm).trans hm⟩
    · rintro ⟨⟨⟨h1, hm⟩, hdm⟩, -, -⟩
      exact ⟨⟨h1, hm⟩, hdm, by omega⟩

/-- `⌊n/d⌋ ≤ n/d ≤ ⌊n/d⌋ + 1`. -/
theorem natDiv_le_div_le (n d : ℕ) (hd : 0 < d) :
    ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d ∧ (n : ℝ) / d ≤ ((n / d : ℕ) : ℝ) + 1 := by
  refine ⟨Nat.cast_div_le, ?_⟩
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_le_iff₀ hdr]
  have h3 : (n : ℝ) = d * (n / d : ℕ) + (n % d : ℕ) := by exact_mod_cast (Nat.div_add_mod n d).symm
  have h4 : ((n % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt n hd).le
  nlinarith

/-- On a logarithmic block [v,v²], the reciprocal mass of any subset of the
primes is at most 4 by the factorial estimate above. -/
theorem reciprocal_block (S : Finset ℕ) (v : ℝ) (hv : 1 < v)
    (hS : ∀ p ∈ S, p.Prime ∧ v ≤ (p : ℝ) ∧ (p : ℝ) ≤ v^2) :
    ∑ p ∈ S, 1/(p:ℝ) ≤ 4 := by
  let N := ⌊v^2⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by simpa using (one_le_pow₀ hv.le : (1:ℝ) ≤ v^2))
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hN1
  have hlog := Real.log_pos hv
  have hin : S ⊆ Finset.Icc 1 N := by
    intro p hp
    obtain ⟨hprime,_,hub⟩ := hS p hp
    exact Finset.mem_Icc.mpr ⟨hprime.pos,Nat.le_floor hub⟩
  have hle : ∑ p ∈ S, ((N:ℝ) * Real.log v) * (1/(p:ℝ)) ≤
       ∑ p ∈ S, 2 * (Λ p * ((N / p : ℕ) : ℝ)) := by
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨hprime,hlo,_⟩ := hS p hp
    obtain ⟨_,hpN⟩ := Finset.mem_Icc.mp (hin hp)
    have hpR : 0 < (p:ℝ) := by exact_mod_cast hprime.pos
    have hge : 1 ≤ N / p := Nat.div_pos hpN hprime.pos
    have hgeR : 1 ≤ ((N / p : ℕ) : ℝ) := by exact_mod_cast hge
    have hdiv := (natDiv_le_div_le N p hprime.pos).2
    have hdiv2 : (N:ℝ)/p ≤ 2 * ((N/p : ℕ):ℝ) := by linarith
    have hprod := mul_le_mul hdiv2 (Real.log_le_log (by linarith) hlo)
      hlog.le (show 0 ≤ 2 * ((N/p : ℕ):ℝ) by positivity)
    rw [ArithmeticFunction.vonMangoldt_apply_prime hprime]
    calc
      (N:ℝ) * log v * (1 / p) = ((N:ℝ)/p)*log v := by ring
      _ ≤ _ := hprod.trans_eq (by ring)
  have hall := Finset.sum_le_sum_of_subset_of_nonneg (f:=fun p : ℕ => 2*(Λ p*((N/p:ℕ):ℝ))) hin
    (fun p _ _ => mul_nonneg (by norm_num) (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)))
  rw [← Finset.mul_sum] at hle
  rw [← Finset.mul_sum (Finset.Icc 1 N), ← log_factorial_eq] at hall
  have hlogF : log (N ! : ℝ) ≤ (N:ℝ) * log N := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.factorial_le_pow N)
  have hlogN := Real.log_le_log hNr (Nat.floor_le (sq_nonneg v) : (N:ℝ) ≤ v^2)
  rw [Real.log_pow] at hlogN
  have hresult := hle.trans hall
  apply le_of_mul_le_mul_left _ (mul_pos hNr hlog)
  have aux := mul_le_mul_of_nonneg_left hlogN hNr.le
  norm_num at aux
  calc
    _ ≤ 2 * log (N ! : ℝ) := hresult
    _ ≤ 2 * ((N:ℝ) * log N) := by linarith
    _ ≤ 2 * ((N:ℝ) * (2 * log v)) := by linarith
    _ = _ := by ring

theorem double_mass_block (S : Finset ℕ) (v : ℝ) (hv : 1 < v)
    (hS : ∀ p ∈ S, p.Prime ∧ v ≤ (p : ℝ) ∧ (p : ℝ) ≤ v^2) :
    ∑ p ∈ S, 2/(p:ℝ) ≤ 8 := by
  have h := mul_le_mul_of_nonneg_left (reciprocal_block S v hv hS) (by norm_num : (0:ℝ) ≤ 2)
  norm_num [Finset.mul_sum, div_eq_mul_inv] at h ⊢
  exact h

end FareyMass

/-! The local Euler-product comparison adapts the argument in Sushaan Kandukoori,
ErdosStraus/Estimates/BrunHooley.lean (Apache-2.0). The normalized
exponential tail and the rank/ratio absorption below are proved here. -/

open Finset
open scoped BigOperators

namespace FareyTail

/-- Euler product for local weights at most two thirds. The logarithmic
inequality follows by bounding the slope of log(1-x) on [0,2/3]. -/
theorem euler_lower {α : Type*} (P : Finset α) (w : α → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p ∧ w p ≤ 2 / 3) (H : ℝ)
    (hSum : (∑ p ∈ P, w p) ≤ H) :
    Real.exp (-3 * H) ≤ ∏ p ∈ P, (1 - w p) := by
  have oneFactor (p : α) (hp : p ∈ P) : Real.exp (-3 * w p) ≤ 1 - w p := by
    obtain ⟨hw0,hw1⟩ := hw p hp
    have hpos : 0 < 1 - w p := by linarith
    have hbound : (1 - w p)⁻¹ ≤ 3 := (inv_le_iff_one_le_mul₀ hpos).mpr (by linarith)
    have hid := inv_mul_cancel₀ hpos.ne'
    have hwBound := mul_le_mul_of_nonneg_right hbound hw0
    have hlog := Real.one_sub_inv_le_log_of_pos hpos
    exact (Real.le_log_iff_exp_le hpos).mp (by nlinarith)
  calc
    _ ≤ Real.exp (∑ p ∈ P, -3 * w p) := by rw [← Finset.mul_sum]; exact Real.exp_le_exp.mpr (by linarith)
    _ = ∏ p ∈ P, Real.exp (-3 * w p) := Real.exp_sum _ _
    _ ≤ _ := Finset.prod_le_prod₀ (fun p _ => (Real.exp_pos _).le) oneFactor

private theorem factorial_bound (H : ℝ) (hH : 0 ≤ H) (m : ℕ) :
    H ^ m / (m.factorial : ℝ) ≤ Real.exp (2 * H) / (2:ℝ)^m := by
  apply (le_div_iff₀ (by positivity)).mpr
  have he : (2 * H)^m / (m.factorial : ℝ) ≤ Real.exp (2 * H) := by
    apply le_trans _ (Real.sum_le_exp_of_nonneg (show 0 ≤ 2*H by positivity) (m+1))
    exact Finset.single_le_sum (s := Finset.range (m+1))
      (f := fun k : ℕ => (2*H)^k / (k.factorial:ℝ))
      (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self _))
  rw [mul_pow] at he
  linarith only [he, (show H ^ m / (m.factorial : ℝ) * 2 ^ m =
                          (2 ^ m * H ^ m) / (m.factorial : ℝ) by ring)]

private theorem geom_half (n : ℕ) :
    (∑ j : Fin n, (1:ℝ) / 2^((j:ℕ)+1)) ≤ 1 := by
  have h : (∑ j ∈ Finset.range n, (1:ℝ)/2^(j+1)) = 1 - 1/(2:ℝ)^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]; ring
  calc
    _ = ∑ k ∈ Finset.range n, (1:ℝ)/2^(k+1) := Fin.sum_univ_eq_sum_range (fun k : ℕ => (1:ℝ)/2^(k+1)) n
    _ = _ := h
    _ ≤ 1 := sub_le_self _ (by positivity)

/-- The first omitted coefficient at ranks R+j has uniformly summable
normalized error, exponentially small as R increases. -/
theorem normalized_tail {α : Type*} (n R : ℕ) (P : Fin n → Finset α)
    (w : α → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hw : ∀ j p, p ∈ P j → 0 ≤ w p ∧ w p ≤ 2 / 3)
    (hSum : ∀ j, (∑ p ∈ P j, w p) ≤ H) :
    (∑ j : Fin n, ((∑ p ∈ P j, w p) ^ (2*(R + (j:ℕ)) + 1) /
      ((2*(R + (j:ℕ)) + 1).factorial : ℝ)) / (∏ p ∈ P j, (1-w p))) ≤
        Real.exp (5*H) / (2:ℝ) ^ (2*R) := by
  let C := Real.exp (5*H) / (2:ℝ)^(2*R)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ ∑ j : Fin n, C * (1 / (2:ℝ)^((j:ℕ)+1)) := by
      apply Finset.sum_le_sum
      intro j _
      let m := 2*(R+j.val)+1
      have hEuler := euler_lower (P j) w (hw j) H (hSum j)
      have hpow : (∑ p ∈ P j, w p)^m / (m.factorial:ℝ) ≤ H^m / (m.factorial:ℝ) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (Finset.sum_nonneg (fun p hp => (hw j p hp).1)) (hSum j) _) (by positivity)
      have h := div_le_div₀ (by positivity : 0 ≤ Real.exp (2*H) / (2:ℝ)^m)
        (hpow.trans (factorial_bound H hH m)) (Real.exp_pos _) hEuler
      apply h.trans
      have h2 : ((2:ℝ)^(2*R)) * 2^((j:ℕ)+1) ≤ 2^m := by
        rw [← pow_add]
        exact pow_le_pow_right₀ (by norm_num) (by dsimp [m]; omega)
      have hrewrite : Real.exp (2*H) / (2:ℝ)^m / Real.exp (-3*H) =
          Real.exp (5*H) / (2:ℝ)^m := by
        rw [show (5:ℝ)*H = 2*H - (-3*H) by ring, Real.exp_sub]
        ring
      rw [hrewrite]
      dsimp only [C]
      rw [show Real.exp (5 * H) / (2:ℝ)^(2*R) * (1 / 2^((j:ℕ)+1)) =
          Real.exp (5*H) / (2^(2*R) * 2^((j:ℕ)+1)) by ring]
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) h2
    _ = C * (∑ j : Fin n, (1:ℝ)/2^((j:ℕ)+1)) := (Finset.mul_sum _ _ _).symm
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left (geom_half n) hC
    _ = _ := mul_one _

end FareyTail

namespace FareyTail

open Filter Topology

/-- The total main-term error times any fixed quadratic-in-U ratio fits
in any prescribed positive budget for all sufficiently large U. -/
theorem eventually_control (H C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ U₀ : ℕ, 8 ≤ U₀ ∧ ∀ U : ℕ, U₀ ≤ U →
      let e := Real.exp (5*H) / (2:ℝ)^(2*(U / 1024))
      C * (U:ℝ)^2 * (e * Real.exp e) ≤ δ := by
  let A := Real.exp (5*H)
  have h0 : Tendsto (fun k : ℕ => A / (4:ℝ)^k) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1:ℝ)<4)).const_mul A
  have h2 := tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1:ℝ)<4)
  let f := fun k : ℕ => (C * 2048^2 * A) * ((k:ℝ)^2 / (4:ℝ)^k) * Real.exp (A / (4:ℝ)^k)
  have hf : Tendsto f atTop (𝓝 0) := by
    simpa [f] using ((h2.const_mul (C * 2048^2 * A)).mul (Real.continuous_exp.continuousAt.tendsto.comp h0))
  obtain ⟨k₀, hk⟩ := eventually_atTop.mp (hf.eventually (gt_mem_nhds hδ))
  refine ⟨1024*(k₀+1), by omega, ?_⟩
  intro U hU
  let k := U / 1024
  have hk1 : 1 ≤ k := by dsimp [k]; omega
  have hkk : k₀ ≤ k := by dsimp [k]; omega
  have hub : U ≤ 2048*k := by dsimp [k] at hk1 ⊢; omega
  have hc : (U:ℝ) ≤ 2048*(k:ℝ) := by exact_mod_cast hub
  have hpow : (U:ℝ)^2 ≤ (2048*(k:ℝ))^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hc _
  have hs : (2:ℝ)^(2*k) = (4:ℝ)^k := by rw [pow_mul]; norm_num
  change C * (U:ℝ)^2 * ((A / (2:ℝ)^(2*k)) * Real.exp (A/(2:ℝ)^(2*k))) ≤ δ
  rw [hs]
  apply le_trans _ (hk k hkk).le
  dsimp only [f]
  have ha : 0 < A := Real.exp_pos _
  calc
    _ ≤ C * (2048*(k:ℝ))^2 * ((A/(4:ℝ)^k) * Real.exp (A/(4:ℝ)^k)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC) (by positivity)
    _ = _ := by ring

end FareyTail

namespace HD8011
open Finset ErdosStraus.BrunHooley
open scoped BigOperators

theorem blockWeights (w : ℝ) (n J : ℕ) (hn : Even n) (j : Fin J) (p : ℕ)
    (hp : p ∈ primeBlocks w n J j) : 0 ≤ 2 / (p : ℝ) ∧ 2 / (p:ℝ) ≤ 2/3 := by
  have h := mem_primeBlocks.mp hp
  have hpr := h.1.two_le
  have hne : p ≠ 2 := fun hh => h.2.2.1 (hh ▸ (even_iff_two_dvd.mp hn))
  have hp3 : (3:ℝ) ≤ p := by exact_mod_cast (show 3≤p by omega)
  exact ⟨by positivity, div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3⟩

theorem blockTail (w : ℝ) (hw : 0 ≤ w) (n J R : ℕ) (hn : Even n) :
   (∑ j : Fin J, ((∑ p ∈ primeBlocks w n J j, 2/(p:ℝ)) ^ (2*(R+j.val)+1) /
      ((2*(R+j.val)+1).factorial : ℝ)) / (∏ p ∈ primeBlocks w n J j, (1 - 2/(p:ℝ)))) ≤
        Real.exp (5*8) / (2:ℝ)^(2*R) := by
  apply FareyTail.normalized_tail J R (primeBlocks w n J) (fun p => 2/(p:ℝ)) 8 (by norm_num)
    (blockWeights w n J hn)
  intro j
  apply FareyMass.double_mass_block (primeBlocks w n J j) (max 2 (blockScale w (j.val+1)))
    (lt_of_lt_of_le (by norm_num : (1:ℝ)<2) (le_max_left _ _))
  intro p hp
  obtain ⟨h1,h2,h3⟩ := primeBlocks_in_square w hw n J j p hp
  exact ⟨h1,h2,h3.le⟩

end HD8011

namespace FareyBrun
open Finset ErdosStraus.RoughEstimates ErdosStraus.BrunHooley
open scoped BigOperators
noncomputable section
open scoped Classical

def window (n l h : ℕ) : Finset ℕ := (Icc l h).filter (fun u => u.Coprime n)
def numeratorHit (n p u : ℕ) : Prop := p ∣ u*(n-u)
def windowMass (n l h : ℕ) : ℝ := ((h-l+1:ℕ):ℝ)*(n.totient:ℝ)/(n:ℝ)
def density (p : ℕ) : ℝ := 2/(p:ℝ)

theorem intersection_window (n l h : ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    intersectionCount (window n l h) (numeratorHit n) s =
      ((((Icc l h).filter (fun u => u.Coprime n ∧ (∏ p ∈ s, p) ∣ u*(n-u))).card : ℕ):ℝ) := by
  classical
  unfold intersectionCount window
  congr 2
  ext u
  constructor
  · intro hu
    obtain ⟨hi, hv⟩ := mem_filter.mp hu
    obtain ⟨hi, hc⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨hi, hc, prod_primes_dvd _ (fun p hp => (hs p hp).prime) hv⟩
  · intro hu
    obtain ⟨hi, hc, hd⟩ := mem_filter.mp hu
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hi, hc⟩, fun p hp => (Finset.dvd_prod_of_mem id hp).trans hd⟩

theorem window_remainder_one (n l h : ℕ) (hn : 1 < n) (hlh : l ≤ h) (hhn : h < n)
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (hnot : ∀ p ∈ s, ¬p∣n) :
    |intersectionCount (window n l h) (numeratorHit n) s -
      windowMass n l h * ∏ p ∈ s, density p| ≤
       (2:ℝ)^s.card * n.divisors.card := by
  classical
  let d := ∏ p ∈ s, p
  have hdp : d.primeFactors = s := Nat.primeFactors_prod hs
  have hpos : 0 < d := prod_pos (fun p hp => (hs p hp).pos)
  have hsq : Squarefree d := by
    exact Finset.squarefree_prod_of_pairwise_isCoprime
      (fun p hp q hq hpq => Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq))
      (fun p hp => (hs p hp).prime.squarefree)
  have hcop : d.Coprime n := Nat.coprime_prod_left_iff.mpr
    (fun p hp => (hs p hp).coprime_iff_not_dvd.mpr (hnot p hp))
  have h := Conjectures.Goldbach.FareyFullSieveRemainder n d l h hn hpos hsq hcop hlh hhn
  dsimp only at h
  rw [hdp] at h
  rw [intersection_window _ _ _ _ hs]
  have hw : ∏ p ∈ s, density p = (2:ℝ)^s.card/(d:ℝ) := by
    simp [density, Finset.prod_div_distrib, d, Nat.cast_prod]
  rw [hw]
  unfold windowMass
  convert h using 2
  ring

theorem window_remainder_choice {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n l h : ℕ) (hn : 1 < n) (hlh : l ≤ h) (hhn : h < n)
    (P : ι → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hnot : ∀ j p, p ∈ P j → ¬p∣n)
    (hdisj : Pairwise (fun j k => Disjoint (P j) (P k)))
    (k : ι → ℕ) (f : ι → Finset ℕ) (hf : f ∈ choices P k) :
    |intersectionCount (window n l h) (numeratorHit n) (selected f) -
      windowMass n l h * ∏ j, ∏ p ∈ f j, density p| ≤
       (2:ℝ)^(selectedProduct f).primeFactors.card * n.divisors.card := by
  classical
  have hp := selected_primes hP hf
  have hnot' : ∀ p ∈ selected f, ¬p∣n := by
    intro p hp
    obtain ⟨j, -, hj⟩ := mem_biUnion.mp hp
    exact hnot j p ((mem_choices.mp hf j).1 hj)
  have h := window_remainder_one n l h hn hlh hhn (selected f) hp hnot'
  have hprod : ∏ p ∈ selected f, density p = ∏ j, ∏ p ∈ f j, density p := by
    apply Finset.prod_biUnion
    intro j _ k _ hjk
    exact (hdisj hjk).mono ((mem_choices.mp hf j).1) ((mem_choices.mp hf k).1)
  rw [hprod] at h
  have hpf : (selectedProduct f).primeFactors = selected f := Nat.primeFactors_prod hp
  simpa only [hpf] using h

theorem window_box_remainder {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n l h : ℕ) (hn : 1 < n) (hlh : l ≤ h) (hhn : h < n)
    (P : ι → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hnot : ∀ j p, p ∈ P j → ¬p∣n)
    (hdisj : Pairwise (fun j k => Disjoint (P j) (P k)))
    (k : ι → ℕ) (D : ℕ) (hD : 1 ≤ D)
    (hsupp : ∀ f ∈ choices P k, selectedProduct f ≤ D) :
    |(∑ u ∈ window n l h, box P (fun p => if numeratorHit n p u then 1 else 0) k) -
       windowMass n l h * box P density k| ≤ (D:ℝ)*(1+Real.log D)*n.divisors.card := by
  classical
  have hinj := choices_product_injOn P hP hdisj k
  have hsub : (choices P k).image selectedProduct ⊆ Icc 1 D := by
    intro d hd
    obtain ⟨f,hf,rfl⟩ := mem_image.mp hd
    exact mem_Icc.mpr ⟨selectedProduct_pos hP hf, hsupp f hf⟩
  unfold box
  rw [sum_block_weights, prod_truncation_eq_sum_choices, Finset.mul_sum, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ f ∈ choices P k, (2:ℝ)^(selectedProduct f).primeFactors.card * n.divisors.card := by
      apply sum_le_sum
      intro f hf
      rw [show sign f * intersectionCount (window n l h) (numeratorHit n) (selected f) -
          windowMass n l h * (sign f * ∏ j, ∏ p ∈ f j, density p) =
          sign f * (intersectionCount (window n l h) (numeratorHit n) (selected f) -
          windowMass n l h * ∏ j, ∏ p ∈ f j, density p) by ring, abs_mul, abs_sign, one_mul]
      exact window_remainder_choice n l h hn hlh hhn P hP hnot hdisj k f hf
    _ = (∑ d ∈ (choices P k).image selectedProduct, (2:ℝ)^d.primeFactors.card) * n.divisors.card := by
      rw [sum_image hinj, sum_mul]
    _ ≤ (∑ d ∈ Icc 1 D, (2:ℝ)^d.primeFactors.card)*n.divisors.card := by
      exact mul_le_mul_of_nonneg_right (sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (Conjectures.Goldbach.FareySieveRootTotal D hD) (by positivity)

theorem window_block_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n l h : ℕ) (hn : 1 < n) (hlh : l ≤ h) (hhn : h < n)
    (P : ι → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hnot : ∀ j p, p ∈ P j → ¬p∣n)
    (hdisj : Pairwise (fun j k => Disjoint (P j) (P k))) (r : ι → ℕ)
    (D : ℕ) (hD : 1 ≤ D) (hsupp : ∀ k : ι → ℕ, (∀ j, k j ≤ 2*r j+1) →
      ∀ f ∈ choices P k, selectedProduct f ≤ D)
    (e : ℝ) (hw : ∀ j p, p ∈ P j → 0 ≤ density p ∧ density p < 1)
    (htail : (∑ j, ((∑ p ∈ P j, density p) ^ (2*r j+1) / ((2*r j+1).factorial : ℝ)) /
       (∏ p ∈ P j, (1-density p))) ≤ e) :
    windowMass n l h * ((∏ j, ∏ p ∈ P j, (1-density p)) * (1-e*Real.exp e)) -
       (1+2*(Fintype.card ι:ℝ))*((D:ℝ)*(1+Real.log D)*n.divisors.card) ≤
      (((window n l h).filter (fun u => ∀ j p, p ∈ P j → ¬ numeratorHit n p u)).card:ℝ) := by
  apply le_trans (sub_le_sub_right (mul_le_mul_of_nonneg_left
    (lower_model P r density hw e htail) (by unfold windowMass; positivity)) _)
  exact lower_count _ P _ r density _ _ (fun k hk =>
    window_box_remainder n l h hn hlh hhn P hP hnot hdisj k D hD (hsupp k hk))
end
end FareyBrun
namespace FareyBrun
open Finset ErdosStraus.BrunHooley
open scoped BigOperators
noncomputable section
open scoped Classical

theorem block_survivors {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n z : ℕ) (hn : 64 ≤ n)
    (P : ι → Finset ℕ) (hcover : ∀ p, (∃ j, p∈P j) ↔ p.Prime ∧ p≤z ∧ ¬p∣n) :
    (window n ((n+2)/3) ((2*n)/3)).filter (fun u => ∀ j p, p ∈ P j → ¬ numeratorHit n p u) =
      ((Icc ((n+2)/3) ((2*n)/3)).filter
        (fun u => u.Coprime n ∧ z < (u*(n-u)).minFac)) := by
  classical
  ext u
  constructor
  · intro hu
    obtain ⟨hwin, havoid⟩ := mem_filter.mp hu
    obtain ⟨huI, hcop⟩ := mem_filter.mp hwin
    refine mem_filter.mpr ⟨huI,hcop,?_⟩
    obtain ⟨hl,hh⟩ := mem_Icc.mp huI
    have hu2 : 2 ≤ u := by omega
    have hus : 1 ≤ n-u := by omega
    have hprod : 2 ≤ u*(n-u) := by nlinarith
    let m := (u*(n-u)).minFac
    have hm : m.Prime := Nat.minFac_prime (by omega)
    have hd : m ∣ u*(n-u) := Nat.minFac_dvd _
    by_contra! hz
    have hmn : ¬ m ∣ n := by
      intro hmn
      have hmu : ¬m ∣ u := fun hdu => Nat.not_coprime_of_dvd_of_dvd hm.one_lt hdu hmn hcop
      rcases hm.dvd_mul.mp hd with hu|hnu
      · exact hmu hu
      · have : m ∣ n-(n-u) := Nat.dvd_sub hmn hnu
        exact hmu (by simpa [Nat.sub_sub_self (by omega : u≤n)] using this)
    obtain ⟨j,hj⟩ := (hcover m).mpr ⟨hm,hz,hmn⟩
    exact havoid j m hj hd
  · intro hu
    obtain ⟨huI, hc, hmin⟩ := mem_filter.mp hu
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨huI,hc⟩,?_⟩
    intro j p hp hd
    obtain ⟨hprime,hpz,_⟩ := (hcover p).mp ⟨j,hp⟩
    exact (not_lt_of_ge (Nat.minFac_le_of_dvd hprime.two_le hd |>.trans hpz)) hmin

theorem block_euler_density {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n z : ℕ) (P : ι → Finset ℕ) (hcover : ∀ p, (∃ j, p∈P j) ↔ p.Prime ∧ p≤z ∧ ¬p∣n)
    (hdisj : Pairwise (fun j k => Disjoint (P j) (P k))) :
    ∏ j, ∏ p ∈ P j, (1-density p) =
      ∏ p ∈ ((Icc 2 z).filter Nat.Prime).filter (fun p => ¬p∣n), (1-2/(p:ℝ)) := by
  classical
  have hu : univ.biUnion P = ((Icc 2 z).filter Nat.Prime).filter (fun p => ¬p∣n) := by
    ext p
    simp only [mem_biUnion, mem_univ, true_and, mem_filter, mem_Icc]
    rw [hcover]
    constructor
    · rintro ⟨hp,hz,hn⟩
      exact ⟨⟨⟨hp.two_le,hz⟩,hp⟩,hn⟩
    · rintro ⟨⟨⟨_,hz⟩,hp⟩,hn⟩
      exact ⟨hp,hz,hn⟩
  rw [←hu, prod_biUnion (fun j _ k _ h => hdisj h)]
  rfl

theorem practical_cutoff_transfer {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n z : ℕ) (hn : 64 ≤ n) (heven : Even n)
    (P : ι → Finset ℕ) (hcover : ∀ p, (∃ j, p∈P j) ↔ p.Prime ∧ p≤z ∧ ¬p∣n)
    (hdisj : Pairwise (fun j k => Disjoint (P j) (P k))) (r : ι → ℕ)
    (D : ℕ) (hD : 1 ≤ D) (hsupp : ∀ k : ι → ℕ, (∀ j, k j ≤ 2*r j+1) →
      ∀ f ∈ choices P k, selectedProduct f ≤ D)
    (e : ℝ)
    (htail : (∑ j, ((∑ p ∈ P j, density p) ^ (2*r j+1) / ((2*r j+1).factorial : ℝ)) /
       (∏ p ∈ P j, (1-density p))) ≤ e) :
    let I := Icc ((n+2)/3) ((2*n)/3)
    let V := (I.card:ℝ)*(n.totient:ℝ)/n * ∏ p ∈ ((Icc 2 z).filter Nat.Prime).filter (fun p => ¬p∣n), (1-2/(p:ℝ))
    V * (1-e*Real.exp e) - (1+2*(Fintype.card ι:ℝ))*((D:ℝ)*(1+Real.log D)*n.divisors.card) ≤
       ((I.filter (fun u => u.Coprime n ∧ z < (u*(n-u)).minFac)).card:ℝ) := by
  classical
  have hw j p (hp : p∈P j) : 0 ≤ density p ∧ density p < 1 := by
    obtain ⟨hprime,_,hnd⟩ := (hcover p).mp ⟨j,hp⟩
    have hpne : p≠2 := by rintro rfl; exact hnd (even_iff_two_dvd.mp heven)
    have hpgt : 2 < p := lt_of_le_of_ne hprime.two_le (Ne.symm hpne)
    have hpR : 2 < (p:ℝ) := by exact_mod_cast hpgt
    unfold density
    exact ⟨by positivity, (div_lt_one (by linarith)).mpr hpR⟩
  have H := window_block_lower n ((n+2)/3) ((2*n)/3) (by omega) (by omega) (by omega)
    P (fun j p hp => ((hcover p).mp ⟨j,hp⟩).1)
    (fun j p hp => ((hcover p).mp ⟨j,hp⟩).2.2) hdisj r D hD hsupp e hw htail
  rw [block_survivors n z hn P hcover, block_euler_density n z P hcover hdisj] at H
  dsimp only
  unfold windowMass at H
  rw [Nat.card_Icc]
  have hc : (2*n)/3+1-(n+2)/3 = (2*n)/3-(n+2)/3+1 := by omega
  rw [hc]
  simpa only [mul_assoc] using H

end
end FareyBrun

namespace HD8011
open Finset ErdosStraus.BrunHooley FareyBrun
open scoped BigOperators
noncomputable section
theorem finite_numerator_window (n z R : ℕ) (hn : 64 ≤ n) (heven : Even n) (e : ℝ)
    (htail : let P := primeBlocks ((z:ℝ)+1) n (z+1)
       (∑ j : Fin (z+1), ((∑ p ∈ P j, density p) ^ (2*(R+j.val)+1) /
           ((2*(R+j.val)+1).factorial : ℝ)) / (∏ p ∈ P j, (1-density p))) ≤ e) :
    let J := z+1
    let D := J^(8*(R+1))
    let I := Icc ((n+2)/3) ((2*n)/3)
    let V := (I.card:ℝ)*(n.totient:ℝ)/n * ∏ p ∈ ((Icc 2 z).filter Nat.Prime).filter (fun p => ¬p∣n), (1-2/(p:ℝ))
    V*(1-e*Real.exp e) - (1+2*(J:ℝ))*((D:ℝ)*(1+Real.log D)*n.divisors.card) ≤
       ((I.filter (fun u => u.Coprime n ∧ z < (u*(n-u)).minFac)).card:ℝ) := by
  classical
  let w : ℝ := (z:ℝ)+1
  let J := z+1
  let P := primeBlocks w n J
  let r := fun j : Fin J => R+j.val
  let D := J^(8*(R+1))
  have hw : 1 ≤ w := by dsimp [w]; linarith [Nat.cast_nonneg (α := ℝ) z]
  have hd := primeBlocks_disjoint w hw n J
  have hcov : ∀ p, (∃ j, p ∈ P j) ↔ p.Prime ∧ p≤z ∧ ¬p∣n := by
    intro p
    have hb := primeBlocks_cover w n J (terminal_scale z)
    have hiff : (∃ j, p∈P j) ↔ p∈primeSupport w n := by
      rw [←hb, mem_biUnion]
      simp [P]
    rw [hiff, mem_primeSupport]
    have hc : (p:ℝ)<w ↔ p≤z := by
      dsimp [w]
      rw [← Nat.cast_one, ← Nat.cast_add]
      exact_mod_cast (Nat.lt_succ_iff : p<z+1 ↔ p≤z)
    rw [hc]
  have hsupp (k : Fin J → ℕ) (hk : ∀ j, k j ≤ 2*r j+1) (f : Fin J → Finset ℕ)
      (hf : f∈choices P k) : selectedProduct f ≤ D := by
    have hc := rank_budget J R P hd w hw (primeBlocks_bound w n J) k hk hf
    change (selectedProduct f:ℝ) ≤ ((z:ℝ)+1)^(8*(R+1)) at hc
    change selectedProduct f ≤ (z+1)^(8*(R+1))
    exact_mod_cast hc
  have hD : 1≤D := by exact Nat.one_le_pow _ _ (Nat.zero_lt_succ z)
  have main := practical_cutoff_transfer n z hn heven P hcov hd r D hD hsupp e htail
  simpa only [Fintype.card_fin] using main

end
end HD8011

open Filter Finset FareyHD8011Estimates
open scoped Topology BigOperators

theorem Conjectures.Goldbach.FareyInitialSieveLower :
let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3); let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime; let V := fun n z : ℕ => ((I n).card:ℝ)*(n.totient:ℝ)/n * ∏ p ∈ (P z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ)); let S := fun n z : ℕ => ((I n).filter (fun u => u.Coprime n ∧ z < (u*(n-u)).minFac)).card; let Z₀ := fun n U : ℕ => ⌊(n:ℝ)^((1:ℝ)/(U:ℝ))⌋₊; let Z₂ := Nat.sqrt; ∃ U₀ : ℕ, 8 ≤ U₀ ∧ ∀ U : ℕ, U₀ ≤ U → ∃ N₀ : ℕ, 64 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n → Even n → V n (Z₀ n U) - V n (Z₂ n)/8 ≤ (S n (Z₀ n U):ℝ) := by
  classical
  obtain ⟨K,hK,hratio⟩ := cutoff_ratio
  obtain ⟨U₁,hU₁,htol⟩ := FareyTail.eventually_control 8 K (1/16) hK.le (by norm_num)
  refine ⟨max 1024 U₁, by omega, ?_⟩
  intro U hU
  have hlarge : 1024 ≤ U := by omega
  have hU8 : 8 ≤ U := by omega
  let R := U/1024
  let e : ℝ := Real.exp (5*8)/(2:ℝ)^(2*R)
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hsmall : K * (U:ℝ)^2 * (e*Real.exp e) ≤ 1/16 := htol U (by omega)
  have eventual : ∀ᶠ n : ℕ in atTop, Even n →
      mass n (initial n U) - mass n n.sqrt / 8 ≤
        (((window n).filter (fun u => u.Coprime n ∧ initial n U < (u*(n-u)).minFac)).card:ℝ) := by
    filter_upwards [hratio U hU8, terminal_domination, HD8011.bounds_eventually U hlarge,
        HD8011.absorb_rounding, eventually_ge_atTop 64] with n hrat hterm hdeg herr hn hnE
    let z := initial n U
    let J := z+1
    let D := J^(8*(R+1))
    have htail := HD8011.blockTail ((z:ℝ)+1) (by positivity) n J R hnE
    have sieved := HD8011.finite_numerator_window n z R hn hnE e htail
    have hD1 : 1 ≤ D := Nat.one_le_pow _ _ (Nat.zero_lt_succ z)
    have round := herr J D hdeg.1 hdeg.2 hD1
    have terminal := hterm hnE
    have ht0 : 0 ≤ mass n n.sqrt := (Real.rpow_nonneg (Nat.cast_nonneg n) _).trans terminal
    have emul : 0 ≤ e*Real.exp e := mul_nonneg he (Real.exp_pos _).le
    have loss : mass n z * (e*Real.exp e) ≤ mass n n.sqrt /16 := by
      calc
        _ ≤ (K*(U:ℝ)^2*mass n n.sqrt)*(e*Real.exp e) :=
          mul_le_mul_of_nonneg_right (hrat hnE) emul
        _ = mass n n.sqrt*(K*(U:ℝ)^2*(e*Real.exp e)) := by ring
        _ ≤ mass n n.sqrt*(1/16) := mul_le_mul_of_nonneg_left hsmall ht0
        _ = _ := by ring
    change mass n z*(1-e*Real.exp e) - (1+2*(J:ℝ))*((D:ℝ)*(1+Real.log D)*n.divisors.card)
      ≤ (((window n).filter (fun u => u.Coprime n ∧ z < (u*(n-u)).minFac)).card:ℝ) at sieved
    change mass n z - mass n n.sqrt/8 ≤ _
    linarith only [sieved, loss, round, terminal]
  obtain ⟨N,hN⟩ := eventually_atTop.mp eventual
  exact ⟨max N 64, le_max_right _ _, fun n hn hnE => hN n (by omega) hnE⟩

