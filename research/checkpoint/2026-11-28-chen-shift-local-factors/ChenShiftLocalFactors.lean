import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-! Local factors for the four linear forms in ChenPairAdmissibleShifts. -/
namespace Goldbach.ChenShiftLocalFactors

def admissible (n : ℕ) (h k : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ a : ℤ, ¬ (p : ℤ) ∣ a*(a+h)*((n:ℤ)-a)*((n:ℤ)-a+k)

def forbidden (p : ℕ) (n h k : ZMod p) : Finset (ZMod p) :=
  {0, -h, n, n+k}

theorem local_iff (p n : ℕ) (hp : p.Prime) (h k : ℤ) :
    (∃ a : ℤ, ¬ (p : ℤ) ∣ a*(a+h)*((n:ℤ)-a)*((n:ℤ)-a+k)) ↔
    ∃ x : ZMod p, x ∉ forbidden p n h k := by
  let : Fact p.Prime := ⟨hp⟩
  have equiv (a : ℤ) : (p : ℤ) ∣ a*(a+h)*((n:ℤ)-a)*((n:ℤ)-a+k) ↔
      (a : ZMod p) ∈ forbidden p n h k := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp only [forbidden, Finset.mem_insert, Finset.mem_singleton, mul_eq_zero]
    grind
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, fun hm => ha ((equiv a).mpr hm)⟩
  · rintro ⟨x, hx⟩
    refine ⟨(x.val : ℤ), fun hd => hx ?_⟩
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using (equiv (x.val : ℤ)).mp hd

theorem number_of_allowed (p : ℕ) [NeZero p] (n h k : ZMod p) :
    (Finset.univ \ forbidden p n h k).card = p - (forbidden p n h k).card := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, ZMod.card]

theorem exists_allowed (p : ℕ) (hp : 5 ≤ p) (n h k : ZMod p) :
    ∃ x : ZMod p, x ∉ forbidden p n h k := by
  let : NeZero p := ⟨by omega⟩
  have hc : (forbidden p n h k).card ≤ 4 := Finset.card_le_four
  have hn := number_of_allowed p n h k
  have pos : 0 < (Finset.univ \ forbidden p n h k).card := by omega
  obtain ⟨x,hx⟩ := Finset.card_pos.mp pos
  exact ⟨x,(Finset.mem_sdiff.mp hx).2⟩

theorem test_two : ∀ n h k : ZMod 2,
    (∃ x : ZMod 2, x ∉ forbidden 2 n h k) ↔ n = 0 ∧ h = 0 ∧ k = 0 := by decide

theorem test_three : ∀ n h k : ZMod 3,
    (∃ x : ZMod 3, x ∉ forbidden 3 n h k) ↔
    (if n = 0 then h = 0 ∨ h ≠ k else h ≠ n ∧ k ≠ n) := by decide

theorem criterion (n : ℕ) (h k : ℤ) :
    admissible n h k ↔
      ((n : ZMod 2) = 0 ∧ (h : ZMod 2) = 0 ∧ (k : ZMod 2) = 0) ∧
      (if (n : ZMod 3) = 0 then (h : ZMod 3) = 0 ∨ (h : ZMod 3) ≠ k
       else (h : ZMod 3) ≠ n ∧ (k : ZMod 3) ≠ n) := by
  constructor
  · intro H
    exact ⟨(test_two ..).mp ((local_iff 2 n Nat.prime_two h k).mp (H 2 Nat.prime_two)),
      (test_three ..).mp ((local_iff 3 n Nat.prime_three h k).mp (H 3 Nat.prime_three))⟩
  · rintro ⟨H₂,H₃⟩ p hp
    apply (local_iff p n hp h k).mpr
    by_cases h₂ : p = 2
    · subst p
      exact (test_two ..).mpr H₂
    by_cases h₃ : p = 3
    · subst p
      exact (test_three ..).mpr H₃
    have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
    have := hp.two_le
    exact exists_allowed p (by omega) _ _ _

/-- Normalized four-form local factor, extended by one at nonprimes. -/
noncomputable def factor (p n : ℕ) (h k : ℤ) : ℝ :=
  if p.Prime then
    ((p : ℝ) - ((forbidden p n h k).card : ℝ)) * (p : ℝ)^3 / ((p : ℝ)-1)^4
  else 1

theorem small_factor (n p : ℕ) (h k : ℤ) (ha : admissible n h k) (hp : p < 24) :
    (1:ℝ)/24 ≤ factor p n h k := by
  unfold factor
  split_ifs with hprime
  · let : NeZero p := ⟨hprime.ne_zero⟩
    obtain ⟨x,hx⟩ := (local_iff p n hprime h k).mp (ha p hprime)
    have hpos : 0 < (Finset.univ \ forbidden p n h k).card :=
      Finset.card_pos.mpr ⟨x,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hx⟩⟩
    rw [number_of_allowed] at hpos
    have hc : (forbidden p n h k).card + 1 ≤ p := by omega
    have hc' : ((forbidden p n h k).card : ℝ) + 1 ≤ p := by exact_mod_cast hc
    have h₂ : (2:ℝ) ≤ p := by exact_mod_cast hprime.two_le
    have h₂₄ : (p:ℝ) ≤ 24 := by exact_mod_cast (Nat.le_of_lt hp)
    have hh : ((p:ℝ)-1)^4 ≤ (p:ℝ)^4 := by gcongr <;> linarith
    apply (le_div_iff₀ (pow_pos (by linarith : 0 < (p:ℝ)-1) 4)).mpr
    calc
      1 / 24 * ((p:ℝ)-1)^4 ≤ 1 / 24 * (p:ℝ)^4 := by gcongr
      _ ≤ (1:ℝ) * (p:ℝ)^3 := by
        rw [pow_succ]; nlinarith [mul_le_mul_of_nonneg_left h₂₄ (by positivity : 0 ≤ (p:ℝ)^3)]
      _ ≤ _ := by gcongr; linarith
  · norm_num

theorem tail_factor (p n : ℕ) (h k : ℤ) (hp : 24 ≤ p) :
    1 - 12 / ((p:ℝ)*((p:ℝ)+1)) ≤ factor p n h k := by
  have hp' : (24:ℝ) ≤ p := by exact_mod_cast hp
  unfold factor
  split_ifs
  · have hc : ((forbidden p n h k).card : ℝ) ≤ 4 := by
      exact Nat.cast_le.mpr (Finset.card_le_four : (forbidden p n h k).card ≤ 4)
    apply (le_div_iff₀ (pow_pos (by linarith : 0 < (p:ℝ)-1) 4)).mpr
    apply le_trans _ (mul_le_mul_of_nonneg_right (sub_le_sub_left hc _) (by positivity : 0 ≤ (p:ℝ)^3))
    generalize (p:ℝ) = x at hp' ⊢
    obtain ⟨t, ht, rfl⟩ := le_iff_exists_nonneg_add.mp hp'
    field_simp
    ring_nf
    nlinarith [sq_nonneg t, pow_nonneg ht 3, pow_nonneg ht 4]
  · have : 0 ≤ 12 / ((p:ℝ)*((p:ℝ)+1)) := by positivity
    linarith

private theorem tail_step (x : ℝ) (hx : 24 ≤ x) :
    1/2 + 12/(x+1) ≤ (1/2 + 12/x)*(1-12/(x*(x+1))) := by
  have ht : 1/2 + 12/x ≤ 1 := by
    have := (div_le_iff₀ (by linarith : 0 < x)).mpr (show (12:ℝ) ≤ (1/2)*x by linarith)
    linarith
  have he : 12/x - 12/(x*(x+1)) = 12/(x+1) := by field_simp; ring
  have hh := mul_le_mul_of_nonneg_right ht (by positivity : 0 ≤ 12/(x*(x+1)))
  linarith

/-- The partial singular product has an absolute positive lower bound,
uniform in both shifts, the target and the upper prime cutoff. -/
theorem partial_product_floor (n : ℕ) (h k : ℤ) (ha : admissible n h k)
    (N : ℕ) (hN : 24 ≤ N) :
    (1/24:ℝ)^24 / 2 ≤ ∏ p ∈ Finset.range N, factor p n h k := by
  have aux (m : ℕ) : (1/24:ℝ)^24 * (1/2 + 12/(24+(m:ℝ))) ≤
      ∏ p ∈ Finset.range (24+m), factor p n h k := by
    induction m with
    | zero =>
      norm_num only [Nat.cast_zero, add_zero]
      have hprod := Finset.prod_le_prod₀ (s := Finset.range 24)
        (f := fun _ : ℕ => (1/24:ℝ)) (g := fun p => factor p n h k)
        (fun _ _ => by norm_num) (fun p hp => small_factor n p h k ha (Finset.mem_range.mp hp))
      norm_num at hprod ⊢
      exact hprod
    | succ m ih =>
      rw [← Nat.add_assoc, Finset.prod_range_succ]
      let x : ℝ := 24 + (m:ℝ)
      have hx : 24 ≤ x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) m]
      have hf := tail_factor (24+m) n h k (by omega)
      push_cast at hf ⊢
      have he : 0 ≤ 1 - 12/(x*(x+1)) := by
        apply sub_nonneg.mpr
        apply (div_le_iff₀ (by positivity : 0 < x*(x+1))).mpr
        nlinarith [sq_nonneg x]
      have hn : 0 ≤ (1/24:ℝ)^24 * (1/2 + 12/(24+(m:ℝ))) := by positivity
      have step := mul_le_mul ih hf he (hn.trans ih)
      have ht := mul_le_mul_of_nonneg_left (tail_step x hx) (by positivity : 0 ≤ (1/24:ℝ)^24)
      dsimp [x] at ht
      convert ht.trans (by simpa only [mul_assoc] using step) using 1; ring
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hN
  have hl := aux m
  have := mul_nonneg (by positivity : 0 ≤ (1/24:ℝ)^24)
    (by positivity : 0 ≤ 12/(24+(m:ℝ)))
  linarith


/-- The six pairwise differences of the four forbidden residues, up to sign. -/
def discriminant (n : ℕ) (h k : ℤ) : ℤ :=
  h * k * n * ((n:ℤ)+h) * ((n:ℤ)+k) * ((n:ℤ)+h+k)

theorem generic_factor (n p : ℕ) (h k : ℤ) (hp : p.Prime)
    (good : ¬ (p:ℤ) ∣ discriminant n h k) :
    factor p n h k = ((p:ℝ)-4)*(p:ℝ)^3/((p:ℝ)-1)^4 := by
  let : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at good
  unfold discriminant at good
  push_cast at good
  simp only [mul_eq_zero, not_or] at good
  have h1 : (0 : ZMod p) ∉ ({-(h:ZMod p), (n:ZMod p), (n:ZMod p)+k} : Finset (ZMod p)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; grind
  have h2 : -(h:ZMod p) ∉ ({(n:ZMod p), (n:ZMod p)+k} : Finset (ZMod p)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; grind
  have h3 : (n:ZMod p) ∉ ({(n:ZMod p)+k} : Finset (ZMod p)) := by
    simp only [Finset.mem_singleton]; grind
  have hc : (forbidden p n h k).card = 4 := by
    simp only [forbidden, Finset.card_insert_of_notMem h1,Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3,Finset.card_singleton]
  simp [factor,hp,hc]

theorem factor_nonneg (p n : ℕ) (h k : ℤ) : 0 ≤ factor p n h k := by
  unfold factor
  split_ifs with hp
  · let : NeZero p := ⟨hp.ne_zero⟩
    have hc := Finset.card_le_card (Finset.subset_univ (forbidden p n h k))
    rw [Finset.card_univ,ZMod.card] at hc
    have h' : ((forbidden p n h k).card : ℝ) ≤ p := Nat.cast_le.mpr hc
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr h') (by positivity)) (by positivity)
  · norm_num

/-- Convert a weighted exceptional-set estimate into an ordinary count.
The input set may vary with the shifts and the cutoff. -/
theorem exceptional_count (S : Finset ℕ) (h k : ℤ) (N : ℕ) (hN : 24 ≤ N) :
    (1/24:ℝ)^24 / 2 * ((S.filter (fun n => @decide (admissible n h k)
       (Classical.propDecidable _))).card : ℝ) ≤
      ∑ n ∈ S, ∏ p ∈ Finset.range N, factor p n h k := by
  classical
  let A := S.filter (fun n => @decide (admissible n h k) (Classical.propDecidable _))
  change _ * (A.card:ℝ) ≤ _
  calc
    _ = ∑ _n ∈ A, (1/24:ℝ)^24 / 2 := by simp [mul_comm]
    _ ≤ ∑ n ∈ A, ∏ p ∈ Finset.range N, factor p n h k := by
      apply Finset.sum_le_sum
      intro n hn
      have ha : admissible n h k := by simpa [A] using (Finset.mem_filter.mp hn).2
      exact partial_product_floor n h k ha N hN
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
      (fun n _ _ => Finset.prod_nonneg (fun p _ => factor_nonneg p n h k))


/-- An obstructed tuple has a zero factor already at 2 or 3. -/
theorem product_zero_of_obstruction (n : ℕ) (h k : ℤ) (N : ℕ) (hN : 4 ≤ N)
    (ha : ¬ admissible n h k) : ∏ p ∈ Finset.range N, factor p n h k = 0 := by
  classical
  have no : ¬ (∀ p ∈ ({2,3} : Finset ℕ), ∃ x : ZMod p, x ∉ forbidden p n h k) := by
    intro hall
    apply ha
    exact (criterion n h k).mpr ⟨(test_two ..).mp (hall 2 (by decide)),
      (test_three ..).mp (hall 3 (by decide))⟩
  push Not at no
  obtain ⟨p,hp,full⟩ := no
  have hp' : p = 2 ∨ p = 3 := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hp
  have prim : p.Prime := hp'.elim (fun e => e ▸ Nat.prime_two) (fun e => e ▸ Nat.prime_three)
  let : NeZero p := ⟨prim.ne_zero⟩
  apply Finset.prod_eq_zero (i := p) (Finset.mem_range.mpr (by omega))
  have hall := Finset.eq_univ_of_forall full
  simp [factor,prim,hall,ZMod.card]

/-- Same representation predicate (including positivity) as the frozen task. -/
def represented (n : ℕ) (h k : ℤ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n ∧ 1 < (p:ℤ)+h ∧ 1 < (q:ℤ)+k ∧
    ((p:ℤ)+h).toNat.primeFactorsList.length ≤ 2 ∧ ((q:ℤ)+k).toNat.primeFactorsList.length ≤ 2

noncomputable def failures (X : ℕ) (h k : ℤ) : Finset ℕ := by
  classical
  exact (Finset.Icc 4 X).filter (fun n => Even n ∧ ¬ represented n h k)

/-- A weighted exceptional-mass power saving is sufficient with an arbitrary
multiplicative constant and any prescribed cutoff at least 24. -/
theorem frozen_of_weighted_failures (cutoff : ℕ → ℕ) (hcut : ∀ X, 24 ≤ cutoff X)
    (hw : ∀ H : ℕ, ∃ d C : ℝ, 0 < d ∧ d < 1 ∧ 0 < C ∧ ∃ T : ℕ,
      ∀ X ≥ T, ∀ h k : ℤ, h ≠ 0 → k ≠ 0 → Even h → Even k →
        (h.natAbs : ℝ) ≤ (Real.log (X:ℝ))^H → (k.natAbs : ℝ) ≤ (Real.log (X:ℝ))^H →
        ∑ n ∈ failures X h k, ∏ p ∈ Finset.range (cutoff X), factor p n h k ≤ C*(X:ℝ)^(1-d)) :
    let ok := fun (n : ℕ) (h k : ℤ) => ∀ l : ℕ, Nat.Prime l → ∃ a : ℤ, ¬ (l : ℤ) ∣ a*(a+h)*((n : ℤ)-a)*((n : ℤ)-a+k); let good := fun (n : ℕ) (h k : ℤ) => ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n ∧ 1 < (p : ℤ)+h ∧ 1 < (q : ℤ)+k ∧ ((p : ℤ)+h).toNat.primeFactorsList.length ≤ 2 ∧ ((q : ℤ)+k).toNat.primeFactorsList.length ≤ 2; ∀ H : ℕ, ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ h k : ℤ, h ≠ 0 → k ≠ 0 → Even h → Even k → (h.natAbs : ℝ) ≤ (Real.log (X : ℝ))^H → (k.natAbs : ℝ) ≤ (Real.log (X : ℝ))^H → let bad := fun n : ℕ => Even n ∧ ok n h k ∧ ¬good n h k; ((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Icc 4 X)).card : ℝ) ≤ (X : ℝ)^(1-δ) := by
  classical
  dsimp only
  intro H
  obtain ⟨d,C,hd,hd1,hC,T,hw⟩ := hw H
  let b : ℝ := (1/24:ℝ)^24 / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hg := (tendsto_rpow_atTop (by linarith : 0 < d/2)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨U,hU⟩ := Filter.eventually_atTop.1 (hg.eventually_ge_atTop (C/b))
  refine ⟨d/2, by linarith, by linarith, max 1 (max U T), ?_⟩
  intro X hX h k hh hk heh hek hlogh hlogk
  have hX₁ : 0 < (X:ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hpow : C/b ≤ (X:ℝ)^(d/2) := hU X (by omega)
  have w := hw X (by omega) h k hh hk heh hek hlogh hlogk
  have hc := exceptional_count (failures X h k) h k (cutoff X) (hcut X)
  have heq : ((failures X h k).filter (fun n => @decide (admissible n h k)
        (Classical.propDecidable _))) =
      (Finset.Icc 4 X).filter (fun n => Even n ∧ admissible n h k ∧ ¬ represented n h k) := by
    ext n
    simp only [failures, Finset.mem_filter, decide_eq_true_eq]
    tauto
  rw [heq] at hc
  suffices hs : (((Finset.Icc 4 X).filter (fun n => Even n ∧ admissible n h k ∧ ¬ represented n h k)).card : ℝ) ≤ (X:ℝ)^(1-d/2) by
    convert hs using 1; congr 2; ext m; simp [admissible, represented]
  apply (le_of_mul_le_mul_left _ hb)
  calc
    _ ≤ C * (X:ℝ)^(1-d) := hc.trans w
    _ ≤ (b * (X:ℝ)^(d/2)) * (X:ℝ)^(1-d) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hX₁.le _)
      simpa [mul_comm] using (div_le_iff₀ hb).mp hpow
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hX₁]; congr 2; ring

end Goldbach.ChenShiftLocalFactors
#print axioms Goldbach.ChenShiftLocalFactors.criterion
#print axioms Goldbach.ChenShiftLocalFactors.partial_product_floor
#print axioms Goldbach.ChenShiftLocalFactors.generic_factor
#print axioms Goldbach.ChenShiftLocalFactors.exceptional_count
#print axioms Goldbach.ChenShiftLocalFactors.frozen_of_weighted_failures
#print axioms Goldbach.ChenShiftLocalFactors.product_zero_of_obstruction

namespace Goldbach.ChenShiftLocalFactors

/-- The prohibited residues of one shifted pair of linear forms. -/
def pairForbidden {p : ℕ} (h : ZMod p) : Finset (ZMod p) := {0,-h}

/-- The residues counted twice when the two forbidden pairs are combined. -/
def overlap {p : ℕ} (n h k : ZMod p) : Finset (ZMod p) :=
  (pairForbidden h).filter (fun a => n-a ∈ pairForbidden k)

private theorem overlap_eq_inter {p : ℕ} (n h k : ZMod p) :
    overlap n h k = pairForbidden h ∩ ({n,n+k} : Finset (ZMod p)) := by
  ext a
  simp only [overlap,pairForbidden,Finset.mem_filter,Finset.mem_inter,Finset.mem_insert,
    Finset.mem_singleton]
  grind

private theorem translated_card {p : ℕ} (n k : ZMod p) :
    ({n,n+k} : Finset (ZMod p)).card = (pairForbidden k).card := by
  by_cases hk : k = 0
  · simp [pairForbidden,hk]
  · have hn : n ≠ n+k := by grind
    simp [pairForbidden,hn,hk]

theorem complement_count_add_overlap {p : ℕ} [NeZero p] (n h k : ZMod p) :
    ((Finset.univ \ forbidden p n h k).card : ℝ) =
    p - ((pairForbidden h).card : ℝ) - ((pairForbidden k).card : ℝ) +
      ((overlap n h k).card : ℝ) := by
  have hu : pairForbidden h ∪ {n,n+k} = forbidden p n h k := by
    ext x
    simp [pairForbidden,forbidden]; tauto
  have hi := Finset.card_union_add_card_inter (pairForbidden h) ({n,n+k} : Finset (ZMod p))
  rw [hu,← overlap_eq_inter,translated_card] at hi
  have hle := Finset.card_le_card (Finset.subset_univ (forbidden p n h k))
  rw [Finset.card_univ,ZMod.card] at hle
  rw [number_of_allowed,Nat.cast_sub hle]
  have hiR := congrArg (Nat.cast : ℕ → ℝ) hi
  push_cast at hiR
  linarith


private theorem overlap_fiber {p : ℕ} (n h k : ZMod p) :
    (overlap n h k).card =
      (((pairForbidden h) ×ˢ (pairForbidden k)).filter (fun ab => ab.1+ab.2=n)).card := by
  apply Finset.card_bij' (fun a _ => (a,n-a)) (fun ab _ => ab.1)
  · intro a ha
    simp only [overlap,Finset.mem_filter] at ha
    simp [ha.1,ha.2]
  · intro ab hab
    obtain ⟨⟨ha,hb⟩,he⟩ := (show (ab.1 ∈ pairForbidden h ∧ ab.2 ∈ pairForbidden k) ∧
      ab.1+ab.2=n by simpa using hab)
    have he' : n-ab.1=ab.2 := by rw [← he]; abel
    simp [overlap,ha,hb,he']
  · intros; rfl
  · intro ab hab
    have he := (Finset.mem_filter.mp hab).2
    apply Prod.ext
    · rfl
    change n-ab.1=ab.2
    rw [← he]; abel

theorem sum_overlap {p : ℕ} [NeZero p] (h k : ZMod p) :
    ∑ n : ZMod p, (overlap n h k).card = (pairForbidden h).card * (pairForbidden k).card := by
  simp_rw [overlap_fiber]
  rw [← Finset.card_product]
  exact (Finset.card_eq_sum_card_fiberwise (f := fun ab : ZMod p × ZMod p => ab.1+ab.2)
    (fun _ _ => Finset.mem_univ _)).symm


noncomputable def residueFactor {p : ℕ} [NeZero p] (n h k : ZMod p) : ℝ :=
  (p:ℝ)^3 / ((p:ℝ)-1)^4 * ((Finset.univ \ forbidden p n h k).card : ℝ)

theorem factor_eq_residueFactor {p : ℕ} [NeZero p] (hp : p.Prime) (n : ℕ) (h k : ℤ) :
    factor p n h k = residueFactor (n:ZMod p) h k := by
  have hh := Finset.card_le_card (Finset.subset_univ (forbidden p n h k))
  rw [Finset.card_univ,ZMod.card] at hh
  simp only [factor, hp, ↓reduceIte, residueFactor,number_of_allowed,Nat.cast_sub hh]
  ring

private theorem sum_overlap_real {p : ℕ} [NeZero p] (h k : ZMod p) :
    ∑ n : ZMod p, ((overlap n h k).card:ℝ) =
      ((pairForbidden h).card:ℝ) * ((pairForbidden k).card:ℝ) := by
  exact_mod_cast sum_overlap h k

theorem sum_residueFactor {p : ℕ} [NeZero p] (h k : ZMod p) :
    ∑ n : ZMod p, residueFactor n h k =
    ((p:ℝ) - (pairForbidden h).card) * ((p:ℝ) - (pairForbidden k).card) *
      (p:ℝ)^3 / ((p:ℝ)-1)^4 := by
  simp only [residueFactor,complement_count_add_overlap,← Finset.mul_sum,Finset.sum_add_distrib,
    Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul,sum_overlap_real]
  ring

private theorem overlap_second_moment {p : ℕ} [NeZero p] (h k : ZMod p) :
    ∑ n : ZMod p, ((overlap n h k).card:ℝ)^2 ≤ 8 := by
  have ch : (pairForbidden h).card ≤ 2 := Finset.card_le_two
  have ck : (pairForbidden k).card ≤ 2 := Finset.card_le_two
  calc
    _ ≤ ∑ n : ZMod p, 2 * ((overlap n h k).card:ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      have hn : ((overlap n h k).card:ℝ) ≤ 2 := Nat.cast_le.mpr ((Finset.card_filter_le ..).trans ch)
      rw [sq]
      gcongr
    _ = 2 * (((pairForbidden h).card:ℝ) * ((pairForbidden k).card:ℝ)) := by
      rw [← Finset.mul_sum,sum_overlap_real]
    _ ≤ 2*(2*2:ℝ) := by gcongr <;> first | exact_mod_cast ch | exact_mod_cast ck
    _ = _ := by norm_num

private theorem centered_le_raw {p : ℕ} [NeZero p] (v : ZMod p → ℝ) :
    ∑ n, (v n - (∑ a, v a)/(p:ℝ))^2 ≤ ∑ n, (v n)^2 := by
  let m := (∑ a, v a)/(p:ℝ)
  have hp : (p:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hm : (p:ℝ)*m = ∑ a, v a := by dsimp [m]; field_simp
  change ∑ n, (v n-m)^2 ≤ _
  simp_rw [sub_sq]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.sum_mul,
    ←Finset.mul_sum,Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) p) (sq_nonneg m),congrArg (· * m) hm]

/-- Over one complete residue system the mean squared fluctuation of the
normalized local factor is at most 2048/p³, uniformly in both shifts. -/
theorem local_variance {p : ℕ} [NeZero p] (hp : 2 ≤ p) (h k : ZMod p) :
    (∑ n : ZMod p, (residueFactor n h k - (∑ a : ZMod p, residueFactor a h k)/(p:ℝ))^2) /
      (p:ℝ) ≤ 2048/(p:ℝ)^3 := by
  let s := (p:ℝ)^3/((p:ℝ)-1)^4
  let b := (p:ℝ) - (pairForbidden h).card - (pairForbidden k).card
  let w := fun n : ZMod p => ((overlap n h k).card:ℝ)
  have hp' : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : 0 < (p:ℝ) := by linarith
  have hv (n : ZMod p) : residueFactor n h k = s*(b+w n) := by
    rw [residueFactor,complement_count_add_overlap]
  have eqmean : (∑ a : ZMod p, residueFactor a h k)/(p:ℝ) = s*(b+(∑ a,w a)/(p:ℝ)) := by
    simp only [hv,← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,
      Finset.card_univ,ZMod.card,nsmul_eq_mul]
    field_simp
  have he (n : ZMod p) : (residueFactor n h k - (∑ a : ZMod p, residueFactor a h k)/(p:ℝ))^2 =
      s^2 * (w n - (∑ a,w a)/(p:ℝ))^2 := by rw [hv,eqmean]; ring
  have hscale : s ≤ 16/(p:ℝ) := by
    have h4 : ((p:ℝ)/2)^4 ≤ ((p:ℝ)-1)^4 := by gcongr; linarith
    dsimp [s]
    apply (div_le_div_iff₀ (pow_pos (by linarith) _) hp0).mpr
    linarith
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hc := (centered_le_raw w).trans (overlap_second_moment h k)
  simp only [he,← Finset.mul_sum]
  calc
    _ ≤ (16/(p:ℝ))^2 * 8 / (p:ℝ) := by gcongr
    _ = _ := by field_simp; ring


/-- Exact first and second moments (and any natural moment) for the actual
product of the local factors over a complete period of pairwise distinct primes. -/
theorem complete_period {ι : Type*} [Fintype ι] (q : ι → ℕ)
    (hq : ∀ i, (q i).Prime) (hcop : Pairwise fun i j => (q i).Coprime (q j))
    [∀ i, NeZero (q i)] [NeZero (∏ i,q i)] (h k : ℤ) (r : ℕ) :
    ∑ a : ZMod (∏ i,q i), (∏ i, factor (q i) a.val h k)^r =
      ∏ i, ∑ n : ZMod (q i), (residueFactor n (h:ZMod (q i)) k)^r := by
  classical
  let e := ZMod.prodEquivPi q hcop
  have he (a : ZMod (∏ i,q i)) (i : ι) : e a i = (a.val : ZMod (q i)) := by
    change ZMod.prodEquivPi q hcop a i = _
    rw [ZMod.prodEquivPi_apply]
    conv_lhs => rw [← ZMod.natCast_zmod_val a]
    simp
  calc
    _ = ∑ a : ZMod (∏ i,q i), ∏ i, (residueFactor (e a i) (h:ZMod (q i)) k)^r := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.prod_pow]
      apply congrArg (fun z : ℝ => z^r)
      apply Finset.prod_congr rfl
      intro i _
      rw [he,factor_eq_residueFactor (hq i)]
    _ = ∑ x : ∀ i,ZMod (q i), ∏ i, (residueFactor (x i) (h:ZMod (q i)) k)^r :=
      e.toEquiv.sum_comp (fun x : (∀ i,ZMod (q i)) => ∏ i,(residueFactor (x i) (h:ZMod (q i)) k)^r)
    _ = _ := (Fintype.prod_sum (fun i (z : ZMod (q i)) => (residueFactor z (h:ZMod (q i)) k)^r)).symm


private theorem block_sum (Q X : ℕ) [NeZero Q] (S : Finset ℕ) (hS : ∀ a ∈ S, a ≤ X)
    (f : ZMod Q → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ S, f (a : ZMod Q) ≤ (↑(X/Q+1):ℝ) * ∑ x : ZMod Q, f x := by
  classical
  let e := fun a : ℕ => (a/Q,(a:ZMod Q))
  have hi : Set.InjOn e S := by
    intro a _ b _ hab
    have he := congrArg Prod.fst hab
    have hm := congrArg Prod.snd hab
    change a/Q = b/Q at he
    change (a:ZMod Q) = (b:ZMod Q) at hm
    have hmod := (ZMod.natCast_eq_natCast_iff' a b Q).mp hm
    have ha := Nat.mod_add_div a Q
    rw [hmod,he,Nat.mod_add_div] at ha
    exact ha.symm
  let T := Finset.range (X/Q+1) ×ˢ (Finset.univ : Finset (ZMod Q))
  have ht : S.image e ⊆ T := by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Nat.div_le_div_right (hS a ha))),Finset.mem_univ _⟩
  calc
    _ ≤ ∑ z ∈ T, f z.2 := Finset.sum_le_sum_of_injOn e hi ht (fun _ _ => le_rfl) (fun z _ _ => hf z.2)
    _ = _ := by simp [T,Finset.sum_product]

/-- Cauchy–Schwarz for an arbitrary target set inside [0,X], with the
complete-period second moment evaluated exactly as a product. -/
theorem target_set_mass {ι : Type*} [Fintype ι] (q : ι → ℕ)
    (hq : ∀ i, (q i).Prime) (hcop : Pairwise fun i j => (q i).Coprime (q j))
    [∀ i, NeZero (q i)] [NeZero (∏ i,q i)] (h k : ℤ) (X : ℕ)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a ≤ X) :
    (∑ a ∈ S, ∏ i, factor (q i) a h k)^2 ≤ (S.card:ℝ) * (↑(X/(∏ i,q i)+1):ℝ) *
      ∏ i, ∑ n : ZMod (q i), (residueFactor n (h:ZMod (q i)) k)^2 := by
  classical
  let Q := ∏ i,q i
  let f := fun a : ZMod Q => (∏ i, factor (q i) a.val h k)^2
  have he (a : ℕ) : (∏ i, factor (q i) a h k)^2 = f (a:ZMod Q) := by
    apply congrArg (fun z : ℝ => z^2)
    apply Finset.prod_congr rfl
    intro i _
    rw [factor_eq_residueFactor (hq i),factor_eq_residueFactor (hq i)]
    apply congrArg (fun z : ZMod (q i) => residueFactor z h k)
    rw [ZMod.val_natCast]
    apply (ZMod.natCast_eq_natCast_iff' ..).mpr
    exact (Nat.mod_mod_of_dvd _ (Finset.dvd_prod_of_mem q (Finset.mem_univ i))).symm
  have hb := block_sum Q X S hS f (fun _ => sq_nonneg _)
  calc
    _ ≤ (S.card:ℝ) * ∑ a ∈ S, (∏ i, factor (q i) a h k)^2 :=
      _root_.sq_sum_le_card_mul_sum_sq
    _ = (S.card:ℝ) * ∑ a ∈ S, f (a:ZMod Q) := by
      exact congrArg ((S.card:ℝ) * ·) (Finset.sum_congr rfl (fun a _ => he a))
    _ ≤ (S.card:ℝ) * ((↑(X/Q+1):ℝ) * ∑ x : ZMod Q, f x) :=
      mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg S.card)
    _ = _ := by
      rw [← mul_assoc]
      exact congrArg ((S.card:ℝ) * (↑(X/Q+1):ℝ) * ·) (complete_period q hq hcop h k 2)

end Goldbach.ChenShiftLocalFactors
#print axioms Goldbach.ChenShiftLocalFactors.local_variance
#print axioms Goldbach.ChenShiftLocalFactors.target_set_mass

namespace Goldbach.ChenShiftLocalFactors

theorem local_moment_comparison {p : ℕ} [NeZero p] (hp : p.Prime) (h k : ZMod p) :
    (p:ℝ) * (∑ n : ZMod p, residueFactor n h k ^ 2) ≤
      (1+32768/(p:ℝ)^3) * (∑ n : ZMod p, residueFactor n h k)^2 := by
  let f := fun n : ZMod p => residueFactor n h k
  let M := (∑ n, f n)/(p:ℝ)
  have hp' : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : 0 < (p:ℝ) := by linarith
  have hm : (p:ℝ)*M = ∑ n, f n := by dsimp [M]; field_simp
  change (p:ℝ) * (∑ n, f n ^ 2) ≤ (1+32768/(p:ℝ)^3)*(∑ n, f n)^2
  by_cases hl : 5 ≤ p
  · have hp5 : (5:ℝ) ≤ p := by exact_mod_cast hl
    have hA : ((pairForbidden h).card:ℝ) ≤ 2 := Nat.cast_le.mpr Finset.card_le_two
    have hB : ((pairForbidden k).card:ℝ) ≤ 2 := Nat.cast_le.mpr Finset.card_le_two
    have hge : (1:ℝ)/4 ≤ M := by
      dsimp only [M,f]
      rw [sum_residueFactor]
      apply (le_div_iff₀ hp0).mpr
      apply (le_div_iff₀ (pow_pos (by linarith) _)).mpr
      have h₁ : ((p:ℝ)-1)^4 ≤ (p:ℝ)^4 := by gcongr <;> linarith
      have h₂ : ((p:ℝ)/2)*((p:ℝ)/2) ≤ ((p:ℝ)-(pairForbidden h).card)*((p:ℝ)-(pairForbidden k).card) := by
        gcongr <;> linarith
      calc
        _ ≤ (1/4*(p:ℝ))*(p:ℝ)^4 := by gcongr
        _ = ((p:ℝ)/2*((p:ℝ)/2))*(p:ℝ)^3 := by ring
        _ ≤ _ := by gcongr
    have hv := local_variance hp.two_le h k
    change (∑ n, (f n-M)^2)/(p:ℝ) ≤ _ at hv
    have hg : 1 ≤ 16*M^2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ M-1/4) (by linarith : 0 ≤ M+1/4)]
    have hr : (∑ n, (f n-M)^2) ≤ (32768/(p:ℝ)^3 * M^2) * p := by
      apply (div_le_iff₀ hp0).mp
      apply hv.trans
      have haux := mul_le_mul_of_nonneg_left hg (by positivity : 0 ≤ 2048/(p:ℝ)^3)
      calc
        _ = (2048/(p:ℝ)^3)*1 := by ring
        _ ≤ _ := haux
        _ = _ := by ring
    have hid : (∑ n, (f n-M)^2) = (∑ n, f n ^ 2) - (p:ℝ)*M^2 := by
      simp_rw [sub_sq]
      simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_mul,← Finset.mul_sum,
        Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul,← hm]
      ring
    rw [hid] at hr
    rw [← hm]
    nlinarith [mul_le_mul_of_nonneg_left hr hp0.le]
  · have hnonneg (n : ZMod p) : 0 ≤ f n := by dsimp [f,residueFactor]; positivity
    have he := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (fun i _ => hnonneg i)
    have hp3 : p = 2 ∨ p = 3 := by
      have := hp.two_le
      have hn : p ≠ 4 := by rintro rfl; norm_num at hp
      omega
    have hpB : (p:ℝ) ≤ 1+32768/(p:ℝ)^3 := by rcases hp3 with rfl|rfl <;> norm_num
    exact mul_le_mul hpB he (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)


/-- A single constant works for every squarefree period and both shifts. -/
noncomputable def momentConstant : ℝ := Real.exp (32768 * ∑' m : ℕ, 1/(m:ℝ)^3)

private theorem relative_product_bound {ι : Type*} [Fintype ι] (q : ι → ℕ)
    (hi : Function.Injective q) :
    ∏ i, (1+32768/(q i:ℝ)^3) ≤ momentConstant := by
  classical
  have hsum : ∑ i, (1/(q i:ℝ)^3) ≤ ∑' m : ℕ, 1/(m:ℝ)^3 := by
    have summ := Real.summable_one_div_nat_pow.mpr (by decide : 1 < 3)
    have hh := summ.sum_le_tsum (Finset.univ.image q) (fun i _ => by positivity)
    rwa [Finset.sum_image hi.injOn] at hh
  calc
    _ ≤ ∏ i, Real.exp (32768 / (q i:ℝ)^3) := Finset.prod_le_prod₀
      (fun i _ => by positivity) (fun i _ => by simpa only [add_comm] using Real.add_one_le_exp (32768/(q i:ℝ)^3))
    _ = Real.exp (32768 * ∑ i, 1/(q i:ℝ)^3) := by
      rw [← Real.exp_sum, Finset.mul_sum]; simp [div_eq_mul_inv]
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum (by norm_num))

theorem wheel_second_moment {ι : Type*} [Fintype ι] (q : ι → ℕ)
    (hq : ∀ i, (q i).Prime) (hcop : Pairwise fun i j => (q i).Coprime (q j))
    [∀ i, NeZero (q i)] [NeZero (∏ i,q i)] (h k : ℤ) :
    ((∏ i,q i : ℕ):ℝ) * (∑ a : ZMod (∏ i,q i), (∏ i, factor (q i) a.val h k)^2) ≤
      momentConstant * (∑ a : ZMod (∏ i,q i), ∏ i, factor (q i) a.val h k)^2 := by
  classical
  have hinj : Function.Injective q := by
    intro i j he
    by_contra hn
    have hh := hcop hn
    change (q i).Coprime (q j) at hh
    rw [he,Nat.coprime_self] at hh
    exact (hq j).ne_one hh
  have hfirst := complete_period q hq hcop h k 1
  simp only [pow_one] at hfirst
  rw [complete_period q hq hcop h k 2,hfirst,Nat.cast_prod,← Finset.prod_mul_distrib]
  calc
    _ ≤ ∏ i, ((1+32768/(q i:ℝ)^3) * (∑ n : ZMod (q i), residueFactor n (h:ZMod (q i)) k)^2) :=
      Finset.prod_le_prod₀ (fun i _ => mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
        (fun i _ => local_moment_comparison (hq i) _ _)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_right (relative_product_bound q hinj) (sq_nonneg _)

end Goldbach.ChenShiftLocalFactors
#print axioms Goldbach.ChenShiftLocalFactors.wheel_second_moment

namespace Goldbach.ChenShiftLocalFactors

noncomputable def pairMean (p : ℕ) (h : ℤ) : ℝ :=
  if (p:ℤ) ∣ h then (p:ℝ)/((p:ℝ)-1) else 1-1/((p:ℝ)-1)^2

private theorem pairMean_formula {p : ℕ} (hp : p.Prime) (h : ℤ) :
    pairMean p h = (p:ℝ)*((p:ℝ)-(pairForbidden (h:ZMod p)).card)/((p:ℝ)-1)^2 := by
  have hpos : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  by_cases hd : (p:ℤ) ∣ h
  · have hzero := (ZMod.intCast_zmod_eq_zero_iff_dvd h p).mpr hd
    simp [pairMean,hd,hzero,pairForbidden]
    field_simp
  · have hn : (h : ZMod p) ≠ 0 := fun he => hd ((ZMod.intCast_zmod_eq_zero_iff_dvd h p).mp he)
    simp [pairMean,hd,pairForbidden,hn]
    field_simp; ring

private theorem pairMean_nonneg {p : ℕ} (hp : p.Prime) (h : ℤ) : 0 ≤ pairMean p h := by
  rw [pairMean_formula hp]
  have hc : (pairForbidden (h : ZMod p)).card ≤ 2 := Finset.card_le_two
  have hc' : ((pairForbidden (h : ZMod p)).card:ℝ) ≤ p := Nat.cast_le.mpr (hc.trans hp.two_le)
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hc')) (by positivity)

theorem prime_first_moment {p : ℕ} [NeZero p] (hp : p.Prime) (h k : ℤ) :
    (∑ n : ZMod p, residueFactor n (h:ZMod p) k) = p * (pairMean p h * pairMean p k) := by
  rw [sum_residueFactor,pairMean_formula hp,pairMean_formula hp]
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  field_simp

private theorem totient_height (m : ℕ) (hm : m ≠ 0) :
    (∏ p ∈ m.primeFactors, (p:ℝ)/((p:ℝ)-1)) = (m:ℝ)/m.totient := by
  have hpos := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm)
  have hd : 0 < ∏ p ∈ m.primeFactors, ((p:ℝ)-1) := by
    apply Finset.prod_pos
    intro p hp
    have := Nat.Prime.one_lt (Nat.prime_of_mem_primeFactors hp)
    exact sub_pos.mpr (by exact_mod_cast this)
  rw [Finset.prod_div_distrib]
  apply (div_eq_div_iff hd.ne' (by exact_mod_cast hpos.ne')).mpr
  have he := congrArg (Nat.cast : ℕ → ℝ) (Nat.totient_mul_prod_primeFactors m)
  push_cast at he
  rw [mul_comm]
  convert he using 2
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (Nat.one_le_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt)]
  simp

private theorem prod_pairMean_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (h : ℤ) (hh : h ≠ 0) :
    ∏ p ∈ P, pairMean p h ≤ (h.natAbs:ℝ)/h.natAbs.totient := by
  classical
  let S := P.filter (fun p : ℕ => (p:ℤ) ∣ h)
  have hS : S ⊆ h.natAbs.primeFactors := by
    intro p hp
    obtain ⟨hpm,hd⟩ := Finset.mem_filter.mp hp
    apply Nat.mem_primeFactors.mpr
    exact ⟨hP p hpm, Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hd), by simpa using hh⟩
  calc
    _ ≤ ∏ p ∈ P, (if (p:ℤ) ∣ h then (p:ℝ)/((p:ℝ)-1) else 1) := by
      apply Finset.prod_le_prod₀ (fun p hp => pairMean_nonneg (hP p hp) h)
      intro p hp
      unfold pairMean
      split_ifs <;> first | exact le_rfl | exact sub_le_self _ (by positivity)
    _ = ∏ p ∈ S, (p:ℝ)/((p:ℝ)-1) := by simp [S,Finset.prod_ite]
    _ ≤ ∏ p ∈ h.natAbs.primeFactors, (p:ℝ)/((p:ℝ)-1) := by
      apply Finset.prod_le_prod_of_subset_of_one_le₀ hS
      · intro p hp
        have hp' : (1:ℝ)<p := by exact_mod_cast (Nat.prime_of_mem_primeFactors (hS hp)).one_lt
        exact div_nonneg (Nat.cast_nonneg _) (by linarith)
      · intro p hp _
        have hp' : (1:ℝ)<p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
        apply (le_div_iff₀ (by linarith)).mpr
        linarith
    _ = _ := totient_height _ (by simpa using hh)


/-- Uniform incomplete-interval bound for the weight on any set of targets.
Q is the squarefree period. The shift dependence only uses the two totients. -/
theorem interval_weight_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (h k : ℤ) (hh : h ≠ 0) (hk : k ≠ 0)
    (X : ℕ) (S : Finset ℕ) (hS : ∀ n ∈ S, n ≤ X) :
    (∑ n ∈ S, ∏ p ∈ P, factor p n h k)^2 ≤
      momentConstant * (S.card:ℝ) * (X + ((∏ p ∈ P,p : ℕ):ℝ)) *
        (((h.natAbs:ℝ)/h.natAbs.totient) * ((k.natAbs:ℝ)/k.natAbs.totient))^2 := by
  classical
  let q : P → ℕ := fun p => p.val
  let Q := ∏ i, q i
  have prime (i : P) : (q i).Prime := hP i i.property
  let : ∀ i, NeZero (q i) := fun i => ⟨(prime i).ne_zero⟩
  let : NeZero (∏ i,q i) := ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => (prime i).ne_zero)⟩
  have cop : Pairwise fun i j => (q i).Coprime (q j) :=
    fun i j hn => (Nat.coprime_primes (prime i) (prime j)).mpr (fun e => hn (Subtype.ext e))
  have Qpos : (0:ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (∏ i,q i))
  have hQ : Q = ∏ p ∈ P,p := Finset.prod_coe_sort P id
  let W := fun a : ZMod Q => ∏ i, factor (q i) a.val h k
  let D := ((h.natAbs:ℝ)/h.natAbs.totient) * ((k.natAbs:ℝ)/k.natAbs.totient)
  have hmean : (∑ a, W a) ≤ (Q:ℝ)*D := by
    have he := complete_period q prime cop h k 1
    simp only [pow_one] at he
    dsimp only [W]
    rw [he]
    simp_rw [prime_first_moment (prime _)]
    rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,← Nat.cast_prod]
    apply mul_le_mul_of_nonneg_left _ Qpos.le
    change (∏ i : P, pairMean i.val h) * (∏ i : P, pairMean i.val k) ≤ D
    rw [Finset.prod_coe_sort P (fun p => pairMean p h),Finset.prod_coe_sort P (fun p => pairMean p k)]
    exact mul_le_mul (prod_pairMean_le P hP h hh) (prod_pairMean_le P hP k hk)
      (Finset.prod_nonneg (fun i hi => pairMean_nonneg (hP i hi) k)) (by positivity)
  have hnn : 0 ≤ ∑ a, W a := Finset.sum_nonneg (fun a _ => Finset.prod_nonneg (fun i _ => factor_nonneg ..))
  have hs := wheel_second_moment q prime cop h k
  change (Q:ℝ) * (∑ a, W a^2) ≤ momentConstant * (∑ a, W a)^2 at hs
  have hC : 0 ≤ momentConstant := (Real.exp_pos _).le
  have hx : (∑ a, W a^2) ≤ momentConstant * (Q:ℝ) * D^2 := by
    apply le_of_mul_le_mul_left _ Qpos
    calc
      _ ≤ _ := hs
      _ ≤ momentConstant * ((Q:ℝ)*D)^2 := by gcongr
      _ = _ := by ring
  have hcount : (↑(X/Q+1):ℝ)*(Q:ℝ) ≤ (X:ℝ)+Q := by
    exact_mod_cast (show (X/Q+1)*Q ≤ X+Q by rw [Nat.add_mul,one_mul]; exact Nat.add_le_add_right (Nat.div_mul_le_self X Q) Q)
  have ht := target_set_mass q prime cop h k X S hS
  rw [← complete_period q prime cop h k 2] at ht
  have rewriteW (n : ℕ) : ∏ i, factor (q i) n h k = ∏ p ∈ P, factor p n h k :=
    Finset.prod_coe_sort P (fun p => factor p n h k)
  change (∑ n ∈ S, ∏ i, factor (q i) n h k)^2 ≤ (S.card:ℝ)*(↑(X/Q+1):ℝ)*(∑ a,W a^2) at ht
  rw [← hQ]
  calc
    _ = (∑ n ∈ S, ∏ i, factor (q i) n h k)^2 := by simp_rw [rewriteW]
    _ ≤ _ := ht
    _ ≤ (S.card:ℝ)*(↑(X/Q+1):ℝ)*(momentConstant*(Q:ℝ)*D^2) :=
      mul_le_mul_of_nonneg_left hx (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ = momentConstant * S.card * ((↑(X/Q+1):ℝ)*(Q:ℝ))*D^2 := by ring
    _ ≤ _ := by change _ ≤ momentConstant * S.card * ((X:ℝ)+Q)*D^2; gcongr

end Goldbach.ChenShiftLocalFactors
#print axioms Goldbach.ChenShiftLocalFactors.interval_weight_bound
