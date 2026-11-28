import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Card
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
