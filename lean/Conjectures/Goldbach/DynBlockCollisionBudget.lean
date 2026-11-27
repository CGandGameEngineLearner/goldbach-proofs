import Mathlib
import Conjectures.Goldbach.DynShiftFactorMean

/-!
The witness-pair count is adapted from `Goldbach.ShortComb.energy` in
`BinaryShiftShortMixedEnergy`. The prime-counting bound is adapted from
`GbSecond.card_P_le` in `DynPathSecondMoment` (goldbach-proofs, Apache-2.0).
The shifted-pair sieve in `DynShiftFactorMean` is uniform in the left endpoint.
We apply it after translating the block by the larger of the two small primes.
-/

namespace Goldbach.LocalCollision
open Finset

private def P (X : ℕ) := (Icc X.sqrt (2*X.sqrt)).filter Nat.Prime
private def W (X : ℕ) := X.sqrt * X.sqrt.sqrt
private def B (X y : ℕ) := ((Icc X (2*X)).filter Even).filter (fun n => y ≤ n ∧ n < y+W X)
private def hit (n p : ℕ) := p ≤ n ∧ Nat.Prime (n-p)
private instance (n : ℕ) : DecidablePred (hit n) := fun p => inferInstanceAs (Decidable (p ≤ n ∧ Nat.Prime (n-p)))
private noncomputable def S (d : ℕ) : ℝ :=
  ∏ l ∈ d.primeFactors.filter (fun l => 2 < l), (((l:ℝ)-1)/((l:ℝ)-2))

private def increasing (I : Finset ℕ) := (I ×ˢ I).filter (fun u => u.1 < u.2)

private theorem energy (M I : Finset ℕ) (p : ℕ → ℕ → Prop) [∀ m, DecidablePred (p m)] :
    (∑ m ∈ M, ((I.filter (p m)).card)^2) ≤ M.card + 4 * ∑ u ∈ increasing I,
      (M.filter (fun m => p m u.1 ∧ p m u.2)).card := by
  classical
  let b := fun u : ℕ × ℕ => fun m => if p m u.1 ∧ p m u.2 then 1 else 0
  have pt (m : ℕ) : ((I.filter (p m)).card)^2 ≤ 1+4*(∑ u ∈ increasing I, b u m) := by
    let s := I.filter (p m)
    have he : (increasing I).filter (fun u => p m u.1 ∧ p m u.2) = increasing s := by
      ext u; simp [increasing,s]; tauto
    have hh : (∑ u ∈ increasing I, b u m) = s.card.choose 2 := by
      simp only [b,← sum_filter,sum_const,smul_eq_mul,mul_one,he]
      exact card_product_filter_lt
    rw [hh]
    change s.card^2 ≤ 1+4*s.card.choose 2
    have hmul : s.card.choose 2 * 2 = s.card*(s.card-1) := by
      have hn := Nat.descFactorial_eq_factorial_mul_choose s.card 2
      simpa [Nat.descFactorial_succ,Nat.factorial_succ,mul_comm,mul_left_comm] using hn.symm
    rcases Nat.eq_zero_or_pos s.card with hz | hz
    · simp [hz]
    · have h1 : s.card-1+1=s.card := by omega
      nlinarith only [hmul,h1,Nat.zero_le ((s.card-1)*(s.card-1))]
  calc _ ≤ ∑ m ∈ M, (1+4*(∑ u ∈ increasing I, b u m)) := sum_le_sum (fun m _ => pt m)
       _ = _ := by
         rw [sum_add_distrib, ← mul_sum, sum_comm]
         simp [b]

private theorem card_P_le : ∃ C3 : ℝ, 0 < C3 ∧ ∃ X0 : ℕ, ∀ X ≥ X0,
    ((P X).card : ℝ) ≤ C3 * Real.sqrt (X:ℝ) / Real.log (X:ℝ) := by
  have ev := Chebyshev.eventually_primeCounting_le (ε := 1) one_pos
  have ht : Filter.Tendsto (fun X : ℕ => 2 * Real.sqrt (X:ℝ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num)
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have ev2 := ht.eventually ev
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.1 (ev2.and (Filter.eventually_ge_atTop 2))
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨4 * (Real.log 4 + 1), by positivity, X0, fun X hX => ?_⟩
  obtain ⟨hpi, hX2⟩ := hX0 X hX
  have hXr : (2:ℝ) ≤ X := by exact_mod_cast hX2
  have hL : 0 < Real.log (X:ℝ) := Real.log_pos (by linarith)
  have hs : 0 < Real.sqrt (X:ℝ) := Real.sqrt_pos.2 (by linarith)
  have hcard : (P X).card ≤ Nat.primeCounting (2 * Nat.sqrt X) := by
    have hsub : P X ⊆ (2 * Nat.sqrt X + 1).primesBelow := by
      intro x hx
      simp only [P, Finset.mem_filter, Finset.mem_Icc] at hx
      rw [Nat.mem_primesBelow]
      exact ⟨by omega, hx.2⟩
    calc (P X).card ≤ (2 * Nat.sqrt X + 1).primesBelow.card := Finset.card_le_card hsub
      _ = Nat.primeCounting (2 * Nat.sqrt X) := Nat.primesBelow_card_eq_primeCounting' _
  have hmono : Nat.primeCounting (2 * Nat.sqrt X) ≤ Nat.primeCounting ⌊2 * Real.sqrt (X:ℝ)⌋₊ := by
    apply Nat.monotone_primeCounting
    apply Nat.le_floor
    have := Real.nat_sqrt_le_real_sqrt (a := X)
    push_cast
    linarith
  have h1 : ((P X).card : ℝ) ≤ (Real.log 4 + 1) * (2 * Real.sqrt (X:ℝ)) /
      Real.log (2 * Real.sqrt (X:ℝ)) :=
    le_trans (by exact_mod_cast hcard.trans hmono) hpi
  have hlog : Real.log (X:ℝ) / 2 ≤ Real.log (2 * Real.sqrt (X:ℝ)) := by
    rw [Real.log_mul (by norm_num) hs.ne', ← Real.log_sqrt (by linarith)]
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  have h2 : (Real.log 4 + 1) * (2 * Real.sqrt (X:ℝ)) / Real.log (2 * Real.sqrt (X:ℝ))
      ≤ (Real.log 4 + 1) * (2 * Real.sqrt (X:ℝ)) / (Real.log (X:ℝ) / 2) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hlog
  refine h1.trans (h2.trans (le_of_eq ?_))
  field_simp
  norm_num

private theorem block_card (X y : ℕ) : (B X y).card ≤ W X := by
  have sub : B X y ⊆ Ico y (y+W X) := fun _ h => mem_Ico.mpr (mem_filter.mp h).2
  simpa using card_le_card sub

private theorem width_bounds {X : ℕ} (hs : 3 ≤ X.sqrt) :
    X.sqrt ≤ W X ∧ X ≤ (W X)^4 := by
  have hroot : 1 ≤ X.sqrt.sqrt := Nat.le_sqrt.mpr (by omega)
  have hw : X.sqrt ≤ W X := by
    simpa only [W, mul_one] using Nat.mul_le_mul_left X.sqrt hroot
  refine ⟨hw, ?_⟩
  have hsq : X.sqrt + 1 ≤ X.sqrt^2 := by nlinarith
  calc X ≤ (X.sqrt + 1)^2 := (Nat.lt_succ_sqrt' X).le
       _ ≤ (X.sqrt^2)^2 := Nat.pow_le_pow_left hsq 2
       _ = X.sqrt^4 := by ring
       _ ≤ (W X)^4 := Nat.pow_le_pow_left hw 4

/-- Translate a common endpoint n to the prime n-q. The window width stays W X. -/
private theorem common_le {X y p q : ℕ} (hq : q ≤ y) (hpq : p < q) :
    ((B X y).filter (fun n => hit n p ∧ hit n q)).card ≤
    ((Icc (y-q) (y-q+W X)).filter (fun t => t.Prime ∧ (t+(q-p)).Prime)).card := by
  apply card_le_card_of_injOn (fun n => n-q)
  · intro n hn
    rcases mem_filter.mp hn with ⟨hn, hp, hq'⟩
    have hwin := (mem_filter.mp hn).2
    rcases hp with ⟨_, hnp⟩
    rcases hq' with ⟨_, hnq⟩
    change n-q ∈ _
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hnq, by simpa only [show n-q+(q-p)=n-p by omega] using hnp⟩
  · intro n hn k hk he
    have hnq := ((mem_filter.mp hn).2.2).1
    have hkq := ((mem_filter.mp hk).2.2).1
    dsimp at he
    omega

private theorem pair_sum (X : ℕ) :
    (∑ u ∈ increasing (P X), S (u.2-u.1)) =
    ∑ p ∈ P X, ∑ q ∈ (P X).filter (fun q => p<q), S (q-p) := by
  simp only [increasing, sum_filter, sum_product]

private theorem log_allowance (X : ℕ) :
    (Real.log X)^2 ≤ 16 * Real.sqrt X := by
  have hx₀ : (0:ℝ) ≤ X := Nat.cast_nonneg _
  have hlog := Real.log_le_rpow_div hx₀ (by norm_num : (0:ℝ) < 1/4)
  have hlog' : Real.log X ≤ 4 * (X:ℝ)^(1/4:ℝ) := by linarith
  have hnn : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  calc (Real.log X)^2 ≤ (4 * (X:ℝ)^(1/4:ℝ))^2 := pow_le_pow_left₀ hnn hlog' 2
       _ = 16 * Real.sqrt X := by
         rw [mul_pow, ← Real.rpow_mul_natCast hx₀, Real.sqrt_eq_rpow]
         norm_num

theorem _root_.Conjectures.Goldbach.DynBlockCollisionBudget :
    let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime; let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card; let W := fun X : ℕ => Nat.sqrt X * Nat.sqrt (Nat.sqrt X); let B := fun (X y : ℕ) => (E X).filter (fun n => y ≤ n ∧ n < y + W X); let M := fun X : ℕ => Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2; ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y + W X ≤ 2*X → (∑ n ∈ B X y, (H X n:ℝ)^2) ≤ C*(W X:ℝ)*(M X)^2 := by
  change ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ X ≥ N, ∀ y : ℕ, X ≤ y → y+W X ≤ 2*X →
    (∑ n ∈ B X y, (((P X).filter (hit n)).card:ℝ)^2) ≤
      C*(W X:ℝ)*(Real.sqrt X/(Real.log X)^2)^2
  obtain ⟨K,hK,Z,hpair⟩ := shifted_pair_upper
  obtain ⟨D,hD,N₁,hmean⟩ := Conjectures.Goldbach.DynShiftFactorMean
  obtain ⟨F,hF,N₂,hcard⟩ := card_P_le
  refine ⟨256 + 64*K*D*F^2, by positivity, ?_⟩
  apply Filter.eventually_atTop.mp
  filter_upwards [Filter.eventually_ge_atTop ((max Z 3)^2), Filter.eventually_ge_atTop N₁,
      Filter.eventually_ge_atTop N₂] with X hbase h₁ h₂
  intro y hxy _
  have hs := Nat.le_sqrt'.mpr hbase
  have hs₃ : 3 ≤ X.sqrt := (le_max_right ..).trans hs
  have hsmall : 2*X.sqrt ≤ X := by have := Nat.sqrt_le' X; nlinarith
  obtain ⟨hsw,hxpow⟩ := width_bounds hs₃
  have hWZ : Z ≤ W X := (le_max_left ..).trans (hs.trans hsw)
  have hxlarge : 1 < X := by omega
  have hwlarge : 1 < W X := by omega
  let L := Real.log (X:ℝ)
  let R := Real.sqrt (X:ℝ)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hxlarge)
  have hLW : 0 < Real.log (W X:ℝ) := Real.log_pos (by exact_mod_cast hwlarge)
  have hlog : L ≤ 4*Real.log (W X:ℝ) := by
    have h := Real.log_le_log (by positivity : (0:ℝ) < X) (by exact_mod_cast hxpow : (X:ℝ) ≤ (W X:ℝ)^4)
    simpa [L,Real.log_pow] using h
  have hslope : L^2 ≤ 16 * (Real.log (W X:ℝ))^2 := by
    calc L^2 ≤ (4*Real.log (W X:ℝ))^2 := pow_le_pow_left₀ hL.le hlog 2
         _ = _ := by ring
  let T := B X y
  let hits := fun (u : ℕ × ℕ) => (T.filter (fun n => hit n u.1 ∧ hit n u.2)).card
  have per (u : ℕ × ℕ) (hu : u ∈ increasing (P X)) :
      (hits u:ℝ) ≤ (16*K*(W X:ℝ)/L^2) * S (u.2-u.1) := by
    rcases u with ⟨p,q⟩
    obtain ⟨hpp,hpq⟩ := mem_filter.mp hu
    obtain ⟨hp,hq⟩ := mem_product.mp hpp
    obtain ⟨hpI,hpr⟩ := mem_filter.mp hp
    obtain ⟨hqI,hqr⟩ := mem_filter.mp hq
    obtain ⟨hpmin,hpmax⟩ := mem_Icc.mp hpI
    obtain ⟨hqmin,hqmax⟩ := mem_Icc.mp hqI
    change p < q at hpq
    have hg : Even (q-p) := by
      obtain ⟨a,ha⟩ := hpr.odd_of_ne_two (by omega)
      obtain ⟨b,hb⟩ := hqr.odd_of_ne_two (by omega)
      exact ⟨b-a, by omega⟩
    have hb := hpair (W X) hWZ (y-q) (q-p) (by omega) hg (by omega)
    have hj : ((hits (p,q)):ℝ) ≤ K*(W X:ℝ)*S (q-p)/(Real.log (W X:ℝ))^2 :=
      (by exact_mod_cast common_le (X:=X) (y:=y) (q:=q) (by omega) hpq : (hits (p,q):ℝ) ≤ _).trans hb
    have hj' := (le_div_iff₀ (sq_pos_of_pos hLW)).mp hj
    have hmul := mul_le_mul_of_nonneg_left hslope (Nat.cast_nonneg (α:=ℝ) (hits (p,q)))
    change (hits (p,q):ℝ) ≤ (16*K*(W X:ℝ)/L^2) * S (q-p)
    rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hL)]
    linarith only [hmul,hj']
  have hfactor : (∑ u ∈ increasing (P X), S (u.2-u.1)) ≤ D*((P X).card:ℝ)^2 :=
    (pair_sum X).le.trans (hmean X h₁)
  have hcount := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) (P X).card) (hcard X h₂) 2
  have hoff : (∑ u ∈ increasing (P X), (hits u:ℝ)) ≤
      (16*K*D*F^2)*(W X:ℝ)*(R/L^2)^2 := by
    calc _ ≤ ∑ u ∈ increasing (P X), (16*K*(W X:ℝ)/L^2)*S (u.2-u.1) := sum_le_sum per
         _ = _ := (mul_sum ..).symm
         _ ≤ (16*K*(W X:ℝ)/L^2)*(D*((P X).card:ℝ)^2) := by gcongr
         _ ≤ (16*K*(W X:ℝ)/L^2)*(D*(F*R/L)^2) := by gcongr
         _ = _ := by ring
  have hM : 1 ≤ 16*(R/L^2) := by
    rw [← mul_div_assoc, le_div_iff₀ (sq_pos_of_pos hL), one_mul]
    exact log_allowance X
  have hone : (1:ℝ) ≤ 256*(R/L^2)^2 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hM 2
    nlinarith only [this]
  have hdiag : (T.card:ℝ) ≤ 256*(W X:ℝ)*(R/L^2)^2 := by
    calc (T.card:ℝ) ≤ (W X:ℝ) := by exact_mod_cast block_card X y
         _ = (W X:ℝ)*1 := (mul_one _).symm
         _ ≤ (W X:ℝ)*(256*(R/L^2)^2) := by gcongr
         _ = _ := by ring
  have he : (∑ n ∈ T, (((P X).filter (hit n)).card:ℝ)^2) ≤
      (T.card:ℝ) + 4 * ∑ u ∈ increasing (P X), (hits u:ℝ) := by
    exact_mod_cast energy T (P X) hit
  change _ ≤ (256 + 64*K*D*F^2)*(W X:ℝ)*(R/L^2)^2
  linarith only [he,hdiag,hoff]

end Goldbach.LocalCollision
