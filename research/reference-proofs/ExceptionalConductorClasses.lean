import Mathlib

/-! The exceptional conductor profiles in §2, equations (2.26)–(2.31), of
Pintz, arXiv:1804.09084. The divisibility argument is finite and independent
of how the primitive conductors and their zeros are produced. -/

namespace Conjectures.Goldbach.ExceptionalConductorClasses

open Finset Filter
open scoped BigOperators Topology

def profile (R : Finset ℕ) (C m : ℕ) := R.filter (fun r => r ∣ C*m)
def modulus (S : Finset ℕ) : ℕ := S.lcm id
def moduli (R : Finset ℕ) := R.powerset.image modulus
noncomputable def bad (R : Finset ℕ) (C N : ℕ) (T : ℝ) :=
  (Ioc 0 N).filter (fun m => T < (modulus (profile R C m) : ℝ))

private theorem cancel_common (q C m : ℕ) (hq : 0 < q) :
    q ∣ C*m ↔ q/(q.gcd C) ∣ m := by
  let g := q.gcd C
  have hg : 0 < g := Nat.gcd_pos_of_pos_left C hq
  have hl : (q/g)*g=q := Nat.div_mul_cancel (Nat.gcd_dvd_left q C)
  have hr : (C/g)*g=C := Nat.div_mul_cancel (Nat.gcd_dvd_right q C)
  have he : ((C/g)*m)*g=C*m := by rw [Nat.mul_right_comm, hr]
  calc
    q ∣ C*m ↔ (q/g)*g ∣ ((C/g)*m)*g := by rw [hl,he]
    _ ↔ (q/g) ∣ (C/g)*m := Nat.mul_dvd_mul_iff_right hg
    _ ↔ _ := (Nat.coprime_div_gcd_div_gcd hg).dvd_mul_left

/-- Exact number of positive multiples after cancelling the common
part of a modulus with the integer attached to the target. -/
theorem multiples (q C N : ℕ) (hq : 0 < q) :
    ((Ioc 0 N).filter (fun m => q ∣ C*m)).card = N/(q/(q.gcd C)) := by
  simp_rw [cancel_common q C _ hq]
  exact Nat.Ioc_filter_dvd_card_eq_div N _

/-- Every target is divisible, after multiplication by C, by the least
common multiple of precisely the exceptional conductors it sees. -/
theorem profile_dvd (R : Finset ℕ) (C m : ℕ) :
    modulus (profile R C m) ∣ C*m := Finset.lcm_dvd (fun _ h => (mem_filter.mp h).2)

private theorem count_one {q C N : ℕ} (hq : 0 < q) (hC : 0 < C) :
    q*((Ioc 0 N).filter (fun m => q ∣ C*m)).card ≤ C*N := by
  rw [multiples q C N hq]
  let g := q.gcd C
  have hq' : (q/g)*g=q := Nat.div_mul_cancel (Nat.gcd_dvd_left q C)
  calc
    _ = ((q/g)*g)*(N/(q/g)) := congrArg (fun x : ℕ => x*(N/(q/g))) hq'.symm
    _ = g*((q/g)*(N/(q/g))) := by ring
    _ ≤ g*N := Nat.mul_le_mul_left _ (Nat.mul_div_le N _)
    _ ≤ C*N := Nat.mul_le_mul_right N (Nat.gcd_le_right q hC)

/-- Distinct lcms are counted once, even when different subsets give
the same modulus. There are at most two to the number of conductors. -/
theorem discard (R : Finset ℕ) (C N : ℕ) (T : ℝ) (hC : 0 < C) (hT : 0 < T) :
    T*((bad R C N T).card : ℝ) ≤ (2 : ℝ)^R.card*C*N := by
  classical
  let Q : Finset ℕ := (moduli R).filter (fun q : ℕ => T < (q : ℝ))
  let V := fun q : ℕ => (Ioc 0 N).filter (fun m => q ∣ C*m)
  have hs : bad R C N T ⊆ Q.biUnion V := by
    intro m hm
    obtain ⟨hI,ht⟩ := mem_filter.mp hm
    have hp : profile R C m ∈ R.powerset := mem_powerset.mpr (filter_subset _ _)
    exact mem_biUnion.mpr ⟨_,mem_filter.mpr ⟨mem_image_of_mem _ hp,ht⟩,
      mem_filter.mpr ⟨hI,profile_dvd R C m⟩⟩
  have hcard : ((bad R C N T).card : ℝ) ≤ ∑ q ∈ Q, ((V q).card : ℝ) := by
    exact_mod_cast (card_le_card hs).trans card_biUnion_le
  have hQ : Q.card ≤ 2^R.card := by
    calc Q.card ≤ (moduli R).card := card_filter_le _ _
         _ ≤ R.powerset.card := card_image_le
         _ = _ := card_powerset _
  calc
    _ ≤ T*(∑ q ∈ Q, ((V q).card : ℝ)) := mul_le_mul_of_nonneg_left hcard hT.le
    _ = ∑ q ∈ Q, T*((V q).card : ℝ) := mul_sum _ _ _
    _ ≤ ∑ _q ∈ Q, (C : ℝ)*N := by
      apply sum_le_sum
      intro q hq
      have hq' : T < (q : ℝ) := (mem_filter.mp hq).2
      have hq0 : 0 < q := by exact_mod_cast hT.trans hq'
      exact (mul_le_mul_of_nonneg_right hq'.le (Nat.cast_nonneg _)).trans
        (by exact_mod_cast count_one hq0 hC)
    _ = (Q.card : ℝ)*((C : ℝ)*N) := by simp
    _ ≤ _ := by
      have hc : (Q.card : ℝ) ≤ (2 : ℝ)^R.card := by exact_mod_cast hQ
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (C : ℝ)*N)

noncomputable def shifted (R : Finset ℕ) (C X : ℕ) (T : ℝ) : Finset ℕ :=
  @Finset.filter ℕ (fun n => Even n ∧ ∃ e ∈ Icc 1 (Nat.log 2 X/2),
    T < (modulus (profile R C (n-2^e)) : ℝ)) (Classical.decPred _) (Ico X (2*X))

private theorem shifted_card {R : Finset ℕ} {C X : ℕ} {T : ℝ} (hX : 8 ≤ X) :
    (shifted R C X T).card ≤ (Nat.log 2 X/2)*(bad R C (2*X) T).card := by
  classical
  let B := bad R C (2*X) T
  let I := Icc 1 (Nat.log 2 X/2)
  have hs : shifted R C X T ⊆ I.biUnion (fun e => B.image (fun m => m+2^e)) := by
    intro n hn
    simp only [shifted, mem_filter] at hn
    obtain ⟨hI,_,e,he,hmod⟩ := hn
    have hlog : 2 ≤ Nat.log 2 X := (Nat.le_log_iff_pow_le (by decide) (by omega)).2 (by omega)
    have hbound := (mem_Icc.mp he).2
    have hpower := (Nat.pow_le_pow_right (by decide : 0 < 2)
      (show e+1 ≤ Nat.log 2 X by omega)).trans (Nat.pow_log_le_self 2 (by omega : X ≠ 0))
    rw [pow_succ] at hpower
    have hn' : X ≤ n ∧ n < 2*X := mem_Ico.mp hI
    refine mem_biUnion.mpr ⟨e,he,mem_image.mpr ⟨n-2^e,?_,by omega⟩⟩
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,by omega⟩,hmod⟩
  calc _ ≤ _ := card_le_card hs
       _ ≤ ∑ e ∈ I, (B.image (fun m => m+2^e)).card := card_biUnion_le
       _ ≤ ∑ _e ∈ I, B.card := sum_le_sum (fun _ _ => card_image_le)
       _ = _ := by simp [I,B]

/-- A bounded number of exceptional conductors can vary with X. Those
with combined modulus above the quarter power, at any of the small
binary shifts, use at most the 31/40 power of the original block. -/
theorem shifted_power (K C : ℕ) (hC : 0 < C) :
    ∀ᶠ X : ℕ in atTop, ∀ R : Finset ℕ, R.card ≤ K →
      ((shifted R C X ((X : ℝ)^(1/4 : ℝ))).card : ℝ) ≤ (X : ℝ)^(31/40 : ℝ) := by
  let M := (2 : ℝ)^K*C*2/Real.log 2
  have h2 := Real.log_pos (by norm_num : (1 : ℝ)<2)
  have hCr : 0 < (C : ℝ) := Nat.cast_pos.mpr hC
  have hM : 0 < M := by dsimp [M]; positivity
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/40)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound (inv_pos.mpr hM)
  filter_upwards [eventually_ge_atTop (8 : ℕ),hsmall] with X hX hs
  intro R hR
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hl : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  let T := (X : ℝ)^(1/4 : ℝ)
  have hT : 0 < T := Real.rpow_pos_of_pos hx _
  have hD := discard R C (2*X) T hC hT
  have hRK := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hR
  have hcard : T*((bad R C (2*X) T).card : ℝ) ≤ (2:ℝ)^K*C*(2*(X:ℝ)) := by
    push_cast at hD
    exact hD.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hRK hCr.le) (by positivity))
  have hL : ((Nat.log 2 X/2 : ℕ) : ℝ) ≤ Real.log X/Real.log 2 :=
    (Nat.cast_le.mpr (Nat.div_le_self _ _)).trans (Real.natLog_le_logb X 2)
  have hnat : ((shifted R C X T).card : ℝ) ≤
      ((Nat.log 2 X/2 : ℕ) : ℝ)*(bad R C (2*X) T).card := by
    exact_mod_cast shifted_card (R:=R) (C:=C) (T:=T) hX
  have hsum : T*((shifted R C X T).card : ℝ) ≤ Real.log X/Real.log 2 *
      ((2 : ℝ)^K*C*(2*(X : ℝ))) := calc
    _ ≤ T*(((Nat.log 2 X/2 : ℕ) : ℝ)*(bad R C (2*X) T).card) :=
      mul_le_mul_of_nonneg_left hnat hT.le
    _ = ((Nat.log 2 X/2 : ℕ) : ℝ)*(T*(bad R C (2*X) T).card) := by ring
    _ ≤ _ := mul_le_mul hL hcard (by positivity) (by positivity)
  have hs' : Real.log X ≤ M⁻¹*(X : ℝ)^(1/40 : ℝ) := by
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg hl,
      abs_of_nonneg (Real.rpow_nonneg hx.le _)] using hs
  have hml : M*Real.log X ≤ (X : ℝ)^(1/40 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hs' hM.le
    rwa [← mul_assoc,mul_inv_cancel₀ hM.ne',one_mul] at hh
  apply le_of_mul_le_mul_left _ hT
  refine hsum.trans ?_
  calc
    _ = (M*Real.log X)*(X : ℝ) := by dsimp [M]; ring
    _ ≤ (X : ℝ)^(1/40 : ℝ)*(X : ℝ) := mul_le_mul_of_nonneg_right hml hx.le
    _ = T*(X : ℝ)^(31/40 : ℝ) := by
      dsimp [T]
      rw [← Real.rpow_add hx, ← Real.rpow_add_one hx.ne']
      norm_num

end Conjectures.Goldbach.ExceptionalConductorClasses

open Conjectures.Goldbach.ExceptionalConductorClasses in
theorem Conjectures.Goldbach.ExceptionalConductorClasses :
    (∀ (R : Finset ℕ) (C N : ℕ) (T : ℝ), 0 < C → 0 < T →
      T*((bad R C N T).card : ℝ) ≤ (2 : ℝ)^R.card*C*N) ∧
    (∀ K C : ℕ, 0 < C → ∀ᶠ X : ℕ in Filter.atTop, ∀ R : Finset ℕ, R.card ≤ K →
      ((shifted R C X ((X : ℝ)^(1/4 : ℝ))).card : ℝ) ≤ (X : ℝ)^(31/40 : ℝ)) :=
  ⟨discard,shifted_power⟩
