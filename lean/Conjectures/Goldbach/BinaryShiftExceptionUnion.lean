import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Local reduction, not the unconditional registered theorem.
A power bound on the ordinary Goldbach exceptional set is the only input.
An eventual Pintz bound with exponent 18/25 implies the weaker 3/4 input. -/

namespace GoldbachBinaryShiftReduction
open Finset

def reps (m : ℕ) : ℕ :=
  ((range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card

def exceptions (Y : ℕ) : Finset ℕ :=
  (Icc 4 Y).filter (fun m => Even m ∧ reps m = 0)

def badShift (X : ℕ) : Finset ℕ :=
  (Ico X (2*X)).filter (fun n => Even n ∧ 0 <
    ((Icc 1 (Nat.log 2 X / 2)).filter (fun e => reps (n-2^e) = 0)).card)

/-- Each flagged target is in the image of a pair (exception, shift index). -/
theorem count_le {X : ℕ} (hx : 8 ≤ X) :
    (badShift X).card ≤ (exceptions (2*X)).card * (Nat.log 2 X / 2) := by
  let H := Icc 1 (Nat.log 2 X / 2)
  let D := exceptions (2*X)
  let addShift := fun u : ℕ × ℕ => u.1 + 2^u.2
  have sub : badShift X ⊆ (D ×ˢ H).image addShift := by
    intro n hn
    obtain ⟨hnI, hEven, hSome⟩ := mem_filter.mp hn
    obtain ⟨hlo,hhi⟩ := mem_Ico.mp hnI
    obtain ⟨e,he⟩ := card_pos.mp hSome
    obtain ⟨heH, hrep⟩ := mem_filter.mp he
    obtain ⟨he1,heL⟩ := mem_Icc.mp heH
    have hsq := Nat.pow_le_of_le_log (b:=2) (x:=e+e) (y:=X) (by omega) (by omega)
    rw [pow_add] at hsq
    have htwo : 2 ≤ 2^e := by
      exact (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) he1 : 2^1 ≤ 2^e)
    have hdouble : 2^e+2^e ≤ X := by
      have h := Nat.mul_le_mul_right (2^e) htwo
      rw [two_mul] at h
      exact h.trans hsq
    have hle : 2^e ≤ n := by omega
    have hpow : Even ((2:ℕ)^e) := even_two.pow_of_ne_zero (by omega)
    have hdiff : Even (n-2^e) := (Nat.even_sub hle).mpr ⟨fun _ => hpow, fun _ => hEven⟩
    have hm : n-2^e ∈ D := by
      apply mem_filter.mpr
      exact ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hdiff, hrep⟩
    exact mem_image.mpr ⟨(n-2^e,e), mem_product.mpr ⟨hm,heH⟩, Nat.sub_add_cancel hle⟩
  calc
    _ ≤ ((D ×ˢ H).image addShift).card := card_le_card sub
    _ ≤ (D ×ˢ H).card := card_image_le
    _ = _ := by simp [D,H, Nat.card_Icc]

private theorem absorb (k : ℕ) (hk : 256 ≤ k) : k^20 * 2^15 ≤ 2^k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have h1 : 256^20 * (k+1)^20 ≤ 257^20 * k^20 := by
      simpa only [mul_pow] using Nat.pow_le_pow_left (show 256*(k+1) ≤ 257*k by omega) 20
    have h2 : 257^20 * k^20 ≤ (2*256^20)*k^20 :=
      Nat.mul_le_mul_right _ (by decide)
    have step : (k+1)^20 ≤ 2*k^20 := by
      apply Nat.le_of_mul_le_mul_left (c := 256^20) _ (by decide)
      calc
        _ ≤ _ := h1.trans h2
        _ = _ := by ac_rfl
    calc
      (k+1)^20 * 2^15 ≤ (2*k^20)*2^15 := Nat.mul_le_mul_right _ step
      _ = 2*(k^20 * 2^15) := by ac_rfl
      _ ≤ 2*(2^k) := Nat.mul_le_mul_left _ ih
      _ = 2^(k+1) := by rw [pow_succ, Nat.mul_comm]

/-- The quantified conclusion is the desk's frozen target, conditional only on
an ordinary, unshifted exceptional-set estimate (in integer arithmetic). -/
theorem of_exception_bound
    (hp : ∃ T : ℕ, ∀ Y ≥ T, (exceptions Y).card^4 ≤ Y^3) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (badShift X).card^5 ≤ X^4 := by
  obtain ⟨T,hT⟩ := hp
  refine ⟨max T (2^256), ?_⟩
  intro X hX
  have ht := (le_max_left T (2^256)).trans hX
  have hx := (le_max_right T (2^256)).trans hX
  have h8 : 8 ≤ X := le_trans (by decide : 8 ≤ (2:ℕ)^256) hx
  let L := Nat.log 2 X / 2
  let B := (exceptions (2*X)).card
  have hk : 256 ≤ Nat.log 2 X := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr hx
  have hL : L^20 * 2^15 ≤ X := calc
    _ ≤ (Nat.log 2 X)^20 * 2^15 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.div_le_self _ _) _)
    _ ≤ 2^(Nat.log 2 X) := absorb _ hk
    _ ≤ X := Nat.pow_log_le_self 2 (by omega)
  have hB : B^4 ≤ (2*X)^3 := hT _ (by omega)
  have h := Nat.pow_le_pow_left (count_le h8) 20
  apply (Nat.pow_le_pow_iff_left (n:=4) (by decide)).mp
  calc
    ((badShift X).card^5)^4 = (badShift X).card^20 := by ring
    _ ≤ (B*L)^20 := h
    _ = (B^4)^5 * L^20 := by ring
    _ ≤ ((2*X)^3)^5 * L^20 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hB 5)
    _ = (L^20*2^15)*X^15 := by ring
    _ ≤ X*X^15 := Nat.mul_le_mul_right _ hL
    _ = (X^4)^4 := by ring

/-- Adapter for an integer version of the published 18/25 estimate.
No analytic exception theorem is postulated or proved by this adapter. -/
theorem frozen_of_pintz
    (hp : ∃ T : ℕ, ∀ Y ≥ T, (exceptions Y).card^25 ≤ Y^18) :
    let G := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card; ∃ X₀ : ℕ, ∀ X ≥ X₀, let L := Nat.log 2 X / 2; let E := (Finset.Ico X (2*X)).filter (fun n => Even n ∧ 0 < ((Finset.Icc 1 L).filter (fun e => G (n-2^e)=0)).card); E.card^5 ≤ X^4 := by
  apply of_exception_bound
  obtain ⟨T,hT⟩ := hp
  refine ⟨max T 1, ?_⟩
  intro Y hY
  have ht := (le_max_left T 1).trans hY
  have hy := (le_max_right T 1).trans hY
  apply (Nat.pow_le_pow_iff_left (n:=25) (by decide)).mp
  calc
    ((exceptions Y).card^4)^25 = ((exceptions Y).card^25)^4 := by ring
    _ ≤ (Y^18)^4 := Nat.pow_le_pow_left (hT Y ht) 4
    _ = Y^72 := by ring
    _ ≤ Y^75 := Nat.pow_le_pow_right (by omega) (by decide)
    _ = (Y^3)^25 := by ring

end GoldbachBinaryShiftReduction
