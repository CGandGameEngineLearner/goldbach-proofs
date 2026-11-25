import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Defs

open Finset

theorem PEqualNP.Outside.L_goldbach_finite_power_count_via_exponent :
    ∀ n : ℕ, ((Finset.Icc 1 n).filter (fun k => 0 < ((Finset.Icc 2 (Nat.log 2 k)).filter (fun a => k.minFac^a=k)).card)).card ≤ Nat.sqrt n + (Nat.log 2 n) * (Finset.Icc 1 n |>.filter (fun p => p^3 ≤ n)).card := by
  classical
  intro n
  let small := (Icc 1 (Nat.sqrt n)).image (fun p : ℕ => p^2)
  let bases := (Icc 1 n).filter (fun p : ℕ => p^3 ≤ n)
  let powers := (bases.product (Icc 2 (Nat.log 2 n))).image (fun z : ℕ × ℕ => z.1^z.2)
  have hpcover :
      (Icc 1 n).filter (fun k => 0 < ((Icc 2 (Nat.log 2 k)).filter (fun a => k.minFac^a=k)).card)
        ⊆ small ∪ powers := by
    intro k hk
    obtain ⟨hkBounds, hkPower⟩ := mem_filter.mp hk
    obtain ⟨a, ha⟩ := card_pos.mp hkPower
    obtain ⟨haBounds, haEq⟩ := mem_filter.mp ha
    obtain ⟨haLower, haUpper⟩ := mem_Icc.mp haBounds
    let p := k.minFac
    have hp₁ : 1 ≤ p := Nat.minFac_pos _
    have hpPow : p^a ≤ n := haEq.le.trans (mem_Icc.mp hkBounds).2
    by_cases haTwo : a = 2
    · subst a
      have hpSqrt : p ≤ Nat.sqrt n := Nat.le_sqrt'.2 hpPow
      exact mem_union_left _ (mem_image.mpr ⟨p, mem_Icc.mpr ⟨hp₁,hpSqrt⟩, haEq⟩)
    · have haThree : 3 ≤ a := by omega
      have hpCube : p^3 ≤ n := (Nat.pow_le_pow_right hp₁ haThree).trans hpPow
      have hpN : p ≤ n := by
        have hpBound : p^1 ≤ p^3 := Nat.pow_le_pow_right hp₁ (by decide)
        simpa only [pow_one] using hpBound.trans hpCube
      have haLog : a ≤ Nat.log 2 n := haUpper.trans (Nat.log_mono_right (mem_Icc.mp hkBounds).2)
      exact mem_union_right _ (mem_image.mpr ⟨(p,a),
        mem_product.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hp₁,hpN⟩,hpCube⟩,
          mem_Icc.mpr ⟨haLower,haLog⟩⟩, haEq⟩)
  have hsmall : small.card ≤ Nat.sqrt n := by
    dsimp [small]
    refine card_image_le.trans ?_
    rw [Nat.card_Icc]
    omega
  have hpowers : powers.card ≤ Nat.log 2 n * bases.card := by
    dsimp [powers]
    refine card_image_le.trans ?_
    rw [Finset.card_product, Nat.mul_comm _ bases.card]
    apply Nat.mul_le_mul_left
    rw [Nat.card_Icc]
    omega
  have hcount := (card_le_card hpcover).trans (card_union_le small powers)
  exact hcount.trans (Nat.add_le_add hsmall hpowers)

