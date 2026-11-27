import Mathlib

open Finset

private theorem reciprocal_sqrt_sum (B : ℕ) :
    (∑ a ∈ range B, 1 / Real.sqrt ((a : ℝ) + 1)) ≤ 2 * Real.sqrt (B : ℝ) := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [sum_range_succ, Nat.cast_succ]
    have hp : 0 < Real.sqrt ((B : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have hle : Real.sqrt (B : ℝ) ≤ Real.sqrt ((B : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    have hnew := Real.sq_sqrt (show 0 ≤ (B : ℝ) + 1 by positivity)
    have hold := Real.sq_sqrt (Nat.cast_nonneg B : 0 ≤ (B : ℝ))
    have hprod := mul_le_mul_of_nonneg_right
      (show Real.sqrt ((B : ℝ) + 1) + Real.sqrt (B : ℝ) ≤
        2 * Real.sqrt ((B : ℝ) + 1) by linarith) (sub_nonneg.mpr hle)
    have hterm : 1 / Real.sqrt ((B : ℝ) + 1) ≤
        2 * (Real.sqrt ((B : ℝ) + 1) - Real.sqrt (B : ℝ)) := by
      apply (div_le_iff₀ hp).2
      nlinarith only [hnew, hold, hprod]
    linarith only [ih, hterm]

private theorem sqrt_div_nat_le (n a : ℕ) :
    (Nat.sqrt (n / (a+1)) : ℝ) ≤ Real.sqrt (n : ℝ) / Real.sqrt ((a : ℝ)+1) := by
  rw [← Real.sqrt_div (Nat.cast_nonneg n)]
  apply Real.le_sqrt_of_sq_le
  exact (by exact_mod_cast Nat.sqrt_le' (n / (a+1)) :
    (Nat.sqrt (n / (a+1)) : ℝ)^2 ≤ ((n / (a+1) : ℕ) : ℝ)).trans
    (by simpa only [Nat.cast_succ] using (Nat.cast_div_le (α := ℝ) (m := n) (n := a+1)))

theorem Conjectures.Goldbach.Type2PrimePowerSupport :
  ∀ n U B : ℕ, let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0;
  let coeff := fun (v : ℕ → ℝ) (m : ℕ) => ∑ a ∈ m.divisors.filter (fun a => U < a ∧ a ≤ B ∧ U < m / a), (∑ d ∈ a.divisors.filter (fun d => U < d), ((ArithmeticFunction.moebius d : ℤ) : ℝ)) * v (m / a);
  (((Finset.range (n + 1)).filter (fun m => coeff ArithmeticFunction.vonMangoldt m ≠ coeff w m)).card : ℝ) ≤ 2 * Real.sqrt n * Real.sqrt B * (Nat.log 2 n : ℝ) := by
  classical
  intro n U B w coeff
  let L := Nat.log 2 n
  let candidates (i : ℕ) :=
    ((range (Nat.sqrt (n / (i+1)))).product (range L)).image
      (fun x => (i+1) * (x.1+1)^(x.2+1))
  have hsubset : (range (n+1)).filter (fun m => coeff ArithmeticFunction.vonMangoldt m ≠
      coeff w m) ⊆ (range B).biUnion candidates := by
    intro m hm
    obtain ⟨hm, hdifferent⟩ := mem_filter.mp hm
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
    have hchange : ∃ a ∈ m.divisors.filter (fun a => U < a ∧ a ≤ B ∧ U < m/a),
        ArithmeticFunction.vonMangoldt (m/a) ≠ w (m/a) := by
      by_contra! hall
      apply hdifferent
      dsimp only [coeff]
      exact sum_congr rfl (fun a ha => by rw [hall a ha])
    obtain ⟨a, ha, hdiff⟩ := hchange
    obtain ⟨had, _, haB, _⟩ := mem_filter.mp ha
    have ha0 := Nat.pos_of_mem_divisors had
    have hdm := (Nat.mem_divisors.mp had).1
    have hnp : ¬ Nat.Prime (m/a) := by
      intro hp
      exact hdiff (by simp [w, hp, ArithmeticFunction.vonMangoldt_apply_prime hp])
    have hpp : IsPrimePow (m/a) := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp
      (by simpa [w, hnp] using hdiff)
    obtain ⟨p, k, hp, hk, hpow⟩ := (isPrimePow_nat_iff _).mp hpp
    have htwo : 2 ≤ k := by
      by_contra! h
      have hk1 : k = 1 := by omega
      exact hnp (by simpa [hk1, ← hpow] using hp)
    have hpn : p^k ≤ n/a := hpow.trans_le (Nat.div_le_div_right hmn)
    have hpbase : p ≤ Nat.sqrt (n/a) := Nat.le_sqrt'.2
      ((pow_le_pow_right' hp.one_lt.le htwo).trans hpn)
    have hkL : k ≤ L := Nat.le_log_of_pow_le (by decide)
      ((Nat.pow_le_pow_left hp.two_le k).trans (hpn.trans (Nat.div_le_self _ _)))
    refine mem_biUnion.mpr ⟨a-1, mem_range.mpr (by omega), ?_⟩
    change _ ∈ ((range (Nat.sqrt (n / (a-1+1)))).product (range L)).image _
    refine mem_image.mpr ⟨(p-1,k-1), mem_product.mpr
      ⟨mem_range.mpr ?_, mem_range.mpr (by omega)⟩, ?_⟩
    · have hp0 := hp.pos
      simpa only [Nat.sub_add_cancel ha0] using (show p-1 < Nat.sqrt (n/a) by omega)
    · simp only [Nat.sub_add_cancel ha0, Nat.sub_add_cancel hp.pos, Nat.sub_add_cancel hk]
      rw [hpow, Nat.mul_div_cancel' hdm]
  have hcard : ((range (n+1)).filter (fun m => coeff ArithmeticFunction.vonMangoldt m ≠
      coeff w m)).card ≤ ∑ i ∈ range B, Nat.sqrt (n/(i+1)) * L := by
    calc
      _ ≤ ((range B).biUnion candidates).card := card_le_card hsubset
      _ ≤ ∑ i ∈ range B, (candidates i).card := card_biUnion_le
      _ ≤ _ := sum_le_sum (fun i _ => by
        simpa [candidates, card_product] using
          (card_image_le (s := (range (Nat.sqrt (n/(i+1)))).product (range L))
            (f := fun x => (i+1) * (x.1+1)^(x.2+1))))
  calc
    _ ≤ ∑ i ∈ range B, (Nat.sqrt (n/(i+1)) : ℝ) * (L : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ i ∈ range B, (Real.sqrt (n : ℝ) / Real.sqrt ((i : ℝ)+1)) * (L : ℝ) :=
      sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (sqrt_div_nat_le n i) (Nat.cast_nonneg L))
    _ = (Real.sqrt (n : ℝ) * (∑ i ∈ range B, 1 / Real.sqrt ((i : ℝ)+1))) * (L : ℝ) := by
      rw [mul_sum, sum_mul]
      exact sum_congr rfl (fun i _ => by rw [mul_one_div])
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (reciprocal_sqrt_sum B) (Real.sqrt_nonneg (n : ℝ)))
        (Nat.cast_nonneg L)
      convert h using 1
      ring
