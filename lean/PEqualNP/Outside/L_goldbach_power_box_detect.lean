import Mathlib

set_option maxHeartbeats 400000 in
theorem PEqualNP.Outside.L_goldbach_power_box_detect :
    let A := fun k : ℕ => if 0 < ((Finset.Icc 2 (Nat.log 2 k)).filter (fun a => k.minFac ^ a=k)).card then Real.log (k:ℝ) else 0;
    let S := fun n : ℕ => (Finset.range (n+1)) ∩ (((Finset.Icc 2 (Nat.sqrt n)).product (Finset.Icc 2 (Nat.log 2 n))).image (fun z => z.1 ^ z.2));
    ∀ n k : ℕ, k≤n → A k≠0 → k∈S n := by
  intro A S n k hkn hA
  have hgoal : k ∈ (Finset.range (n+1)) ∩
      (((Finset.Icc 2 (Nat.sqrt n)).product (Finset.Icc 2 (Nat.log 2 n))).image (fun z => z.1 ^ z.2)) := by
    by_cases hc : 0 < ((Finset.Icc 2 (Nat.log 2 k)).filter (fun a => k.minFac ^ a=k)).card
    · obtain ⟨a, ha⟩ := Finset.card_pos.mp hc
      obtain ⟨haIcc, hpow⟩ := Finset.mem_filter.mp ha
      obtain ⟨h2a, hak⟩ := Finset.mem_Icc.mp haIcc
      have h2log : 0 < Nat.log 2 k := by omega
      have hk2 : 2 ≤ k := (Nat.log_pos_iff.mp h2log).1
      have hprime : k.minFac.Prime := Nat.minFac_prime (by omega)
      have hp2 : 2 ≤ k.minFac := hprime.two_le
      have hp2a : k.minFac ^ 2 ≤ k.minFac ^ a := Nat.pow_le_pow_right (by omega) h2a
      have hp2k : k.minFac ^ 2 ≤ k := le_trans hp2a (le_of_eq hpow)
      have hpsqrt : k.minFac ≤ Nat.sqrt n := Nat.le_sqrt'.mpr (le_trans hp2k hkn)
      have halogn : a ≤ Nat.log 2 n := le_trans hak (Nat.log_mono_right hkn)
      refine Finset.mem_inter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
      refine Finset.mem_image.mpr ⟨(k.minFac, a), ?_, hpow⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hp2, hpsqrt⟩, Finset.mem_Icc.mpr ⟨h2a, halogn⟩⟩
    · have hA' : (if 0 < ((Finset.Icc 2 (Nat.log 2 k)).filter (fun a => k.minFac ^ a=k)).card
          then Real.log (k:ℝ) else 0) ≠ 0 := hA
      rw [if_neg hc] at hA'
      exact (hA' rfl).elim
  exact hgoal
