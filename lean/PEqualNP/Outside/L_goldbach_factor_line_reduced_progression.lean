import Mathlib

open Finset

/-- Cancelling a common divisor in the two residues also divides the modulus. -/
private theorem reducedLine {a b g n r : ℕ} (hg : 0 < g)
    (ha : g ∣ a) (hb : g ∣ b) (hn : g ∣ n) :
    (a / g) * r ≡ n / g [MOD b / g] ↔ a * r ≡ n [MOD b] := by
  rw [← Nat.ModEq.mul_left_cancel_iff' (Nat.ne_of_gt hg), ← Nat.mul_assoc,
    Nat.mul_div_cancel' ha, Nat.mul_div_cancel' hb, Nat.mul_div_cancel' hn]

theorem PEqualNP.Outside.L_goldbach_factor_line_reduced_progression : let Λ := ArithmeticFunction.vonMangoldt; ∀ (n a b U : ℕ), 0 < a → 0 < b → let g := Nat.gcd a b; (∑ r ∈ Finset.Ioc U (n/a), ∑ s ∈ (Finset.Ioc U (n/b)).filter (fun s => a*r+b*s=n), Λ r * Λ s) = if g ∣ n then ∑ r ∈ (Finset.Ioc U (n/a)).filter (fun r => (a/g)*r % (b/g) = (n/g) % (b/g) ∧ U < (n-a*r)/b), Λ r * Λ ((n-a*r)/b) else 0 := by
  intro Λ n a b U ha hb g
  have hga : g ∣ a := Nat.gcd_dvd_left ..
  have hgb : g ∣ b := Nat.gcd_dvd_right ..
  by_cases hgn : g ∣ n
  · rw [ite_eq_left hgn]
    conv_rhs => rw [sum_filter]
    refine sum_congr rfl fun r hr => ?_
    have har : a*r ≤ n := by
      simpa only [mul_comm] using (Nat.le_div_iff_mul_le ha).mp (mem_Ioc.mp hr).2
    let s₀ := (n-a*r)/b
    have recover {s : ℕ} (h : a*r+b*s=n) : s₀ = s := by
      simp [s₀, ← h, Nat.mul_div_cancel_left _ hb]
    have red := reducedLine (r := r) (Nat.gcd_pos_of_pos_left b ha) hga hgb hgn
    by_cases hit : (a/g)*r % (b/g) = (n/g) % (b/g) ∧ U < s₀
    · rw [ite_eq_left hit]
      have hd := (red.mp hit.1).dvd'
      have he : a*r+b*s₀ = n := by
        rw [show b*s₀ = n-a*r from Nat.mul_div_cancel' hd]
        omega
      have hset : (Ioc U (n/b)).filter (fun s => a*r+b*s=n) = {s₀} := by
        ext s
        simp only [mem_filter, mem_Ioc, mem_singleton]
        constructor
        · exact fun h => (recover h.2).symm
        · rintro rfl
          exact ⟨⟨hit.2, Nat.div_le_div_right (Nat.sub_le ..)⟩,he⟩
      rw [hset, sum_singleton]
    · rw [ite_eq_right hit]
      apply sum_eq_zero
      intro s hs
      obtain ⟨hs,he⟩ := mem_filter.mp hs
      exfalso
      apply hit
      refine ⟨red.mpr ((Nat.modEq_iff_dvd' har).mpr ?_), recover he ▸ (mem_Ioc.mp hs).1⟩
      rw [← he, Nat.add_sub_cancel_left]
      exact dvd_mul_right b s
  · rw [ite_eq_right hgn]
    refine sum_eq_zero fun r _ => sum_eq_zero fun s hs => ?_
    have he := (mem_filter.mp hs).2
    exact (hgn (he ▸ dvd_add (hga.mul_right r) (hgb.mul_right s))).elim