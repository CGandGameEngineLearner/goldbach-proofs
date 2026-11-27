import Mathlib

namespace Conjectures.Goldbach.BinaryShiftMissedCenter_aux

lemma two_pow_add_unique {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d)
    (h : 2 ^ a + 2 ^ b = 2 ^ c + 2 ^ d) : a = c ∧ b = d := by
  have hb : b = d := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : 2 ^ a + 2 ^ b ≤ 2 ^ b + 2 ^ b :=
        Nat.add_le_add_right (Nat.pow_le_pow_right (by norm_num) hab) (2 ^ b)
      have h2 : 2 ^ b + 2 ^ b = 2 ^ (b + 1) := by ring
      have h3 : 2 ^ b + 2 ^ b ≤ 2 ^ d := by
        rw [h2]
        exact Nat.pow_le_pow_right (by norm_num) hlt
      have h4 : 2 ^ d < 2 ^ c + 2 ^ d := by
        have hc : 0 < 2 ^ c := by positivity
        omega
      omega
    · have h1 : 2 ^ c + 2 ^ d ≤ 2 ^ d + 2 ^ d :=
        Nat.add_le_add_right (Nat.pow_le_pow_right (by norm_num) hcd) (2 ^ d)
      have h2 : 2 ^ d + 2 ^ d = 2 ^ (d + 1) := by ring
      have h3 : 2 ^ d + 2 ^ d ≤ 2 ^ b := by
        rw [h2]
        exact Nat.pow_le_pow_right (by norm_num) hgt
      have h4 : 2 ^ b < 2 ^ a + 2 ^ b := by
        have ha : 0 < 2 ^ a := by positivity
        omega
      omega
  refine ⟨?_, hb⟩
  have h5 : 2 ^ a = 2 ^ c := by
    rw [hb] at h
    omega
  exact Nat.pow_right_injective (by norm_num) h5

end Conjectures.Goldbach.BinaryShiftMissedCenter_aux

theorem Conjectures.Goldbach.BinaryShiftMissedCenter :
    ∀ n L : ℕ, ((Finset.Icc 1 L).filter (fun e => n = 2^e + 2^(Nat.log 2 (n-2^e)))).card ≤ 2 := by
  intro n L
  classical
  have key : ∀ e : ℕ, n = 2 ^ e + 2 ^ (Nat.log 2 (n - 2 ^ e)) →
      2 ^ (min e (Nat.log 2 (n - 2 ^ e))) + 2 ^ (max e (Nat.log 2 (n - 2 ^ e))) = n := by
    intro e he
    rcases le_total e (Nat.log 2 (n - 2 ^ e)) with h | h
    · rw [min_eq_left h, max_eq_right h]
      exact he.symm
    · rw [min_eq_right h, max_eq_left h]
      exact (Nat.add_comm _ _).trans he.symm
  by_cases hE : ∃ e : ℕ, n = 2 ^ e + 2 ^ (Nat.log 2 (n - 2 ^ e))
  · obtain ⟨e₀, he₀⟩ := hE
    have hsub : ∀ e ∈ (Finset.Icc 1 L).filter (fun e => n = 2^e + 2^(Nat.log 2 (n-2^e))),
        e = min e₀ (Nat.log 2 (n - 2 ^ e₀)) ∨ e = max e₀ (Nat.log 2 (n - 2 ^ e₀)) := by
      intro e he
      have he' : n = 2 ^ e + 2 ^ (Nat.log 2 (n - 2 ^ e)) := (Finset.mem_filter.mp he).2
      have hu := Conjectures.Goldbach.BinaryShiftMissedCenter_aux.two_pow_add_unique
        (min_le_max : min e (Nat.log 2 (n - 2 ^ e)) ≤ max e (Nat.log 2 (n - 2 ^ e)))
        (min_le_max : min e₀ (Nat.log 2 (n - 2 ^ e₀)) ≤ max e₀ (Nat.log 2 (n - 2 ^ e₀)))
        ((key e he').trans (key e₀ he₀).symm)
      rcases le_total e (Nat.log 2 (n - 2 ^ e)) with h | h
      · exact Or.inl ((min_eq_left h).symm.trans hu.1)
      · exact Or.inr ((max_eq_left h).symm.trans hu.2)
    have hmem : (Finset.Icc 1 L).filter (fun e => n = 2^e + 2^(Nat.log 2 (n-2^e))) ⊆
        {min e₀ (Nat.log 2 (n - 2 ^ e₀)), max e₀ (Nat.log 2 (n - 2 ^ e₀))} := by
      intro x hx
      rcases hsub x hx with h | h
      · simp [h]
      · simp [h]
    exact (Finset.card_le_card hmem).trans Finset.card_le_two
  · have hempty : (Finset.Icc 1 L).filter (fun e => n = 2^e + 2^(Nat.log 2 (n-2^e))) = ∅ := by
      refine Finset.not_nonempty_iff_eq_empty.mp ?_
      rintro ⟨x, hx⟩
      exact hE ⟨x, (Finset.mem_filter.mp hx).2⟩
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le 2
