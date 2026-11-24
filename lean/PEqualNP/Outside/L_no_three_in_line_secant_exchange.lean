import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_secant_exchange :
    let d := fun (a b c : ℤ × ℤ) => (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1); let ok := fun (S : Finset (ℤ × ℤ)) => ∀ a∈S, ∀ b∈S, ∀ c∈S, a≠b → b≠c → a≠c → d a b c≠0; ∀ (S : Finset (ℤ × ℤ)) (r x y : ℤ × ℤ), let T := S.erase r; ok S → x≠y → (∀ a∈T,∀ b∈T,a≠b → d a b x≠0 ∧ d a b y≠0) → (∀ a∈T,d x y a≠0) → ok (insert x (insert y T)) := by
  dsimp only
  intro S r x y hS hxy hT hxyT p hp q hq s hs hpq hqs hps
  have memT : ∀ z, z ∈ insert x (insert y (S.erase r)) → z ≠ x → z ≠ y → z ∈ S.erase r := by
    intro z hz hzx hzy
    rcases Finset.mem_insert.mp hz with h | h
    · exact absurd h hzx
    · rcases Finset.mem_insert.mp h with h' | h'
      · exact absurd h' hzy
      · exact h'
  have hsub : ∀ a ∈ S.erase r, a ∈ S := fun a ha => Finset.mem_of_mem_erase ha
  by_cases hpx : p = x
  · rw [hpx] at hpq hps ⊢
    by_cases hqy : q = y
    · rw [hqy] at hpq hqs ⊢
      exact hxyT s (memT s hs (fun h => hps h.symm) (fun h => hqs h.symm))
    · have hqT := memT q hq (fun h => hpq h.symm) hqy
      by_cases hsy : s = y
      · rw [hsy] at hps hqs ⊢
        intro h0
        exact hxyT q hqT (by first | linear_combination h0 | linear_combination -h0)
      · have hsT := memT s hs (fun h => hps h.symm) hsy
        intro h0
        exact (hT q hqT s hsT hqs).1 (by first | linear_combination h0 | linear_combination -h0)
  · by_cases hpy : p = y
    · rw [hpy] at hpq hps ⊢
      by_cases hqx : q = x
      · rw [hqx] at hpq hqs ⊢
        intro h0
        exact hxyT s (memT s hs (fun h => hqs h.symm) (fun h => hps h.symm)) (by first | linear_combination h0 | linear_combination -h0)
      · have hqT := memT q hq hqx (fun h => hpq h.symm)
        by_cases hsx : s = x
        · rw [hsx] at hps hqs ⊢
          intro h0
          exact hxyT q hqT (by first | linear_combination h0 | linear_combination -h0)
        · have hsT := memT s hs hsx (fun h => hps h.symm)
          intro h0
          exact (hT q hqT s hsT hqs).2 (by first | linear_combination h0 | linear_combination -h0)
    · have hpT := memT p hp hpx hpy
      by_cases hqx : q = x
      · rw [hqx] at hpq hqs ⊢
        by_cases hsy : s = y
        · rw [hsy] at hps hqs ⊢
          intro h0
          exact hxyT p hpT (by first | linear_combination h0 | linear_combination -h0)
        · have hsT := memT s hs (fun h => hqs h.symm) hsy
          intro h0
          exact (hT p hpT s hsT hps).1 (by first | linear_combination h0 | linear_combination -h0)
      · by_cases hqy : q = y
        · rw [hqy] at hpq hqs ⊢
          by_cases hsx : s = x
          · rw [hsx] at hps hqs ⊢
            intro h0
            exact hxyT p hpT (by first | linear_combination h0 | linear_combination -h0)
          · have hsT := memT s hs hsx (fun h => hqs h.symm)
            intro h0
            exact (hT p hpT s hsT hps).2 (by first | linear_combination h0 | linear_combination -h0)
        · have hqT := memT q hq hqx hqy
          by_cases hsx : s = x
          · rw [hsx] at hps hqs ⊢
            exact (hT p hpT q hqT hpq).1
          · by_cases hsy : s = y
            · rw [hsy] at hps hqs ⊢
              exact (hT p hpT q hqT hpq).2
            · have hsT := memT s hs hsx hsy
              exact hS p (hsub p hpT) q (hsub q hqT) s (hsub s hsT) hpq hqs hps
