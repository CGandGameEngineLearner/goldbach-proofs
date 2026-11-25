import Mathlib

open Filter Finset Topology

theorem PEqualNP.Outside.L_goldbach_coset_ap_mass :
    let w := fun k : ℕ => if k.Prime then Real.log (k : ℝ) else 0
    let F := fun n q r : ℕ => (Finset.range (n + 1)).filter (fun k => k % q = r)
    let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k
    ∀ q : ℕ, 0 < q → ∀ ε : ℝ, 0 < ε → ∃ X : ℕ, ∀ n ≥ X, ∀ r < q, r.Coprime q →
      |A n q r / (n : ℝ) - 1 / (q.totient : ℝ)| ≤ ε := by
  intro weight fiber mass modulus hmod tolerance htol
  let : NeZero modulus := ⟨hmod.ne'⟩
  let residues := (range modulus).filter (fun residue => residue.Coprime modulus)
  have uniform : ∀ᶠ bound : ℕ in atTop, ∀ residue ∈ residues,
      |mass bound modulus residue / bound - 1 / (modulus.totient : ℝ)| ≤ tolerance := by
    apply (eventually_all_finset residues).2
    intro residue hres
    obtain ⟨hrange, hcop⟩ := mem_filter.mp hres
    have hlt := mem_range.mp hrange
    have limit : Tendsto (fun bound : ℕ => mass bound modulus residue / bound) atTop
        (𝓝 (1 / (modulus.totient : ℝ))) := by
      rw [one_div]
      apply ((Chebyshev.tendsto_sum_log_prime_modEq_div_atTop hcop).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).congr
      intro bound
      simp only [Function.comp_apply, Nat.floor_natCast, mass, fiber,
        Nat.range_succ_eq_Icc_zero, sum_filter]
      rw [← add_sum_Ioc_eq_sum_Icc (Nat.zero_le bound)]
      simp only [weight, Nat.not_prime_zero, ite_false, ite_self, zero_add]
      apply congrArg (fun total : ℝ => total / bound)
      apply sum_congr rfl
      intro prime _
      simp only [Nat.ModEq, Nat.mod_eq_of_lt hlt]
      split_ifs <;> simp_all
    filter_upwards [Metric.tendsto_nhds.mp limit tolerance htol] with bound hbound
    exact le_of_lt (by simpa only [Real.dist_eq] using hbound)
  obtain ⟨threshold, hall⟩ := eventually_atTop.1 uniform
  exact ⟨threshold, fun bound hb residue hr hc =>
    hall bound hb residue (mem_filter.mpr ⟨mem_range.mpr hr, hc⟩)⟩
