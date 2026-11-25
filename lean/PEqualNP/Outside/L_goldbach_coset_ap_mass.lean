import Mathlib

theorem PEqualNP.Outside.L_goldbach_coset_ap_mass :
    let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; ∀ q : ℕ, 0<q → ∀ ε : ℝ, 0<ε → ∃ X : ℕ, ∀ n≥X, ∀ r<q, r.Coprime q → |A n q r/(n:ℝ)-1/(q.totient:ℝ)| ≤ ε := by
  intro w F A q hq ε hε
  haveI : NeZero q := ⟨by omega⟩
  have hIoc : ∀ n : ℕ, Finset.Ioc 0 n = (Finset.range (n+1)).filter (fun k => k ≠ 0) := by
    intro n
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_range]
    omega
  have hA : ∀ (n r : ℕ), r < q → A n q r =
      ∑ p ∈ Finset.Ioc 0 n with p.Prime ∧ p ≡ r [MOD q], Real.log (p:ℝ) := by
    intro n r hr
    have hLHS : A n q r =
        ∑ k ∈ Finset.range (n+1), if k.Prime ∧ k % q = r then Real.log (k:ℝ) else 0 := by
      change (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = r),
        (if k.Prime then Real.log (k:ℝ) else 0)) = _
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hp : k.Prime
      · by_cases hq : k % q = r
        · simp [hp, hq]
        · simp [hp, hq]
      · simp [hp]
    rw [hLHS, hIoc n]
    rw [Finset.filter_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hp : k.Prime
    · have hk0 : k ≠ 0 := hp.ne_zero
      have hmod : (k ≡ r [MOD q]) ↔ (k % q = r) := by
        constructor
        · intro h
          rw [Nat.ModEq] at h
          rwa [Nat.mod_eq_of_lt hr] at h
        · intro h
          rw [Nat.ModEq]
          rwa [Nat.mod_eq_of_lt hr]
      by_cases hq : k % q = r
      · simp [hp, hk0, hmod.mpr hq, hq]
      · have hnmod : ¬ (k ≡ r [MOD q]) := fun h => hq (hmod.mp h)
        simp [hp, hk0, hq, hnmod]
    · have : ¬ (k.Prime ∧ (k ≡ r [MOD q])) := fun h => hp h.1
      simp [hp, this]
  have key : ∀ r : ℕ, r < q → r.Coprime q → ∀ᶠ n : ℕ in Filter.atTop,
      |A n q r / (n:ℝ) - 1/(q.totient:ℝ)| ≤ ε := by
    intro r hr hrc
    have hlim := Chebyshev.tendsto_sum_log_prime_modEq_div_atTop (q := q) (a := r) hrc
    have hcomp : Filter.Tendsto (fun n : ℕ =>
        (∑ p ∈ Finset.Ioc 0 n with p.Prime ∧ p ≡ r [MOD q], Real.log (p:ℝ)) / (n:ℝ))
        Filter.atTop (nhds ((q.totient:ℝ)⁻¹)) := by
      have h := hlim.comp tendsto_natCast_atTop_atTop
      simpa [Function.comp_def] using h
    have hmetric : ∀ᶠ n : ℕ in Filter.atTop, dist ((∑ p ∈ Finset.Ioc 0 n with p.Prime ∧ p ≡ r [MOD q], Real.log (p:ℝ)) / (n:ℝ)) ((q.totient:ℝ)⁻¹) < ε := by
      exact Filter.eventually_atTop.mpr ((Metric.tendsto_atTop.mp hcomp) ε hε)
    filter_upwards [hmetric] with n hn
    have hAeq : A n q r = ∑ p ∈ Finset.Ioc 0 n with p.Prime ∧ p ≡ r [MOD q], Real.log (p:ℝ) :=
      hA n r hr
    rw [Real.dist_eq] at hn
    rw [hAeq, one_div]
    exact le_of_lt hn
  have hAll : ∀ᶠ n : ℕ in Filter.atTop, ∀ r ∈ Finset.range q, r < q → r.Coprime q →
      |A n q r / (n:ℝ) - 1/(q.totient:ℝ)| ≤ ε := by
    rw [Finset.eventually_all]
    intro r hr
    have hrq : r < q := Finset.mem_range.mp hr
    by_cases hrc : r.Coprime q
    · filter_upwards [key r hrq hrc] with n hn
      intro _ _; exact hn
    · exact Filter.Eventually.of_forall (fun n _ h => absurd h hrc)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hAll
  exact ⟨X, fun n hn r hr hrc => hX n hn r (Finset.mem_range.mpr hr) hr hrc⟩
