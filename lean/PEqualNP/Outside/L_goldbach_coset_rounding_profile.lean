import Mathlib

theorem PEqualNP.Outside.L_goldbach_coset_rounding_profile :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k%q=r); ∀ n q : ℕ, 0<q → let s := (n+1)%q; (∑ r ∈ Finset.range q, (((F n q r).card:ℝ)-(n+1:ℕ)/(q:ℝ))^2) = (s:ℝ)*((q:ℝ)-s)/q := by
  dsimp only
  intro n q hq
  -- count of numbers `≤ n` in a residue class
  have card_eq : ∀ r : ℕ, r < q →
      ((Finset.range (n+1)).filter (fun k => k % q = r)).card = (n + q - r) / q := by
    intro r hr
    have hset : (Finset.range (n+1)).filter (fun k => k % q = r)
        = (Finset.range ((n + 1 + q - 1 - r) / q)).image (fun i => i*q + r) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hk, hkr⟩
        refine ⟨k/q, ?_, ?_⟩
        · apply (Nat.lt_div_iff_mul_lt hq).mpr
          have hdiv : q * (k/q) + r = k := by rw [← hkr, Nat.div_add_mod]
          have hkq : q * (k/q) = k - r := by omega
          rw [mul_comm (k/q) q, hkq]
          have : n + 1 + q - 1 - r - (q - 1) = n + 1 - r := by omega
          rw [this]
          have hrk : r ≤ k := hkr ▸ Nat.mod_le k q
          omega
        · have h1 : q * (k/q) + r = k := by rw [← hkr, Nat.div_add_mod]
          rw [mul_comm (k/q) q, h1]
      · rintro ⟨i, hi, rfl⟩
        constructor
        · have hi' := (Nat.lt_div_iff_mul_lt hq).mp hi
          have hb : n + 1 + q - 1 - r - (q - 1) = n + 1 - r := by omega
          rw [hb] at hi'
          omega
        · rw [mul_comm i q, add_comm (q * i) r, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    rw [hset, Finset.card_image_of_injective _
      (fun a b hab => Nat.eq_of_mul_eq_mul_right hq (Nat.add_right_cancel hab))]
    have h1 : n + 1 + q - 1 - r = n + q - r := by omega
    rw [Finset.card_range, h1]
  -- rewrite the count as quotient plus indicator
  have key : ∀ r : ℕ, r < q →
      (n + q - r)/q = (n+1)/q + (if r < (n+1)%q then 1 else 0) := by
    intro r hr
    have hN : n + 1 = q * ((n+1)/q) + (n+1)%q := (Nat.div_add_mod (n+1) q).symm
    have e1 : n + q - r = (n+1) + (q - 1 - r) := by omega
    have hadd : (n+1)%q + (q - 1 - r) + q * ((n+1)/q) = n + q - r := by omega
    have step : (n + q - r)/q = ((n+1)%q + (q - 1 - r))/q + (n+1)/q := by
      conv_lhs => rw [← hadd]
      rw [mul_comm q ((n+1)/q)]
      exact Nat.add_mul_div_right _ _ hq
    have hslt : (n+1)%q < q := Nat.mod_lt (n+1) hq
    have e3 : (n+1)%q + (q - 1 - r) = (n+1)%q + q - 1 - r := by omega
    have hA : ((n+1)%q + q - 1 - r)/q = if r < (n+1)%q then 1 else 0 := by
      by_cases h : r < (n+1)%q
      · rw [ite_eq_left h]
        have hdiv1 : ∀ x : ℕ, q ≤ x → x < 2*q → x/q = 1 := by
          intro x h1 h2
          obtain ⟨t, rfl⟩ : ∃ t, x = q + t := ⟨x - q, by omega⟩
          have ht : t < q := by omega
          rw [add_comm, show t + q = t + 1 * q by rw [Nat.one_mul],
            Nat.add_mul_div_right _ 1 hq, Nat.div_eq_of_lt ht, Nat.zero_add]
        exact hdiv1 _ (by omega) (by omega)
      · rw [ite_eq_right h]
        exact Nat.div_eq_of_lt (by omega)
    rw [step, e3, hA]
    omega
  -- cast of the quotient identity
  have hcast : ((n+1 : ℕ) : ℝ)/(q:ℝ) = (((n+1)/q : ℕ) : ℝ) + (((n+1)%q : ℕ) : ℝ)/(q:ℝ) := by
    have hN : (n+1 : ℕ) = q * ((n+1)/q) + (n+1)%q := (Nat.div_add_mod (n+1) q).symm
    have hNR : ((n+1 : ℕ) : ℝ) = (q:ℝ) * (((n+1)/q : ℕ) : ℝ) + (((n+1)%q : ℕ) : ℝ) := by
      conv_lhs => rw [hN]
      push_cast
      ring
    have hqR : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    rw [hNR]
    field_simp
  -- the terms
  have hterm : ∀ r ∈ Finset.range q,
      ((((Finset.range (n+1)).filter (fun k => k % q = r)).card : ℝ) - ((n+1:ℕ):ℝ)/(q:ℝ))^2
      = ((((n+1)/q : ℕ) : ℝ) + (if r < (n+1)%q then (1:ℝ) else 0) - ((n+1:ℕ):ℝ)/(q:ℝ))^2 := by
    intro r hr
    rw [Finset.mem_range] at hr
    rw [card_eq r hr, key r hr]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm]
  have hsle : (n+1)%q ≤ q := le_of_lt (Nat.mod_lt (n+1) hq)
  have hsplit : ∀ f : ℕ → ℝ,
      ∑ r ∈ Finset.range q, f r
        = ∑ r ∈ Finset.range ((n+1)%q), f r
          + ∑ r ∈ Finset.range (q - (n+1)%q), f ((n+1)%q + r) := by
    intro f
    conv_lhs => rw [← Nat.add_sub_of_le hsle]
    rw [Finset.sum_range_add]
  rw [hsplit]
  -- first block: indicator is 1
  have h1 : ∑ r ∈ Finset.range ((n+1)%q),
      ((((n+1)/q : ℕ) : ℝ) + (if r < (n+1)%q then (1:ℝ) else 0) - ((n+1:ℕ):ℝ)/(q:ℝ))^2
      = ((((n+1)%q : ℕ) : ℝ)) * (1 - ((((n+1)%q : ℕ) : ℝ)/(q:ℝ)))^2 := by
    have hstep : ∀ r ∈ Finset.range ((n+1)%q),
        ((((n+1)/q : ℕ) : ℝ) + (if r < (n+1)%q then (1:ℝ) else 0) - ((n+1:ℕ):ℝ)/(q:ℝ))^2
        = (1 - ((((n+1)%q : ℕ) : ℝ)/(q:ℝ)))^2 := by
      intro r hr
      rw [Finset.mem_range] at hr
      rw [ite_eq_left hr, hcast]
      ring
    rw [Finset.sum_congr rfl hstep, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- second block: indicator is 0
  have h2 : ∑ r ∈ Finset.range (q - (n+1)%q),
      ((((n+1)/q : ℕ) : ℝ) + (if (n+1)%q + r < (n+1)%q then (1:ℝ) else 0) - ((n+1:ℕ):ℝ)/(q:ℝ))^2
      = ((q - (n+1)%q : ℕ) : ℝ) * ((((n+1)%q : ℕ) : ℝ)/(q:ℝ))^2 := by
    have hstep : ∀ r ∈ Finset.range (q - (n+1)%q),
        ((((n+1)/q : ℕ) : ℝ) + (if (n+1)%q + r < (n+1)%q then (1:ℝ) else 0) - ((n+1:ℕ):ℝ)/(q:ℝ))^2
        = ((((n+1)%q : ℕ) : ℝ)/(q:ℝ))^2 := by
      intro r hr
      rw [ite_eq_right (by omega), hcast]
      ring
    rw [Finset.sum_congr rfl hstep, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [h1, h2]
  have hqs : ((q - (n+1)%q : ℕ) : ℝ) = (q:ℝ) - (((n+1)%q : ℕ) : ℝ) := by
    rw [Nat.cast_sub hsle]
  rw [hqs]
  have hqR : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp
  ring