import Mathlib

open scoped BigOperators


theorem PEqualNP.Outside.L_goldbach_coset_rounding_profile :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k%q=r);
    ∀ n q : ℕ, 0<q → let s := (n+1)%q;
      (∑ r ∈ Finset.range q, (((F n q r).card:ℝ)-(n+1:ℕ)/(q:ℝ))^2) =
        (s:ℝ)*((q:ℝ)-s)/q := by
  intro F n q hq s
  let N := n+1
  let t := N/q
  have hsq : s < q := Nat.mod_lt N hq
  have hN : s + q*t = N := Nat.mod_add_div N q
  have hpoint (r j : ℕ) (hr : r < q) :
      q*j+r < N ↔ j < t + (if r < s then 1 else 0) := by
    have hsmall (hj : j < t) : q*j+r < N := by
      have hmul := Nat.mul_le_mul_left q (show j+1 ≤ t by omega)
      rw [Nat.mul_add, Nat.mul_one] at hmul
      omega
    have hlarge (hj : t < j) : N ≤ q*j+r := by
      have hmul := Nat.mul_le_mul_left q (show t+1 ≤ j by omega)
      rw [Nat.mul_add, Nat.mul_one] at hmul
      omega
    rcases lt_trichotomy j t with hj | h | hj
    · have hsmall' := hsmall hj
      by_cases hrs : r < s <;> simp [hrs, hsmall', hj, Nat.lt_succ_of_lt hj]
    · subst j
      by_cases hrs : r < s <;> simp [hrs] <;> omega
    · have hlarge' := hlarge hj
      by_cases hrs : r < s <;> simp [hrs] <;> omega
  have hcard (r : ℕ) (hr : r < q) :
      (F n q r).card = t + (if r < s then 1 else 0) := by
    rw [← Finset.card_range (t + (if r < s then 1 else 0))]
    symm
    apply Finset.card_bij (fun j _ => q*j+r)
    · intro j hj
      simp only [Finset.mem_range] at hj
      change q*j+r ∈ (Finset.range N).filter (fun k => k%q=r)
      simpa [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hr] using (hpoint r j hr).mpr hj
    · intro i hi j hj hij
      apply Nat.eq_of_mul_eq_mul_left hq
      omega
    · intro k hk
      change k ∈ (Finset.range N).filter (fun l => l%q=r) at hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      have hrepr : q*(k/q)+r = k := by
        have := Nat.mod_add_div k q
        omega
      refine ⟨k/q, Finset.mem_range.mpr ((hpoint r (k/q) hr).mp ?_), hrepr⟩
      simpa only [hrepr] using hk.1
  have hsum (a b : ℝ) :
      (∑ r ∈ Finset.range q, (if r < s then a else b)) =
        (q:ℝ)*b+(s:ℝ)*(a-b) := by
    have hfilter : ((Finset.range q).filter (fun r => r < s)) = Finset.range s := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    calc
      _ = ∑ r ∈ Finset.range q, (b + if r < s then a-b else 0) := by
        apply Finset.sum_congr rfl
        intro r hr
        by_cases hrs : r < s <;> simp [hrs]
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter, hfilter]
        simp
        ring
  have hqR : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hNR : (N:ℝ) = (s:ℝ) + (q:ℝ)*(t:ℝ) := by exact_mod_cast hN.symm
  change (∑ r ∈ Finset.range q, (((F n q r).card:ℝ)-(N:ℝ)/(q:ℝ))^2) =
    (s:ℝ)*((q:ℝ)-s)/q
  calc
    _ = ∑ r ∈ Finset.range q,
        (if r < s then ((t:ℝ)+1-(N:ℝ)/(q:ℝ))^2 else ((t:ℝ)-(N:ℝ)/(q:ℝ))^2) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hcard r (Finset.mem_range.mp hr)]
      by_cases hrs : r < s <;> simp [hrs, Nat.cast_add]
    _ = _ := by
      rw [hsum, hNR]
      field_simp
      ring
