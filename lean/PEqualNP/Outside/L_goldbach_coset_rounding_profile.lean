import Mathlib

theorem PEqualNP.Outside.L_goldbach_coset_rounding_profile :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k%q=r); ∀ n q : ℕ, 0<q → let s := (n+1)%q; (∑ r ∈ Finset.range q, (((F n q r).card:ℝ)-(n+1:ℕ)/(q:ℝ))^2) = (s:ℝ)*((q:ℝ)-s)/q := by
  dsimp only
  intro n q hq
  set m := (n + 1) / q with hm_def
  set s := (n + 1) % q with hs_def
  have hs : s < q := Nat.mod_lt _ hq
  have hdiv : n + 1 = m * q + s := by
    have h := Nat.div_add_mod (n + 1) q
    rw [← hm_def, ← hs_def] at h
    have h2 : q * m = m * q := Nat.mul_comm q m
    omega
  have hcount : ∀ r, r < q → ((Finset.range (n+1)).filter (fun k => k % q = r)).card = m + (if r < s then 1 else 0) := by
    intro r hr
    have himg : (Finset.range (n+1)).filter (fun k => k % q = r)
        = (Finset.range (m + (if r < s then 1 else 0))).image (fun i => i * q + r) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hk, hkr⟩
        have hklt : k < m * q + s := by omega
        set t := k / q with ht_def
        have hk_eq : t * q + r = k := by
          have h := Nat.div_add_mod k q
          rw [← ht_def] at h
          rw [hkr] at h
          have h2 : q * t = t * q := Nat.mul_comm q t
          omega
        have htle : t ≤ m := by
          by_contra hcon
          have h1 : m + 1 ≤ t := by omega
          have h2 : (m+1)*q ≤ t*q := Nat.mul_le_mul_right q h1
          have h3 : (m+1)*q = m*q + q := by ring
          have h4 : t*q ≤ k := by omega
          omega
        rcases lt_or_eq_of_le htle with hlt | heq
        · refine ⟨t, ?_, ?_⟩
          · by_cases hrs : r < s <;> simp [hrs] <;> omega
          · omega
        · have hk_eq' : m * q + r = k := by
            rw [heq] at hk_eq
            exact hk_eq
          refine ⟨m, ?_, ?_⟩
          · have hrs : r < s := by omega
            simp [hrs]
          · exact hk_eq'
      · rintro ⟨i, hi, hk⟩
        constructor
        · by_cases hrs : r < s
          · rw [if_pos hrs] at hi
            rcases lt_or_eq_of_le (by omega : i ≤ m) with hlt | heq
            · have h1 : (i+1)*q ≤ m*q := Nat.mul_le_mul_right q (by omega)
              have h2 : (i+1)*q = i*q + q := by ring
              omega
            · have hk2 : m * q + r = k := by
                rw [heq] at hk
                exact hk
              omega
          · rw [if_neg hrs] at hi
            have h1 : (i+1)*q ≤ m*q := Nat.mul_le_mul_right q (by omega)
            have h2 : (i+1)*q = i*q + q := by ring
            omega
        · rw [← hk, Nat.add_comm (i*q) r, Nat.mul_comm i q, Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt hr]
    rw [himg, Finset.card_image_of_injective _ ?_, Finset.card_range]
    intro i j hij
    have h2 : i * q + r = j * q + r := hij
    have h : i * q = j * q := by omega
    exact Nat.eq_of_mul_eq_mul_right hq h
  have hc : ((n+1:ℕ):ℝ)/(q:ℝ) = (m:ℝ) + (s:ℝ)/(q:ℝ) := by
    have hqR : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have hn1 : ((n+1:ℕ):ℝ) = (m:ℝ)*(q:ℝ) + (s:ℝ) := by
      rw [hdiv]
      push_cast
      ring
    rw [hn1]
    field_simp
  have hterm : ∀ r ∈ Finset.range q, ((((Finset.range (n+1)).filter (fun k => k % q = r)).card:ℝ) - ((n+1:ℕ):ℝ)/(q:ℝ))^2
      = if r < s then (1 - (s:ℝ)/(q:ℝ))^2 else ((s:ℝ)/(q:ℝ))^2 := by
    intro r hr
    have hrq : r < q := Finset.mem_range.mp hr
    have h1 := hcount r hrq
    by_cases hrs : r < s
    · rw [if_pos hrs] at h1
      rw [if_pos hrs, h1, hc]
      push_cast
      ring
    · rw [if_neg hrs] at h1
      rw [if_neg hrs, h1, hc]
      push_cast
      ring
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_ite]
  have hf1 : (Finset.range q).filter (fun r => r < s) = Finset.range s := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hf2 : ((Finset.range q).filter (fun r => ¬ r < s)).card = q - s := by
    have hfe : (Finset.range q).filter (fun r => ¬ r < s) = Finset.range q \ Finset.range s := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff]
    rw [hfe, Finset.card_sdiff]
    have hfi : Finset.range s ∩ Finset.range q = Finset.range s := by
      ext r
      simp only [Finset.mem_inter, Finset.mem_range]
      omega
    rw [hfi, Finset.card_range q, Finset.card_range s]
  have h1 : (∑ r ∈ (Finset.range q).filter (fun r => r < s), (1 - (s:ℝ)/(q:ℝ))^2)
      = (s:ℝ) * (1 - (s:ℝ)/(q:ℝ))^2 := by
    rw [Finset.sum_const, nsmul_eq_mul, hf1, Finset.card_range s]
  have h2 : (∑ r ∈ (Finset.range q).filter (fun r => ¬ r < s), ((s:ℝ)/(q:ℝ))^2)
      = ((q:ℝ) - (s:ℝ)) * ((s:ℝ)/(q:ℝ))^2 := by
    rw [Finset.sum_const, nsmul_eq_mul, hf2]
    have hcast : ((q - s : ℕ) : ℝ) = (q:ℝ) - (s:ℝ) := Nat.cast_sub hs.le
    rw [hcast]
  rw [h1, h2]
  have hqR : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp
  ring
