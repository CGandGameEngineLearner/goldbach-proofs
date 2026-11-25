import Mathlib

theorem PEqualNP.Outside.L_goldbach_residual_quadratic_signal :
    let F := fun x q r : ℕ => (Finset.range (x+1)).filter (fun k => k % q = r); let e := fun (x q : ℕ) (a : ℕ → ℝ) k => let f := F x q (k % q); a k-(∑ i ∈ f, a i)/(f.card:ℝ); let C := fun (x : ℕ) (a b : ℕ → ℝ) s => ∑ k ∈ (Finset.range (x+1)).filter (fun k => k ≤ s ∧ s-k ≤ x), a k*b (s-k); ∀ (x q c : ℕ) (a b : ℕ → ℝ), c<q → (∑ s ∈ (Finset.range (2*x+1)).filter (fun s => s % q = c), (s:ℝ)^2*C x (e x q a) (e x q b) s) = 2*∑ r ∈ Finset.range q, ((∑ i ∈ F x q r, (i:ℝ)*e x q a i)*(∑ j ∈ F x q ((c % q + q - r) % q), (j:ℝ)*e x q b j)) := by
  intro F e C x q c a b hcq
  have hq : 0 < q := by omega
  have hzero : ∀ (g : ℕ → ℝ) (r : ℕ), ∑ k ∈ F x q r, e x q g k = 0 := by
    intro g r
    have hconst : ∑ k ∈ F x q r, e x q g k =
        ∑ k ∈ F x q r, (g k - (∑ i ∈ F x q r, g i) / ((F x q r).card : ℝ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only [F] at hk
      have hmod : k % q = r := (Finset.mem_filter.mp hk).2
      dsimp only [e]
      rw [hmod]
    rw [hconst]
    by_cases hcard : (F x q r).card = 0
    · have hempty : F x q r = ∅ := Finset.card_eq_zero.mp hcard
      rw [hempty, Finset.sum_empty]
    · have hne : ((F x q r).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcard
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      field_simp <;> ring
  have hrange_add : ∀ (f : ℕ → ℝ) (m n : ℕ),
      ∑ k ∈ Finset.range (m + n), f k =
        (∑ k ∈ Finset.range m, f k) + ∑ k ∈ Finset.range n, f (m + k) := by
    intro f m n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← Nat.add_assoc, Finset.sum_range_succ, Finset.sum_range_succ, ih, add_assoc]
  have hreidx :
      (∑ s ∈ (Finset.range (2 * x + 1)).filter (fun s => s % q = c),
        (s : ℝ) ^ 2 * C x (e x q a) (e x q b) s) =
      ∑ k ∈ Finset.range (x + 1), ∑ j ∈ Finset.range (x + 1),
        if (k + j) % q = c then ((k + j : ℕ) : ℝ) ^ 2 * (e x q a k * e x q b j) else 0 := by
    have h1 :
        (∑ s ∈ (Finset.range (2 * x + 1)).filter (fun s => s % q = c),
          (s : ℝ) ^ 2 * C x (e x q a) (e x q b) s) =
        ∑ s ∈ Finset.range (2 * x + 1), ∑ k ∈ Finset.range (x + 1),
          if s % q = c then
            if k ≤ s ∧ s - k ≤ x then (s : ℝ) ^ 2 * (e x q a k * e x q b (s - k)) else 0
          else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro s _
      by_cases hs : s % q = c
      · rw [if_pos hs]
        dsimp only [C]
        rw [Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro k _
        rw [if_pos hs]
      · rw [if_neg hs]
        symm
        apply Finset.sum_eq_zero
        intro k _
        rw [if_neg hs]
    rw [h1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    have hkx : k ≤ x := by
      have hlt := Finset.mem_range.mp hk
      omega
    have hlen : 2 * x + 1 = k + ((x + 1) + (x - k)) := by omega
    let G : ℕ → ℝ := fun s =>
      if s % q = c then
        if k ≤ s ∧ s - k ≤ x then (s : ℝ) ^ 2 * (e x q a k * e x q b (s - k)) else 0
      else 0
    change ∑ s ∈ Finset.range (2 * x + 1), G s = _
    rw [hlen, hrange_add G k ((x + 1) + (x - k)), hrange_add (fun t => G (k + t)) (x + 1) (x - k)]
    have hleft : ∑ s ∈ Finset.range k, G s = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      have hslt : s < k := Finset.mem_range.mp hs
      dsimp only [G]
      by_cases hsq : s % q = c
      · rw [if_pos hsq, if_neg (by omega)]
      · rw [if_neg hsq]
    have hright : ∑ t ∈ Finset.range (x - k), G (k + (x + 1 + t)) = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      dsimp only [G]
      by_cases hsq : (k + (x + 1 + t)) % q = c
      · rw [if_pos hsq, if_neg (by omega)]
      · rw [if_neg hsq]
    rw [hleft, zero_add, hright, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    have hjx : j ≤ x := by
      have hlt := Finset.mem_range.mp hj
      omega
    dsimp only [G]
    by_cases hsq : (k + j) % q = c
    · rw [if_pos hsq, if_pos hsq, if_pos (by omega)]
      have hsub : k + j - k = j := by omega
      rw [hsub]
    · rw [if_neg hsq, if_neg hsq]
  rw [hreidx]
  have hfib : ∀ f : ℕ → ℝ, ∑ r ∈ Finset.range q, ∑ k ∈ F x q r, f k = ∑ k ∈ Finset.range (x + 1), f k := by
    intro f
    symm
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun k => k % q) (t := Finset.range q)]
    intro k _
    exact Finset.mem_range.mpr (Nat.mod_lt k hq)
  rw [← hfib (fun k => ∑ j ∈ Finset.range (x + 1),
    if (k + j) % q = c then ((k + j : ℕ) : ℝ) ^ 2 * (e x q a k * e x q b j) else 0)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r1 hr1
  have hr1lt : r1 < q := Finset.mem_range.mp hr1
  have hinner :
      (∑ k ∈ F x q r1, ∑ j ∈ Finset.range (x + 1),
        if (k + j) % q = c then ((k + j : ℕ) : ℝ) ^ 2 * (e x q a k * e x q b j) else 0) =
      ∑ r2 ∈ Finset.range q, ∑ k ∈ F x q r1, ∑ j ∈ F x q r2,
        if (k + j) % q = c then ((k + j : ℕ) : ℝ) ^ 2 * (e x q a k * e x q b j) else 0 := by
    symm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    exact hfib (fun j => if (k + j) % q = c then ((k + j : ℕ) : ℝ) ^ 2 * (e x q a k * e x q b j) else 0)
  rw [hinner]
  let r2star : ℕ := (c % q + q - r1) % q
  have hr2star_mem : r2star ∈ Finset.range q := Finset.mem_range.mpr (Nat.mod_lt _ hq)
  have hmod_iff : ∀ r2 < q, (r1 + r2) % q = c ↔ r2 = r2star := by
    intro r2 hr2
    dsimp only [r2star]
    have hcq_mod : c % q = c := Nat.mod_eq_of_lt hcq
    rw [hcq_mod]
    have hstar : (c + q - r1) % q = if r1 ≤ c then c - r1 else c + q - r1 := by
      by_cases hle : r1 ≤ c
      · rw [if_pos hle]
        have heq : c + q - r1 = (c - r1) + q := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      · rw [if_neg hle, Nat.mod_eq_of_lt (by omega)]
    have hsum : (r1 + r2) % q = if r1 + r2 < q then r1 + r2 else r1 + r2 - q := by
      by_cases hlt : r1 + r2 < q
      · rw [if_pos hlt, Nat.mod_eq_of_lt hlt]
      · rw [if_neg hlt]
        have heq : r1 + r2 = (r1 + r2 - q) + q := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
    rw [hstar, hsum]
    by_cases hle : r1 ≤ c <;> by_cases hlt : r1 + r2 < q
    · rw [if_pos hle, if_pos hlt]; omega
    · rw [if_pos hle, if_neg hlt]; omega
    · rw [if_neg hle, if_pos hlt]; omega
    · rw [if_neg hle, if_neg hlt]; omega
  have hcollapse :
      (∑ r2 ∈ Finset.range q, ∑ k ∈ F x q r1, ∑ j ∈ F x q r2,
        if (k + j) % q = c then ((k + j : ℕ) : ℝ) ^ 2 * (e x q a k * e x q b j) else 0) =
      ∑ k ∈ F x q r1, ∑ j ∈ F x q r2star,
        if (k + j) % q = c then ((k + j : ℕ) : ℝ) ^ 2 * (e x q a k * e x q b j) else 0 := by
    apply Finset.sum_eq_single_of_mem r2star hr2star_mem
    intro r2 hr2 hne
    have hr2lt : r2 < q := Finset.mem_range.mp hr2
    have hrc : (r1 + r2) % q ≠ c := by
      intro heq
      exact hne ((hmod_iff r2 hr2lt).mp heq)
    apply Finset.sum_eq_zero
    intro k hk
    apply Finset.sum_eq_zero
    intro j hj
    dsimp only [F] at hk hj
    have hkmod : k % q = r1 := (Finset.mem_filter.mp hk).2
    have hjmod : j % q = r2 := (Finset.mem_filter.mp hj).2
    have hkj : (k + j) % q ≠ c := by
      rw [Nat.add_mod, hkmod, hjmod]
      exact hrc
    rw [if_neg hkj]
  rw [hcollapse]
  have hr2star_lt : r2star < q := Nat.mod_lt _ hq
  have hrc : (r1 + r2star) % q = c := (hmod_iff r2star hr2star_lt).mpr rfl
  have hsplit :
      (∑ k ∈ F x q r1, ∑ j ∈ F x q r2star,
        if (k + j) % q = c then ((k + j : ℕ) : ℝ) ^ 2 * (e x q a k * e x q b j) else 0) =
      ((∑ k ∈ F x q r1, ∑ j ∈ F x q r2star, ((k : ℝ) ^ 2 * e x q a k) * e x q b j) +
       (∑ k ∈ F x q r1, ∑ j ∈ F x q r2star, e x q a k * ((j : ℝ) ^ 2 * e x q b j))) +
      (∑ k ∈ F x q r1, ∑ j ∈ F x q r2star, 2 * (((k : ℝ) * e x q a k) * ((j : ℝ) * e x q b j))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [F] at hk hj
    have hkmod : k % q = r1 := (Finset.mem_filter.mp hk).2
    have hjmod : j % q = r2star := (Finset.mem_filter.mp hj).2
    have hkj : (k + j) % q = c := by
      rw [Nat.add_mod, hkmod, hjmod, hrc]
    rw [if_pos hkj, Nat.cast_add]
    ring
  rw [hsplit]
  have hterm1 : (∑ k ∈ F x q r1, ∑ j ∈ F x q r2star, ((k : ℝ) ^ 2 * e x q a k) * e x q b j) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [← Finset.mul_sum, hzero b r2star, mul_zero]
  have hterm2 : (∑ k ∈ F x q r1, ∑ j ∈ F x q r2star, e x q a k * ((j : ℝ) ^ 2 * e x q b j)) = 0 := by
    have hpull :
        (∑ k ∈ F x q r1, ∑ j ∈ F x q r2star, e x q a k * ((j : ℝ) ^ 2 * e x q b j)) =
        (∑ k ∈ F x q r1, e x q a k) * (∑ j ∈ F x q r2star, (j : ℝ) ^ 2 * e x q b j) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
    rw [hpull, hzero a r1, zero_mul]
  have hterm3 :
      (∑ k ∈ F x q r1, ∑ j ∈ F x q r2star, 2 * (((k : ℝ) * e x q a k) * ((j : ℝ) * e x q b j))) =
      2 * ((∑ i ∈ F x q r1, (i : ℝ) * e x q a i) * (∑ j ∈ F x q r2star, (j : ℝ) * e x q b j)) := by
    symm
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum, Finset.mul_sum]
  rw [hterm1, hterm2, hterm3, add_zero, zero_add]
