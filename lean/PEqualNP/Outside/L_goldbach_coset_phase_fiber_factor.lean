import Mathlib

theorem PEqualNP.Outside.L_goldbach_coset_phase_fiber_factor :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q = r); let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; let j := fun n q r : ℕ => (n + q - r) % q; let B := fun n s : ℕ => ∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s-k ≤ n), w k*w (s-k); let Y := fun (n q : ℕ) (z : ℂ) => (B n n:ℂ) + ∑ h ∈ Finset.Icc 1 (n/q), ((B n (n+h*q):ℂ)*z^h + (B n (n-h*q):ℂ)*(z⁻¹)^h); ∀ (n q : ℕ) (u : ℂ), 0<q → u≠0 → u^n*Y n q (u^q) = ∑ r ∈ Finset.range q, (∑ k ∈ F n q r, (w k:ℂ)*u^k)*(∑ k ∈ F n q (j n q r), (w k:ℂ)*u^k) := by
  intro F w A j B Y n q u hq hu
  let c : ℕ := n % q
  have hcq : c < q := Nat.mod_lt n hq
  let T : ℕ → ℂ := fun s => (B n s : ℂ) * u ^ s
  have hrange_add : ∀ (f : ℕ → ℂ) (a b : ℕ),
      ∑ k ∈ Finset.range (a + b), f k =
        (∑ k ∈ Finset.range a, f k) + ∑ k ∈ Finset.range b, f (a + k) := by
    intro f a b
    induction b with
    | zero => simp
    | succ b ih =>
      rw [← Nat.add_assoc, Finset.sum_range_succ, Finset.sum_range_succ, ih, add_assoc]
  have hrange_reflect : ∀ (f : ℕ → ℂ) (m : ℕ),
      ∑ k ∈ Finset.range m, f k = ∑ k ∈ Finset.range m, f (m - 1 - k) := by
    intro f m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have hsplit : m + 1 = 1 + m := by omega
      have h1 : ∑ k ∈ Finset.range (m + 1), f (m + 1 - 1 - k) =
          f m + ∑ k ∈ Finset.range m, f (m - 1 - k) := by
        rw [hsplit, hrange_add (fun k => f (1 + m - 1 - k)) 1 m]
        have hhead : ∑ k ∈ Finset.range 1, f (1 + m - 1 - k) = f m := by
          rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
          have h0 : 1 + m - 1 - 0 = m := by omega
          rw [h0]
        have htail : ∑ k ∈ Finset.range m, f (1 + m - 1 - (1 + k)) =
            ∑ k ∈ Finset.range m, f (m - 1 - k) := by
          apply Finset.sum_congr rfl
          intro k _
          have heq : 1 + m - 1 - (1 + k) = m - 1 - k := by omega
          rw [heq]
        rw [hhead, htail]
      rw [h1, add_comm]
  have hIcc_succ : ∀ (f : ℕ → ℂ) (m : ℕ),
      ∑ h ∈ Finset.Icc 1 (m + 1), f h = (∑ h ∈ Finset.Icc 1 m, f h) + f (m + 1) := by
    intro f m
    have hset : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnotmem : m + 1 ∉ Finset.Icc 1 m := by
      simp only [Finset.mem_Icc]
      omega
    rw [hset, Finset.sum_insert hnotmem, add_comm]
  have hmod_add_eq : ∀ a b : ℕ, (a + b) % q = a % q ↔ b % q = 0 := by
    intro a b
    have ha := Nat.div_add_mod a q
    have hb := Nat.div_add_mod b q
    have hab := Nat.div_add_mod (a + b) q
    have hlt_a := Nat.mod_lt a hq
    have hlt_b := Nat.mod_lt b hq
    have hlt_ab := Nat.mod_lt (a + b) hq
    constructor
    · intro heq
      have h1 : q * ((a + b) / q) = q * (a / q + b / q) + b % q := by nlinarith
      have hle : a / q + b / q ≤ (a + b) / q := by nlinarith
      have hge : (a + b) / q ≤ a / q + b / q := by nlinarith
      nlinarith
    · intro hb0
      have h1 : a + b = a % q + q * (a / q + b / q) := by nlinarith
      rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt_a]
  have hmul_sum : ∀ (f : ℕ → ℂ) (M : ℕ),
      (∑ d ∈ Finset.range M, if (d + 1) % q = 0 then f (d + 1) else 0) =
      ∑ h ∈ Finset.Icc 1 (M / q), f (h * q) := by
    intro f M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      have hM := Nat.div_add_mod M q
      have hM1 := Nat.div_add_mod (M + 1) q
      have hltM := Nat.mod_lt M hq
      have hltM1 := Nat.mod_lt (M + 1) hq
      by_cases hdvd : (M + 1) % q = 0
      · rw [if_pos hdvd]
        have hdiv : (M + 1) / q = M / q + 1 := by
          have h1 : M / q < (M + 1) / q := by nlinarith
          have h2 : (M + 1) / q ≤ M / q + 1 := by nlinarith
          omega
        have hprod : (M / q + 1) * q = M + 1 := by nlinarith
        rw [hdiv, hIcc_succ (fun h => f (h * q)) (M / q), hprod]
      · rw [if_neg hdvd, add_zero]
        have hdiv : (M + 1) / q = M / q := by
          have h1 : M / q ≤ (M + 1) / q := by nlinarith
          have h2 : (M + 1) / q ≤ M / q := by nlinarith
          omega
        rw [hdiv]
  have hLHS :
      u ^ n * Y n q (u ^ q) =
      ∑ s ∈ (Finset.range (2 * n + 1)).filter (fun s => s % q = c), T s := by
    have hYexpand :
        u ^ n * Y n q (u ^ q) =
        T n + (∑ h ∈ Finset.Icc 1 (n / q), T (n + h * q)) +
          ∑ h ∈ Finset.Icc 1 (n / q), T (n - h * q) := by
      dsimp only [Y]
      rw [mul_add, Finset.mul_sum]
      have hterm :
          ∑ h ∈ Finset.Icc 1 (n / q),
            u ^ n * ((B n (n + h * q) : ℂ) * (u ^ q) ^ h + (B n (n - h * q) : ℂ) * ((u ^ q)⁻¹) ^ h) =
          ∑ h ∈ Finset.Icc 1 (n / q), (T (n + h * q) + T (n - h * q)) := by
        apply Finset.sum_congr rfl
        intro h hh
        have hh2 : h ≤ n / q := (Finset.mem_Icc.mp hh).2
        have hhq : h * q ≤ n := le_trans (Nat.mul_le_mul_right q hh2) (Nat.div_mul_le_self n q)
        rw [mul_add]
        have hpos : u ^ n * ((B n (n + h * q) : ℂ) * (u ^ q) ^ h) = T (n + h * q) := by
          dsimp only [T]
          rw [pow_add, ← pow_mul, mul_comm q h]
          ring
        have hneg : u ^ n * ((B n (n - h * q) : ℂ) * ((u ^ q)⁻¹) ^ h) = T (n - h * q) := by
          dsimp only [T]
          have hn : n = (n - h * q) + h * q := by omega
          have huq : u ^ q ≠ 0 := pow_ne_zero q hu
          have hinv : (u ^ q) ^ h * ((u ^ q)⁻¹) ^ h = 1 := by
            rw [← mul_pow]
            have h1 : u ^ q * (u ^ q)⁻¹ = 1 := by field_simp
            rw [h1, one_pow]
          have hpow : u ^ n = u ^ (n - h * q) * (u ^ q) ^ h := by
            rw [hn, pow_add, ← pow_mul, mul_comm q h]
          calc
            u ^ n * ((B n (n - h * q) : ℂ) * ((u ^ q)⁻¹) ^ h)
                = (B n (n - h * q) : ℂ) * u ^ (n - h * q) * ((u ^ q) ^ h * ((u ^ q)⁻¹) ^ h) := by
                  rw [hpow]; ring
            _ = (B n (n - h * q) : ℂ) * u ^ (n - h * q) := by rw [hinv, mul_one]
        rw [hpos, hneg]
      rw [hterm, Finset.sum_add_distrib, ← add_assoc]
      have h0 : u ^ n * (B n n : ℂ) = T n := by dsimp only [T]; ring
      rw [h0]
    rw [hYexpand]
    rw [Finset.sum_filter]
    have h2n : 2 * n + 1 = n + (1 + n) := by omega
    rw [h2n, hrange_add (fun s => if s % q = c then T s else 0) n (1 + n),
        hrange_add (fun t => if (n + t) % q = c then T (n + t) else 0) 1 n]
    have hmid : (∑ t ∈ Finset.range 1, if (n + t) % q = c then T (n + t) else 0) = T n := by
      rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero]
      rw [if_pos (rfl : n % q = c)]
    have hupper :
        (∑ d ∈ Finset.range n, if (n + (1 + d)) % q = c then T (n + (1 + d)) else 0) =
        ∑ h ∈ Finset.Icc 1 (n / q), T (n + h * q) := by
      have hcongr :
          (∑ d ∈ Finset.range n, if (n + (1 + d)) % q = c then T (n + (1 + d)) else 0) =
          ∑ d ∈ Finset.range n, if (d + 1) % q = 0 then T (n + (d + 1)) else 0 := by
        apply Finset.sum_congr rfl
        intro d _
        have h1d : 1 + d = d + 1 := by omega
        rw [h1d]
        by_cases hd : (d + 1) % q = 0
        · have hmod : (n + (d + 1)) % q = c := (hmod_add_eq n (d + 1)).mpr hd
          rw [if_pos hmod, if_pos hd]
        · have hmod : (n + (d + 1)) % q ≠ c := fun h => hd ((hmod_add_eq n (d + 1)).mp h)
          rw [if_neg hmod, if_neg hd]
      rw [hcongr, hmul_sum (fun m => T (n + m)) n]
    have hlower :
        (∑ s ∈ Finset.range n, if s % q = c then T s else 0) =
        ∑ h ∈ Finset.Icc 1 (n / q), T (n - h * q) := by
      rw [hrange_reflect (fun s => if s % q = c then T s else 0) n]
      have hcongr :
          (∑ d ∈ Finset.range n, if (n - 1 - d) % q = c then T (n - 1 - d) else 0) =
          ∑ d ∈ Finset.range n, if (d + 1) % q = 0 then T (n - (d + 1)) else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        have hdlt : d < n := Finset.mem_range.mp hd
        have hsub : n - 1 - d = n - (d + 1) := by omega
        rw [hsub]
        have hadd : (n - (d + 1)) + (d + 1) = n := by omega
        by_cases h0 : (d + 1) % q = 0
        · have hmod : (n - (d + 1)) % q = c := by
            dsimp only [c]
            have := (hmod_add_eq (n - (d + 1)) (d + 1)).mpr h0
            rw [hadd] at this
            exact this.symm
          rw [if_pos hmod, if_pos h0]
        · have hmod : (n - (d + 1)) % q ≠ c := by
            intro h
            apply h0
            apply (hmod_add_eq (n - (d + 1)) (d + 1)).mp
            rw [hadd]
            exact h.symm
          rw [if_neg hmod, if_neg h0]
      rw [hcongr, hmul_sum (fun m => T (n - m)) n]
    rw [hmid, hupper, hlower]
    ring
  have hRHS :
      (∑ s ∈ (Finset.range (2 * n + 1)).filter (fun s => s % q = c), T s) =
      ∑ r ∈ Finset.range q,
        (∑ k ∈ F n q r, (w k : ℂ) * u ^ k) * (∑ k ∈ F n q (j n q r), (w k : ℂ) * u ^ k) := by
    have hreidx :
        (∑ s ∈ (Finset.range (2 * n + 1)).filter (fun s => s % q = c), T s) =
        ∑ k ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (n + 1),
          if (k + m) % q = c then ((w k : ℂ) * u ^ k) * ((w m : ℂ) * u ^ m) else 0 := by
      have h1 :
          (∑ s ∈ (Finset.range (2 * n + 1)).filter (fun s => s % q = c), T s) =
          ∑ s ∈ Finset.range (2 * n + 1), ∑ k ∈ Finset.range (n + 1),
            if s % q = c then
              if k ≤ s ∧ s - k ≤ n then (w k : ℂ) * (w (s - k) : ℂ) * u ^ s else 0
            else 0 := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro s _
        by_cases hs : s % q = c
        · rw [if_pos hs]
          dsimp only [T, B]
          push_cast
          rw [Finset.sum_mul, Finset.sum_filter]
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
      have hkn : k ≤ n := by
        have hlt := Finset.mem_range.mp hk
        omega
      have hlen : 2 * n + 1 = k + ((n + 1) + (n - k)) := by omega
      let G : ℕ → ℂ := fun s =>
        if s % q = c then
          if k ≤ s ∧ s - k ≤ n then (w k : ℂ) * (w (s - k) : ℂ) * u ^ s else 0
        else 0
      change ∑ s ∈ Finset.range (2 * n + 1), G s = _
      rw [hlen, hrange_add G k ((n + 1) + (n - k)), hrange_add (fun t => G (k + t)) (n + 1) (n - k)]
      have hleft : ∑ s ∈ Finset.range k, G s = 0 := by
        apply Finset.sum_eq_zero
        intro s hs
        have hslt : s < k := Finset.mem_range.mp hs
        dsimp only [G]
        by_cases hsq : s % q = c
        · rw [if_pos hsq, if_neg (by omega)]
        · rw [if_neg hsq]
      have hright : ∑ t ∈ Finset.range (n - k), G (k + (n + 1 + t)) = 0 := by
        apply Finset.sum_eq_zero
        intro t _
        dsimp only [G]
        by_cases hsq : (k + (n + 1 + t)) % q = c
        · rw [if_pos hsq, if_neg (by omega)]
        · rw [if_neg hsq]
      rw [hleft, zero_add, hright, add_zero]
      apply Finset.sum_congr rfl
      intro m hm
      have hmn : m ≤ n := by
        have hlt := Finset.mem_range.mp hm
        omega
      dsimp only [G]
      by_cases hsq : (k + m) % q = c
      · rw [if_pos hsq, if_pos hsq, if_pos (by omega)]
        have hsub : k + m - k = m := by omega
        rw [hsub, pow_add]
        ring
      · rw [if_neg hsq, if_neg hsq]
    rw [hreidx]
    have hfib : ∀ f : ℕ → ℂ, ∑ r ∈ Finset.range q, ∑ k ∈ F n q r, f k = ∑ k ∈ Finset.range (n + 1), f k := by
      intro f
      symm
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun k => k % q) (t := Finset.range q)]
      intro k _
      exact Finset.mem_range.mpr (Nat.mod_lt k hq)
    rw [← hfib (fun k => ∑ m ∈ Finset.range (n + 1),
      if (k + m) % q = c then ((w k : ℂ) * u ^ k) * ((w m : ℂ) * u ^ m) else 0)]
    apply Finset.sum_congr rfl
    intro r1 hr1
    have hr1lt : r1 < q := Finset.mem_range.mp hr1
    have hinner :
        (∑ k ∈ F n q r1, ∑ m ∈ Finset.range (n + 1),
          if (k + m) % q = c then ((w k : ℂ) * u ^ k) * ((w m : ℂ) * u ^ m) else 0) =
        ∑ r2 ∈ Finset.range q, ∑ k ∈ F n q r1, ∑ m ∈ F n q r2,
          if (k + m) % q = c then ((w k : ℂ) * u ^ k) * ((w m : ℂ) * u ^ m) else 0 := by
      symm
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      exact hfib (fun m => if (k + m) % q = c then ((w k : ℂ) * u ^ k) * ((w m : ℂ) * u ^ m) else 0)
    rw [hinner]
    have hj_eq : j n q r1 = (c + q - r1) % q := by
      dsimp only [j]
      have hdm : n % q + q * (n / q) = n := Nat.mod_add_div n q
      have heq : n + q - r1 = (c + q - r1) + q * (n / q) := by
        dsimp only [c]
        omega
      rw [heq, Nat.add_mul_mod_self_left]
    have hj_mem : j n q r1 ∈ Finset.range q := by
      dsimp only [j]
      exact Finset.mem_range.mpr (Nat.mod_lt _ hq)
    have hmod_iff : ∀ r2 < q, (r1 + r2) % q = c ↔ r2 = j n q r1 := by
      intro r2 hr2
      rw [hj_eq]
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
        (∑ r2 ∈ Finset.range q, ∑ k ∈ F n q r1, ∑ m ∈ F n q r2,
          if (k + m) % q = c then ((w k : ℂ) * u ^ k) * ((w m : ℂ) * u ^ m) else 0) =
        ∑ k ∈ F n q r1, ∑ m ∈ F n q (j n q r1),
          if (k + m) % q = c then ((w k : ℂ) * u ^ k) * ((w m : ℂ) * u ^ m) else 0 := by
      apply Finset.sum_eq_single_of_mem (j n q r1) hj_mem
      intro r2 hr2 hne
      have hr2lt : r2 < q := Finset.mem_range.mp hr2
      have hrc : (r1 + r2) % q ≠ c := fun heq => hne ((hmod_iff r2 hr2lt).mp heq)
      apply Finset.sum_eq_zero
      intro k hk
      apply Finset.sum_eq_zero
      intro m hm
      dsimp only [F] at hk hm
      have hkmod : k % q = r1 := (Finset.mem_filter.mp hk).2
      have hmmod : m % q = r2 := (Finset.mem_filter.mp hm).2
      have hkm : (k + m) % q ≠ c := by
        rw [Nat.add_mod, hkmod, hmmod]
        exact hrc
      rw [if_neg hkm]
    rw [hcollapse]
    have hj_lt : j n q r1 < q := Finset.mem_range.mp hj_mem
    have hrc : (r1 + j n q r1) % q = c := (hmod_iff (j n q r1) hj_lt).mpr rfl
    have hdrop :
        (∑ k ∈ F n q r1, ∑ m ∈ F n q (j n q r1),
          if (k + m) % q = c then ((w k : ℂ) * u ^ k) * ((w m : ℂ) * u ^ m) else 0) =
        ∑ k ∈ F n q r1, ∑ m ∈ F n q (j n q r1), ((w k : ℂ) * u ^ k) * ((w m : ℂ) * u ^ m) := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro m hm
      dsimp only [F] at hk hm
      have hkmod : k % q = r1 := (Finset.mem_filter.mp hk).2
      have hmmod : m % q = j n q r1 := (Finset.mem_filter.mp hm).2
      have hkm : (k + m) % q = c := by
        rw [Nat.add_mod, hkmod, hmmod, hrc]
      rw [if_pos hkm]
    rw [hdrop]
    symm
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
  exact hLHS.trans hRHS
