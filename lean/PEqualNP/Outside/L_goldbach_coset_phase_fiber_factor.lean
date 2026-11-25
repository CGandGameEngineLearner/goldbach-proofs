import Mathlib

set_option maxHeartbeats 1600000

theorem PEqualNP.Outside.L_goldbach_coset_phase_fiber_factor :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k%q=r); let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; let j := fun n q r : ℕ => (n+q-r)%q; let B := fun n s : ℕ => ∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s-k ≤ n), w k*w (s-k); let Y := fun (n q : ℕ) (z : ℂ) => (B n n:ℂ) + ∑ h ∈ Finset.Icc 1 (n/q), ((B n (n+h*q):ℂ)*z^h + (B n (n-h*q):ℂ)*(z⁻¹)^h); ∀ (n q : ℕ) (u : ℂ), 0<q → u≠0 → u^n*Y n q (u^q) = ∑ r ∈ Finset.range q, (∑ k ∈ F n q r, (w k:ℂ)*u^k)*(∑ k ∈ F n q (j n q r), (w k:ℂ)*u^k) := by
  dsimp only
  intro n q u hq hu
  have key : ∀ (W : ℕ → ℂ) (n q : ℕ) (u : ℂ), 0 < q → u ≠ 0 →
      (let PP : ℕ → Finset ℕ := fun s => (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s - k ≤ n)
       let BB : ℕ → ℂ := fun s => ∑ k ∈ PP s, W k * W (s-k)
       let FF : ℕ → Finset ℕ := fun r => (Finset.range (n+1)).filter (fun k => k % q = r)
       u^n*(BB n + ∑ h ∈ Finset.Icc 1 (n/q), (BB (n+h*q)*(u^q)^h + BB (n-h*q)*((u^q)⁻¹)^h)) =
         ∑ r ∈ Finset.range q,
           (∑ k ∈ FF r, W k*u^k) * (∑ k ∈ FF ((n+q-r)%q), W k*u^k)) := by
    intro W n q u hq hu
    let PP : ℕ → Finset ℕ := fun s => (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s - k ≤ n)
    let BB : ℕ → ℂ := fun s => ∑ k ∈ PP s, W k * W (s-k)
    let FF : ℕ → Finset ℕ := fun r => (Finset.range (n+1)).filter (fun k => k % q = r)
    change u^n*(BB n + ∑ h ∈ Finset.Icc 1 (n/q),
        (BB (n+h*q)*(u^q)^h + BB (n-h*q)*((u^q)⁻¹)^h)) =
      ∑ r ∈ Finset.range q,
        (∑ k ∈ FF r, W k*u^k) * (∑ k ∈ FF ((n+q-r)%q), W k*u^k)
    let S : Finset (ℕ × ℕ) :=
      ((Finset.range (n+1)) ×ˢ (Finset.range (n+1))).filter
        (fun kp : ℕ × ℕ => (kp.1 + kp.2) % q = n % q)
    let g : ℕ × ℕ → ℂ := fun kp => W kp.1 * W kp.2 * u^(kp.1 + kp.2)
    have hR : ∑ r ∈ Finset.range q,
        (∑ k ∈ FF r, W k*u^k) * (∑ k ∈ FF ((n+q-r)%q), W k*u^k) = ∑ kp ∈ S, g kp := by
      have hfib : ∀ r, r < q → S.filter (fun kp => kp.1 % q = r) =
          (FF r) ×ˢ (FF ((n+q-r)%q)) := by
        intro r hr
        ext kp
        obtain ⟨k, p⟩ := kp
        simp only [S, FF, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        constructor
        · rintro ⟨⟨⟨hk, hp⟩, hmod⟩, hkr⟩
          refine ⟨⟨hk, hkr⟩, hp, ?_⟩
          have hkp : ((k : ℕ) : ZMod q) = ((k % q : ℕ) : ZMod q) := by
            rw [ZMod.natCast_eq_natCast_iff']
            rw [Nat.mod_eq_of_lt (Nat.mod_lt k hq)]
          have hmod' : (((k + p : ℕ)) : ZMod q) = (n : ZMod q) :=
            (ZMod.natCast_eq_natCast_iff' (k + p) n q).mpr hmod
          have hp' : ((p : ℕ) : ZMod q) = ((n + q - k % q : ℕ) : ZMod q) := by
            have h1 : ((p : ℕ) : ZMod q) = (n : ZMod q) - (k : ZMod q) := by
              have h2 := hmod'
              push_cast at h2
              linear_combination h2
            rw [h1, hkp]
            rw [Nat.cast_sub (by omega : k % q ≤ n + q), Nat.cast_add, ZMod.natCast_self,
              add_zero]
          rw [← hkr]
          exact (ZMod.natCast_eq_natCast_iff' p (n + q - k % q) q).mp hp'
        · rintro ⟨⟨hk, hkr⟩, hp, hpr⟩
          refine ⟨⟨⟨hk, hp⟩, ?_⟩, hkr⟩
          have h1 : ((k : ℕ) : ZMod q) = (r : ZMod q) := by
            rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hr]
            exact hkr
          have h2 : ((p : ℕ) : ZMod q) = ((n+q-r : ℕ) : ZMod q) :=
            (ZMod.natCast_eq_natCast_iff' p (n+q-r) q).mpr hpr
          have h3 : ((n+q-r : ℕ) : ZMod q) = (n : ZMod q) - (r : ZMod q) := by
            rw [Nat.cast_sub (by omega : r ≤ n + q), Nat.cast_add, ZMod.natCast_self,
              add_zero]
          have h4 : (((k + p : ℕ)) : ZMod q) = (n : ZMod q) := by
            push_cast
            rw [h1, h2, h3]
            ring
          exact (ZMod.natCast_eq_natCast_iff' (k + p) n q).mp h4
      have hmaps2 : ∀ kp ∈ S, kp.1 % q ∈ Finset.range q := by
        intro kp _
        rw [Finset.mem_range]
        exact Nat.mod_lt _ hq
      rw [← Finset.sum_fiberwise_of_maps_to (f := g) hmaps2]
      apply Finset.sum_congr rfl
      intro r _
      rw [hfib r (by simpa using ‹r ∈ Finset.range q›)]
      rw [Finset.sum_product]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro p _
      simp only [g]
      rw [pow_add]
      ring
    let E : Finset ℕ := insert n
      ((Finset.Icc 1 (n/q)).image (fun h => n + h*q) ∪
        (Finset.Icc 1 (n/q)).image (fun h => n - h*q))
    have hEmod : ∀ s ∈ E, s % q = n % q := by
      intro s hs
      simp only [E, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_Icc] at hs
      rcases hs with rfl | ⟨h, ⟨h1, h2⟩, rfl⟩ | ⟨h, ⟨h1, h2⟩, rfl⟩
      · rfl
      · rw [← ZMod.natCast_eq_natCast_iff']
        push_cast
        rw [ZMod.natCast_self, mul_zero, add_zero]
      · have hle : h*q ≤ n := (Nat.le_div_iff_mul_le hq).mp h2
        rw [← ZMod.natCast_eq_natCast_iff']
        rw [Nat.cast_sub hle]
        have hz : ((h*q : ℕ) : ZMod q) = 0 := by
          push_cast
          rw [ZMod.natCast_self, mul_zero]
        rw [hz, sub_zero]
    have L1 : ∀ s : ℕ, n ≤ s → s % q = n % q → ∃ h, s - n = q * h := by
      intro s hns hmod
      have hm : n ≡ s [MOD q] := hmod.symm
      exact (Nat.modEq_iff_dvd' hns).mp hm
    have L2 : ∀ s : ℕ, s ≤ n → s % q = n % q → ∃ h, n - s = q * h := by
      intro s hsn hmod
      have hm : s ≡ n [MOD q] := hmod
      exact (Nat.modEq_iff_dvd' hsn).mp hm
    have hmaps : ∀ kp ∈ S, kp.1 + kp.2 ∈ E := by
      rintro ⟨k, p⟩ hkp
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hkp
      obtain ⟨⟨hk, hp⟩, hmod⟩ := hkp
      have hk' : k ≤ n := by omega
      have hp' : p ≤ n := by omega
      rcases lt_trichotomy (k + p) n with hlt | heq | hgt
      · obtain ⟨h, hh⟩ := L2 (k + p) (le_of_lt hlt) hmod
        rw [mul_comm] at hh
        have hq_le : h*q ≤ n := by omega
        have hsp : n - h*q = k + p := by omega
        have h1 : 1 ≤ h := by
          rcases Nat.eq_zero_or_pos h with h0 | h0
          · subst h0
            simp only [zero_mul] at hh
            omega
          · exact h0
        have h2 : h ≤ n/q := (Nat.le_div_iff_mul_le hq).mpr hq_le
        simp only [E, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
        exact Or.inr (Or.inr ⟨h, ⟨h1, h2⟩, hsp⟩)
      · simp only [E, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
        exact Or.inl heq
      · obtain ⟨h, hh⟩ := L1 (k + p) (le_of_lt hgt) hmod
        rw [mul_comm] at hh
        have hq_le : h*q ≤ n := by omega
        have hsp : n + h*q = k + p := by omega
        have h1 : 1 ≤ h := by
          rcases Nat.eq_zero_or_pos h with h0 | h0
          · subst h0
            simp only [zero_mul] at hh
            omega
          · exact h0
        have h2 : h ≤ n/q := (Nat.le_div_iff_mul_le hq).mpr hq_le
        simp only [E, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
        exact Or.inr (Or.inl ⟨h, ⟨h1, h2⟩, hsp⟩)
    have hfiber : ∀ s, s % q = n % q →
        S.filter (fun kp => kp.1 + kp.2 = s) = (PP s).image (fun k => (k, s - k)) := by
      intro s hsmod
      ext kp
      obtain ⟨k, p⟩ := kp
      simp only [S, PP, Finset.mem_filter, Finset.mem_image, Finset.mem_product,
        Finset.mem_range]
      constructor
      · rintro ⟨⟨⟨hk, hp⟩, hmod⟩, hsum⟩
        refine ⟨k, ⟨hk, by omega, by omega⟩, ?_⟩
        exact Prod.ext rfl (by omega)
      · rintro ⟨k', ⟨hk', hks, hsk⟩, hpair⟩
        have h1 : k' = k := by simpa using congrArg Prod.fst hpair
        have h2 : s - k' = p := by simpa using congrArg Prod.snd hpair
        subst h1
        subst h2
        refine ⟨⟨⟨hk', ?_⟩, ?_⟩, ?_⟩
        · omega
        · rw [show k' + (s - k') = s by omega]
          exact hsmod
        · omega
    have hinj : ∀ s, ∀ x ∈ PP s, ∀ y ∈ PP s, (x, s - x) = (y, s - y) → x = y := by
      intro s x _ y _ h
      exact (Prod.mk.injEq x (s-x) y (s-y)).mp h |>.1
    have hsumfib : ∑ kp ∈ S, g kp = ∑ s ∈ E, (∑ k ∈ PP s, W k * W (s-k)) * u^s := by
      rw [← Finset.sum_fiberwise_of_maps_to (f := g) hmaps]
      apply Finset.sum_congr rfl
      intro s hs
      rw [hfiber s (hEmod s hs)]
      rw [Finset.sum_image (g := fun k => (k, s - k)) (hinj s)]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      have hks : k ≤ s := by
        simp only [PP, Finset.mem_filter] at hk
        exact hk.2.1
      simp only [g]
      rw [show k + (s - k) = s by omega]
    have hEsum : ∑ s ∈ E, (∑ k ∈ PP s, W k * W (s-k)) * u^s =
        BB n * u^n + ∑ h ∈ Finset.Icc 1 (n/q),
          (BB (n+h*q) * u^(n+h*q) + BB (n-h*q) * u^(n-h*q)) := by
      have hn1 : n ∉ (Finset.Icc 1 (n/q)).image (fun h => n + h*q) := by
        simp only [Finset.mem_image, Finset.mem_Icc]
        rintro ⟨h, ⟨h1, h2⟩, hh⟩
        have hq0 : 0 < h*q := Nat.mul_pos (by omega) hq
        have hgt : n < n + h*q := Nat.lt_add_of_pos_right hq0
        omega
      have hn2 : n ∉ (Finset.Icc 1 (n/q)).image (fun h => n - h*q) := by
        simp only [Finset.mem_image, Finset.mem_Icc]
        rintro ⟨h, ⟨h1, h2⟩, hh⟩
        have hq0 : 0 < h*q := Nat.mul_pos (by omega) hq
        have hqn : h*q ≤ n := (Nat.le_div_iff_mul_le hq).mp h2
        omega
      have hdisj : Disjoint ((Finset.Icc 1 (n/q)).image (fun h => n + h*q))
          ((Finset.Icc 1 (n/q)).image (fun h => n - h*q)) := by
        rw [Finset.disjoint_left]
        intro s h1 h2
        simp only [Finset.mem_image, Finset.mem_Icc] at h1 h2
        obtain ⟨a, ⟨ha1, ha2⟩, rfl⟩ := h1
        obtain ⟨b, ⟨hb1, hb2⟩, hb⟩ := h2
        have hbq : 0 < b*q := Nat.mul_pos (by omega) hq
        have hbqn : b*q ≤ n := (Nat.le_div_iff_mul_le hq).mp hb2
        have hle : n ≤ n + a*q := Nat.le_add_right n (a*q)
        omega
      have hinjA : ∀ x ∈ Finset.Icc 1 (n/q), ∀ y ∈ Finset.Icc 1 (n/q),
          n + x*q = n + y*q → x = y := by
        intro x _ y _ h
        have h2 : x*q = y*q := Nat.add_left_cancel h
        exact Nat.mul_right_cancel hq h2
      have hinjB : ∀ x ∈ Finset.Icc 1 (n/q), ∀ y ∈ Finset.Icc 1 (n/q),
          n - x*q = n - y*q → x = y := by
        intro x hx y hy h
        simp only [Finset.mem_Icc] at hx hy
        have hxq : x*q ≤ n := (Nat.le_div_iff_mul_le hq).mp hx.2
        have hyq : y*q ≤ n := (Nat.le_div_iff_mul_le hq).mp hy.2
        have h2 : x*q = y*q := by omega
        exact Nat.mul_right_cancel hq h2
      simp only [E]
      rw [Finset.sum_insert (by simp only [Finset.mem_union]; tauto)]
      rw [Finset.sum_union hdisj]
      rw [Finset.sum_image (g := fun h => n + h*q) hinjA]
      rw [Finset.sum_image (g := fun h => n - h*q) hinjB]
      simp only [BB]
      rw [← Finset.sum_add_distrib]
    have hLHS1 : u^n*(BB n + ∑ h ∈ Finset.Icc 1 (n/q),
        (BB (n+h*q)*(u^q)^h + BB (n-h*q)*((u^q)⁻¹)^h)) =
        BB n * u^n + ∑ h ∈ Finset.Icc 1 (n/q),
          (BB (n+h*q) * u^(n+h*q) + BB (n-h*q) * u^(n-h*q)) := by
      have hcomm : u^n * BB n = BB n * u^n := by ring
      have hterm : ∀ h ∈ Finset.Icc 1 (n/q),
          u^n * (BB (n+h*q)*(u^q)^h + BB (n-h*q)*((u^q)⁻¹)^h) =
          (BB (n+h*q) * u^(n+h*q) + BB (n-h*q) * u^(n-h*q)) := by
        intro h hh
        have hh2 : h ≤ n/q := (Finset.mem_Icc.mp hh).2
        have hqh : q*h ≤ n := by
          rw [mul_comm q h]
          exact (Nat.le_div_iff_mul_le hq).mp hh2
        have hp1 : u^n * (u^q)^h = u^(n + h*q) := by
          rw [← pow_mul, ← pow_add]
          congr 1
          ring
        have hp2 : u^n * ((u^q)⁻¹)^h = u^(n - h*q) := by
          rw [show ((u^q)⁻¹)^h = ((u^q)^h)⁻¹ from inv_pow (u^q) h, ← pow_mul]
          have hnez : u^(q*h) ≠ 0 := pow_ne_zero _ hu
          have hsplit : u^n = u^(n - q*h) * u^(q*h) := by
            rw [← pow_add]
            congr 1
            omega
          rw [hsplit, mul_assoc, mul_inv_cancel₀ hnez, mul_one, mul_comm q h]
        rw [mul_add]
        congr 1
        · rw [show u^n * (BB (n+h*q) * (u^q)^h) = BB (n+h*q) * (u^n * (u^q)^h) from by ring, hp1]
        · rw [show u^n * (BB (n-h*q) * ((u^q)⁻¹)^h) = BB (n-h*q) * (u^n * ((u^q)⁻¹)^h) from by ring, hp2]
      calc u^n*(BB n + ∑ h ∈ Finset.Icc 1 (n/q),
            (BB (n+h*q)*(u^q)^h + BB (n-h*q)*((u^q)⁻¹)^h))
          = u^n * BB n + u^n * ∑ h ∈ Finset.Icc 1 (n/q),
              (BB (n+h*q)*(u^q)^h + BB (n-h*q)*((u^q)⁻¹)^h) := by rw [mul_add]
        _ = BB n * u^n + ∑ h ∈ Finset.Icc 1 (n/q),
              (BB (n+h*q) * u^(n+h*q) + BB (n-h*q) * u^(n-h*q)) := by
            rw [hcomm, Finset.mul_sum, Finset.sum_congr rfl hterm]
    exact hLHS1.trans (hEsum.symm.trans (hsumfib.symm.trans hR.symm))
  have hB : ∀ s : ℕ,
      ((∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s - k ≤ n),
          (if k.Prime then Real.log (k:ℝ) else 0) *
            (if (s-k).Prime then Real.log ((↑(s - k)) : ℝ) else 0) : ℝ) : ℂ) =
      ∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s - k ≤ n),
        Complex.ofReal (if k.Prime then Real.log (k:ℝ) else 0) *
          Complex.ofReal (if (s-k).Prime then Real.log ((↑(s - k)) : ℝ) else 0) := by
    intro s
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Complex.ofReal_mul]
  have hkey := key (fun k => Complex.ofReal (if k.Prime then Real.log (k:ℝ) else 0)) n q u hq hu
  have hkey := key (fun k => ((if k.Prime then Real.log (k:ℝ) else 0) : ℂ)) n q u hq hu
  have hpush : ∀ k : ℕ,
      Complex.ofReal (if k.Prime then Real.log (k:ℝ) else 0) =
        (if k.Prime then Complex.ofReal (Real.log (k:ℝ)) else 0) := by
    intro k
    split_ifs <;> simp
  dsimp only at hkey
  simp only [hB, hpush]
  exact hkey
