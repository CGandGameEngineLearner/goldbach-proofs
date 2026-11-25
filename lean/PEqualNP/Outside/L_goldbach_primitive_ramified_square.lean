import Mathlib

theorem PEqualNP.Outside.L_goldbach_primitive_ramified_square :
    ∀ n : ℕ, 2≤n → (∑ k ∈ (Finset.range (n+1)).filter (fun k => n≤3*k ∧ 3*k≤2*n ∧ ¬k.Coprime n), (ArithmeticFunction.vonMangoldt k)^2) ≤ 2*(Real.log (n:ℝ))^2 := by
  intro n hn
  classical
  have hnpos : 0 < n := by omega
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hnpos
  have hR2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  set S : Finset ℕ := (Finset.range (n+1)).filter (fun k => n ≤ 3*k ∧ 3*k ≤ 2*n ∧ ¬k.Coprime n) with hS
  set T : Finset ℕ := S.filter (fun k => IsPrimePow k) with hT
  have hmemS : ∀ k, k ∈ S ↔ k < n+1 ∧ n ≤ 3*k ∧ 3*k ≤ 2*n ∧ ¬k.Coprime n := by
    intro k; rw [hS]; simp [Finset.mem_range, and_assoc]
  have hmemT : ∀ k, k ∈ T ↔ k ∈ S ∧ IsPrimePow k := by
    intro k; rw [hT]; simp
  have hkfacts : ∀ k ∈ T, 2 ≤ k ∧ k ≤ n := by
    intro k hk
    obtain ⟨hkS, -⟩ := (hmemT k).1 hk
    obtain ⟨hkn, h1, h2, h3⟩ := (hmemS k).1 hkS
    have hk2 : k ≠ 1 := by
      intro h; subst h; exact h3 (Nat.coprime_one_left n)
    omega
  have hminfac : ∀ k ∈ T, (Nat.minFac k).Prime ∧ Nat.minFac k ∣ k ∧ 2 ≤ Nat.minFac k ∧ Nat.minFac k ≤ n := by
    intro k hk
    obtain ⟨hk2, hkn⟩ := hkfacts k hk
    have hprime : (Nat.minFac k).Prime := Nat.minFac_prime (by omega)
    have hdvd : Nat.minFac k ∣ k := Nat.minFac_dvd k
    have hge2 : 2 ≤ Nat.minFac k := hprime.two_le
    have hle : Nat.minFac k ≤ k := Nat.le_of_dvd (by omega) hdvd
    exact ⟨hprime, hdvd, hge2, by omega⟩
  have hpow : ∀ k ∈ T, ∃ e : ℕ, 1 ≤ e ∧ k = (Nat.minFac k)^e := by
    intro k hk
    obtain ⟨-, hpp⟩ := (hmemT k).1 hk
    obtain ⟨q, e, hq, he, hkq⟩ := hpp
    have hmin : Nat.minFac k = q := by
      rw [← hkq, Nat.pow_minFac he.ne', Nat.Prime.minFac_eq (Nat.prime_iff.mpr hq)]
    exact ⟨e, he, by rw [hmin]; exact hkq.symm⟩
  have hwin : ∀ k ∈ T, n ≤ 3*k ∧ 3*k ≤ 2*n := by
    intro k hk
    obtain ⟨hkS, -⟩ := (hmemT k).1 hk
    obtain ⟨-, h1, h2, -⟩ := (hmemS k).1 hkS
    exact ⟨h1, h2⟩
  have hA : (∑ k ∈ S, (ArithmeticFunction.vonMangoldt k)^2) = ∑ k ∈ T, (ArithmeticFunction.vonMangoldt k)^2 := by
    have h1 : (∑ k ∈ S, (if IsPrimePow k then (ArithmeticFunction.vonMangoldt k)^2 else 0))
        = ∑ k ∈ S.filter (fun k => IsPrimePow k), (ArithmeticFunction.vonMangoldt k)^2 :=
      (Finset.sum_filter (s := S) (p := fun k => IsPrimePow k)
        (f := fun k => (ArithmeticFunction.vonMangoldt k)^2)).symm
    have h2 : (∑ k ∈ S.filter (fun k => IsPrimePow k), (ArithmeticFunction.vonMangoldt k)^2)
        = ∑ k ∈ T, (ArithmeticFunction.vonMangoldt k)^2 := by rw [hT]
    have h3 : (∑ k ∈ S, (if IsPrimePow k then (ArithmeticFunction.vonMangoldt k)^2 else 0))
        = ∑ k ∈ S, (ArithmeticFunction.vonMangoldt k)^2 := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      by_cases hp : IsPrimePow k
      · simp [hp]
      · simp [hp, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hp]
    rw [← h3, h1, h2]
  have hmain : ∑ k ∈ T, (ArithmeticFunction.vonMangoldt k)^2 ≤ 2*(Real.log (n:ℝ))^2 := by
    have hstep1 : ∑ k ∈ T, (ArithmeticFunction.vonMangoldt k)^2 = ∑ k ∈ T, (Real.log (Nat.minFac k))^2 := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [ArithmeticFunction.vonMangoldt_apply, if_pos ((hmemT k).1 hk).2]
    rw [hstep1]
    have hlogbound : ∀ k ∈ T, (Real.log (Nat.minFac k))^2 ≤ Real.log n * Real.log (Nat.minFac k) := by
      intro k hk
      obtain ⟨-, -, hge2, hle⟩ := hminfac k hk
      have hpos : (0:ℝ) < (Nat.minFac k : ℝ) := by exact_mod_cast (by omega : 0 < Nat.minFac k)
      have h1 : Real.log (Nat.minFac k) ≤ Real.log n := Real.log_le_log hpos (by exact_mod_cast hle)
      have h0 : 0 ≤ Real.log (Nat.minFac k) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Nat.minFac k))
      nlinarith [h1, h0]
    have hfibercard : ∀ p ∈ n.primeFactors, (T.filter (fun k => Nat.minFac k = p)).card ≤ 2 := by
      intro p hp
      have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
      have hp2 : 2 ≤ p := hpprime.two_le
      have hp0 : 0 < p := hpprime.pos
      have heq : ∀ k ∈ T.filter (fun k => Nat.minFac k = p), ∃ e, 1 ≤ e ∧ k = p^e := by
        intro k hk
        obtain ⟨hkT, hkp⟩ := Finset.mem_filter.mp hk
        obtain ⟨e, he, hke⟩ := hpow k hkT
        exact ⟨e, he, by simpa [hkp] using hke⟩
      have hgap : ∀ k1 ∈ T.filter (fun k => Nat.minFac k = p),
          ∀ k2 ∈ T.filter (fun k => Nat.minFac k = p),
          ∀ e1 e2, k1 = p^e1 → k2 = p^e2 → e1 < e2 → p^(e2-e1) ≤ 2 := by
        intro k1 hk1 k2 hk2 e1 e2 h1 h2 hlt
        obtain ⟨hk1T, -⟩ := Finset.mem_filter.mp hk1
        obtain ⟨hk2T, -⟩ := Finset.mem_filter.mp hk2
        obtain ⟨hwn1, -⟩ := hwin k1 hk1T
        obtain ⟨-, hwn4⟩ := hwin k2 hk2T
        have hpos : 0 < p^e1 := pow_pos hp0 e1
        have hkey : 3 * p^e2 ≤ 6 * p^e1 := by
          calc 3 * p^e2 = 3 * k2 := by rw [h2]
            _ ≤ 2 * n := hwn4
            _ ≤ 2 * (3 * k1) := Nat.mul_le_mul_left 2 hwn1
            _ = 6 * p^e1 := by rw [h1]; ring
        have hsplit : p^e2 = p^(e2-e1) * p^e1 := by
          rw [← pow_add, Nat.sub_add_cancel (le_of_lt hlt)]
        have h3 : (3 * p^(e2-e1)) * p^e1 ≤ 6 * p^e1 := by
          calc (3 * p^(e2-e1)) * p^e1 = 3 * (p^(e2-e1) * p^e1) := by ring
            _ = 3 * p^e2 := by rw [hsplit]
            _ ≤ 6 * p^e1 := hkey
        have h4 : 3 * p^(e2-e1) ≤ 6 := Nat.le_of_mul_le_mul_right h3 hpos
        omega
      have hno3 : ¬ (3 ≤ (T.filter (fun k => Nat.minFac k = p)).card) := by
        intro h3
        obtain ⟨t, htsub, htcard⟩ := Finset.exists_subset_card_eq h3
        obtain ⟨x, y, z, hxy, hxz, hyz, htx⟩ := Finset.card_eq_three.mp htcard
        have hxF : x ∈ T.filter (fun k => Nat.minFac k = p) :=
          htsub (htx ▸ by simp)
        have hyF : y ∈ T.filter (fun k => Nat.minFac k = p) :=
          htsub (htx ▸ by simp)
        have hzF : z ∈ T.filter (fun k => Nat.minFac k = p) :=
          htsub (htx ▸ by simp)
        obtain ⟨ex, -, hxe⟩ := heq x hxF
        obtain ⟨ey, -, hye⟩ := heq y hyF
        obtain ⟨ez, -, hze⟩ := heq z hzF
        have hxye : ex ≠ ey := by
          intro h
          exact hxy (by rw [hxe, hye, h])
        have hxze : ex ≠ ez := by
          intro h
          exact hxz (by rw [hxe, hze, h])
        have hyze : ey ≠ ez := by
          intro h
          exact hyz (by rw [hye, hze, h])
        have order3 : ∀ a b c : ℕ, a ≠ b → a ≠ c → b ≠ c →
            ∃ u v : ℕ, (u = a ∨ u = b ∨ u = c) ∧ (v = a ∨ v = b ∨ v = c) ∧ u < v ∧ 2 ≤ v - u := by
          intro a b c hab hac hbc
          rcases lt_trichotomy a b with h | h | h
          · rcases lt_trichotomy b c with h2 | h2 | h2
            · exact ⟨a, c, Or.inl rfl, Or.inr (Or.inr rfl), by omega, by omega⟩
            · exact absurd h2 hbc
            · rcases lt_trichotomy a c with h3 | h3 | h3
              · exact ⟨a, b, Or.inl rfl, Or.inr (Or.inl rfl), by omega, by omega⟩
              · exact absurd h3 hac
              · exact ⟨c, b, Or.inr (Or.inr rfl), Or.inr (Or.inl rfl), by omega, by omega⟩
          · exact absurd h hab
          · rcases lt_trichotomy a c with h3 | h3 | h3
            · exact ⟨b, c, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), by omega, by omega⟩
            · exact absurd h3 hac
            · rcases lt_trichotomy b c with h4 | h4 | h4
              · exact ⟨b, a, Or.inr (Or.inl rfl), Or.inl rfl, by omega, by omega⟩
              · exact absurd h4 hbc
              · exact ⟨c, a, Or.inr (Or.inr rfl), Or.inl rfl, by omega, by omega⟩
        obtain ⟨u, v, hu, hv, huv, huv2⟩ := order3 ex ey ez hxye hxze hyze
        have hmemOf : ∀ e : ℕ, (e = ex ∨ e = ey ∨ e = ez) →
            p^e ∈ T.filter (fun k => Nat.minFac k = p) := by
          intro e he
          rcases he with rfl | rfl | rfl
          · rwa [← hxe]
          · rwa [← hye]
          · rwa [← hze]
        have hpu := hmemOf u hu
        have hpv := hmemOf v hv
        have hgapuv := hgap (p^u) hpu (p^v) hpv u v rfl rfl huv
        have hge : 4 ≤ p^(v-u) := by
          have h1 : p^2 ≤ p^(v-u) := pow_le_pow_right' (by omega : 1 ≤ p) huv2
          have h2 : (4:ℕ) ≤ p^2 := by
            calc (4:ℕ) = 2^2 := by norm_num
              _ ≤ p^2 := Nat.pow_le_pow_left hp2 2
          omega
        omega
      by_contra hcon
      exact hno3 (by omega)
    have hfibsum : ∑ k ∈ T, Real.log (Nat.minFac k) ≤ 2 * ∑ p ∈ n.primeFactors, Real.log p := by
      have hmaps : ∀ k ∈ T, Nat.minFac k ∈ n.primeFactors := by
        intro k hk
        obtain ⟨hprime, hdvd, hge2, -⟩ := hminfac k hk
        rw [Nat.mem_primeFactors]
        refine ⟨hprime, ?_, by omega⟩
        obtain ⟨e, he1, hke⟩ := hpow k hk
        obtain ⟨-, -, -, hnc⟩ := (hmemS k).1 ((hmemT k).1 hk).1
        have hnc' : ¬ (Nat.minFac k).Coprime n := by
          intro hc
          exact hnc (by rw [hke]; exact (Nat.coprime_pow_left_iff he1 (Nat.minFac k) n).2 hc)
        by_contra hnp
        exact hnc' ((hprime.coprime_iff_not_dvd).2 hnp)
      have hfib := Finset.sum_fiberwise_of_maps_to (s := T) (t := n.primeFactors)
        (g := fun k => Nat.minFac k) (f := fun k => Real.log (Nat.minFac k)) hmaps
      rw [← hfib, Finset.mul_sum]
      refine Finset.sum_le_sum (fun p hp => ?_)
      have hconst : ∀ k ∈ T.filter (fun k => Nat.minFac k = p), Real.log (Nat.minFac k) = Real.log p := by
        intro k hk
        rw [(Finset.mem_filter.mp hk).2]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
      have hp2 : 2 ≤ p := (Nat.mem_primeFactors.mp hp).1.two_le
      have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
      have hcard' : ((T.filter (fun k => Nat.minFac k = p)).card : ℝ) ≤ 2 := by
        exact_mod_cast hfibercard p hp
      nlinarith
    have hsumlog : ∑ p ∈ n.primeFactors, Real.log p ≤ Real.log n := by
      have hprod : (∏ p ∈ n.primeFactors, (p:ℝ)) ≤ (n:ℝ) := by
        have hd := Nat.prod_primeFactors_dvd n
        have hle : (∏ p ∈ n.primeFactors, p) ≤ n := Nat.le_of_dvd hnpos hd
        calc (∏ p ∈ n.primeFactors, (p:ℝ)) = ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) := by push_cast; ring
          _ ≤ (n:ℝ) := by exact_mod_cast hle
      have hposprod : (0:ℝ) < ∏ p ∈ n.primeFactors, (p:ℝ) := by
        apply Finset.prod_pos
        intro p hp
        have := (Nat.mem_primeFactors.mp hp).1
        exact_mod_cast this.pos
      have hlogprod : Real.log (∏ p ∈ n.primeFactors, (p:ℝ)) = ∑ p ∈ n.primeFactors, Real.log p := by
        rw [Real.log_prod]
        intro p hp
        have := (Nat.mem_primeFactors.mp hp).1
        exact_mod_cast this.pos.ne'
      rw [← hlogprod]
      exact Real.log_le_log hposprod hprod
    have hlogN : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    calc ∑ k ∈ T, (Real.log (Nat.minFac k))^2
        ≤ ∑ k ∈ T, Real.log n * Real.log (Nat.minFac k) := Finset.sum_le_sum hlogbound
      _ = Real.log n * ∑ k ∈ T, Real.log (Nat.minFac k) := by rw [Finset.mul_sum]
      _ ≤ Real.log n * (2 * ∑ p ∈ n.primeFactors, Real.log p) := by
          exact mul_le_mul_of_nonneg_left hfibsum hlogN
      _ ≤ Real.log n * (2 * Real.log n) := by
          exact mul_le_mul_of_nonneg_left (by linarith) hlogN
      _ = 2*(Real.log (n:ℝ))^2 := by ring
  calc (∑ k ∈ (Finset.range (n+1)).filter (fun k => n≤3*k ∧ 3*k≤2*n ∧ ¬k.Coprime n), (ArithmeticFunction.vonMangoldt k)^2)
      = ∑ k ∈ S, (ArithmeticFunction.vonMangoldt k)^2 := by rw [hS]
    _ = ∑ k ∈ T, (ArithmeticFunction.vonMangoldt k)^2 := hA
    _ ≤ 2*(Real.log (n:ℝ))^2 := hmain