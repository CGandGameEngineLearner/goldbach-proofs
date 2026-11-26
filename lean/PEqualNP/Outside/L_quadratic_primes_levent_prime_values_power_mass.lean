import Mathlib

private lemma not_sq_succ (n : ℕ) (hn : 1 ≤ n) : ∀ q : ℕ, n^2 + 1 ≠ q^2 := by
  intro q h
  have h1 : n < q := by
    by_contra hc
    have hc' : q ≤ n := Nat.le_of_not_lt hc
    have hle : q^2 ≤ n^2 := Nat.pow_le_pow_left hc' 2
    omega
  have h2 : (n+1)^2 ≤ q^2 := Nat.pow_le_pow_left (by omega : n + 1 ≤ q) 2
  have h3 : (n+1)^2 = n^2 + 2*n + 1 := by ring
  rw [h3] at h2
  omega

private lemma prime_pow_structure (x n : ℕ) (hn : n ∈ Finset.Ioc x (2*x))
    (hne : ArithmeticFunction.vonMangoldt (n^2+1) ≠ 0) (hnp : ¬ (n^2+1).Prime) :
    ∃ p k : ℕ, p.Prime ∧ Odd k ∧ 3 ≤ k ∧ n^2+1 = p^k ∧ p^3 ≤ (2*x)^2+1 := by
  obtain ⟨hxn, hn2x⟩ := Finset.mem_Ioc.mp hn
  have hn1 : 1 ≤ n := by omega
  obtain ⟨p, k, hp, hk, hpk⟩ :=
    (isPrimePow_nat_iff (n^2+1)).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hne)
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [pow_one] at hpk
    exact hnp (hpk ▸ hp)
  have hk2 : 2 ≤ k := by omega
  have hkodd : Odd k := by
    rcases Nat.even_or_odd k with he | ho
    · exfalso
      obtain ⟨j, hj⟩ := he
      have hsq : n^2 + 1 = (p^j)^2 := by
        rw [← hpk, hj, pow_add, pow_two]
      exact not_sq_succ n hn1 (p^j) hsq
    · exact ho
  have hk3 : 3 ≤ k := by
    obtain ⟨j, hj⟩ := hkodd
    omega
  refine ⟨p, k, hp, hkodd, hk3, hpk.symm, ?_⟩
  have h1 : p^3 ≤ p^k := Nat.pow_le_pow_right hp.pos hk3
  have h2 : n^2 + 1 ≤ (2*x)^2 + 1 := by
    have hle : n ≤ 2*x := hn2x
    have := Nat.pow_le_pow_left hle 2
    omega
  calc p^3 ≤ p^k := h1
    _ = n^2 + 1 := hpk
    _ ≤ (2*x)^2 + 1 := h2

private lemma card_bound (x : ℕ) :
    ((Finset.Ioc x (2*x)).filter
        (fun n => ¬ (n^2+1).Prime ∧ ArithmeticFunction.vonMangoldt (n^2+1) ≠ 0)).card
      ≤ 2 ^ (Nat.log 8 ((2*x)^2+1) + 1) * (Nat.log 2 ((2*x)^2+1) + 1) := by
  classical
  rcases Nat.eq_zero_or_pos x with hx0 | hxpos
  · subst hx0
    simp
  set M := (2*x)^2+1 with hMdef
  set J := Nat.log 8 M with hJdef
  set K := Nat.log 2 M with hKdef
  set S := (Finset.Ioc x (2*x)).filter
      (fun n => ¬ (n^2+1).Prime ∧ ArithmeticFunction.vonMangoldt (n^2+1) ≠ 0) with hSdef
  have hlt : M < 8 ^ (J+1) := by
    have h := Nat.lt_pow_succ_log_self (show 1 < 8 by norm_num) M
    simpa [hJdef, Nat.succ_eq_add_one] using h
  let f : ℕ → ℕ × ℕ := fun n =>
    if h : ∃ p k : ℕ, p.Prime ∧ Odd k ∧ 3 ≤ k ∧ n^2+1 = p^k ∧ p^3 ≤ (2*x)^2+1
    then (h.choose, h.choose_spec.choose) else (0,0)
  have hspec : ∀ n ∈ S, (f n).1.Prime ∧ Odd (f n).2 ∧ 3 ≤ (f n).2 ∧ n^2+1 = (f n).1^(f n).2
      ∧ (f n).1^3 ≤ (2*x)^2+1 := by
    intro n hn
    simp only [hSdef, Finset.mem_filter] at hn
    obtain ⟨hbase, hnp, hne⟩ := hn
    obtain ⟨p, k, hp, hkodd, hk3, hpk, hp3⟩ := prime_pow_structure x n hbase hne hnp
    have hex : ∃ p k : ℕ, p.Prime ∧ Odd k ∧ 3 ≤ k ∧ n^2+1 = p^k ∧ p^3 ≤ (2*x)^2+1 :=
      ⟨p, k, hp, hkodd, hk3, hpk, hp3⟩
    have heq : f n = (hex.choose, hex.choose_spec.choose) := by
      simp only [f]
      rw [dif_pos hex]
    rw [heq]
    exact hex.choose_spec.choose_spec
  have hleM : ∀ n ∈ S, n^2+1 ≤ M := by
    intro n hn
    simp only [hSdef, Finset.mem_filter] at hn
    have hn2x : n ≤ 2*x := (Finset.mem_Ioc.mp hn.1).2
    have := Nat.pow_le_pow_left hn2x 2
    simp only [hMdef]
    omega
  have hfst : ∀ n ∈ S, (f n).1 < 2^(J+1) := by
    intro n hn
    have h := hspec n hn
    by_contra hc
    have hc' : 2^(J+1) ≤ (f n).1 := Nat.le_of_not_lt hc
    have hcube : (2^(J+1))^3 ≤ (f n).1^3 := Nat.pow_le_pow_left hc' 3
    have h8 : (2^(J+1))^3 = 8^(J+1) := by
      have h1 : (2^(J+1))^3 = 2^((J+1)*3) := (pow_mul 2 (J+1) 3).symm
      have h2 : (8:ℕ)^(J+1) = 2^(3*(J+1)) := by
        rw [show (8:ℕ) = 2^3 from by norm_num, pow_mul]
      rw [h1, h2, Nat.mul_comm]
    have hlt8 : 8^(J+1) ≤ M := by
      rw [h8] at hcube
      exact le_trans hcube (le_trans h.2.2.2.2 (le_of_eq hMdef))
    omega
  have hsnd : ∀ n ∈ S, (f n).2 < K+1 := by
    intro n hn
    have h := hspec n hn
    have hp2 : 2 ≤ (f n).1 := h.1.two_le
    have h2k : 2^(f n).2 ≤ (f n).1^(f n).2 := Nat.pow_le_pow_left hp2 _
    have hM : 2^(f n).2 ≤ M := by
      rw [← h.2.2.2.1] at h2k
      exact le_trans h2k (hleM n hn)
    have := Nat.le_log_of_pow_le (show 1 < 2 by norm_num) hM
    omega
  have hinj : (S : Set ℕ).InjOn f := by
    intro n1 h1 n2 h2 heq
    have e1 : n1^2+1 = (f n1).1^(f n1).2 := (hspec n1 h1).2.2.2.1
    have e2 : n2^2+1 = (f n2).1^(f n2).2 := (hspec n2 h2).2.2.2.1
    have hsq : n1^2 = n2^2 := by
      have h0 : n1^2+1 = n2^2+1 := by rw [e1, heq, ← e2]
      omega
    nlinarith
  calc S.card ≤ ((Finset.range (2^(J+1))) ×ˢ (Finset.range (K+1))).card := by
        apply Finset.card_le_card_of_injOn f _ hinj
        intro n hn
        rw [Finset.mem_coe] at hn
        rw [Finset.mem_coe, Finset.mem_product]
        exact ⟨Finset.mem_range.mpr (hfst n hn), Finset.mem_range.mpr (hsnd n hn)⟩
    _ = 2^(J+1) * (K+1) := by rw [Finset.card_product]; simp

private lemma pp_bound (x : ℕ) :
    (∑ n ∈ (Finset.Ioc x (2*x)).filter (fun n => ¬ (n^2+1).Prime),
        ArithmeticFunction.vonMangoldt (n^2+1))
      ≤ (((Finset.Ioc x (2*x)).filter
            (fun n => ¬ (n^2+1).Prime ∧ ArithmeticFunction.vonMangoldt (n^2+1) ≠ 0)).card : ℝ)
        * Real.log (((2*x)^2+1 : ℕ) : ℝ) := by
  classical
  set M := ((2*x)^2+1 : ℕ) with hMdef
  set S := (Finset.Ioc x (2*x)).filter
      (fun n => ¬ (n^2+1).Prime ∧ ArithmeticFunction.vonMangoldt (n^2+1) ≠ 0) with hSdef
  set T := (Finset.Ioc x (2*x)).filter (fun n => ¬ (n^2+1).Prime) with hTdef
  have hsub : S ⊆ T := by
    intro n hn
    simp only [hSdef, hTdef, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1⟩
  have hzero : ∀ n ∈ T, n ∉ S → ArithmeticFunction.vonMangoldt (n^2+1) = 0 := by
    intro n hn hnS
    by_contra h
    refine hnS ?_
    have hn' : n ∈ Finset.Ioc x (2*x) ∧ ¬ (n^2+1).Prime := by
      simpa [hTdef, Finset.mem_filter] using hn
    simp only [hSdef, Finset.mem_filter]
    exact ⟨hn'.1, hn'.2, h⟩
  rw [← Finset.sum_subset hsub hzero]
  have hterm : ∀ n ∈ S, ArithmeticFunction.vonMangoldt (n^2+1) ≤ Real.log (M : ℝ) := by
    intro n hn
    have hnT : n ∈ T := hsub hn
    simp only [hTdef, Finset.mem_filter, Finset.mem_Ioc] at hnT
    have hn2x : n ≤ 2*x := hnT.1.2
    have h1 : ArithmeticFunction.vonMangoldt (n^2+1) ≤ Real.log ((n^2+1 : ℕ) : ℝ) :=
      ArithmeticFunction.vonMangoldt_le_log
    have hnat : n^2+1 ≤ M := by
      have := Nat.pow_le_pow_left hn2x 2
      simp only [hMdef]
      omega
    have h2 : ((n^2+1 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hnat
    have h3 : (0:ℝ) < ((n^2+1 : ℕ) : ℝ) := by positivity
    exact le_trans h1 (Real.log_le_log h3 h2)
  calc ∑ n ∈ S, ArithmeticFunction.vonMangoldt (n^2+1)
      ≤ ∑ n ∈ S, Real.log (M : ℝ) := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * Real.log (M : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]

theorem PEqualNP.Outside.L_quadratic_primes_levent_prime_values_power_mass :
    let block := fun x : ℕ => Finset.Ioc x (2*x); let pp := fun x : ℕ => ∑ n ∈ (block x).filter (fun n => ¬ Nat.Prime (n^2+1)), ArithmeticFunction.vonMangoldt (n^2+1); ∀ ε : ℝ, 0<ε → ∃ X : ℕ, ∀ x ≥ X, pp x ≤ ε*x := by
  dsimp only
  intro ε hε
  have hδ : (0:ℝ) < ε^3/(55^3*72) := by positivity
  have hlog : ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y → Real.log y ^ 6 ≤ (ε^3/(55^3*72)) * y := by
    have hlit := isLittleO_log_rpow_rpow_atTop (r := (6:ℝ)) (s := (1:ℝ)) one_pos
    have hb : ∀ᶠ y : ℝ in Filter.atTop, ‖Real.log y ^ (6:ℝ)‖ ≤ (ε^3/(55^3*72)) * ‖y ^ (1:ℝ)‖ :=
      hlit.bound hδ
    have hb' : ∀ᶠ y : ℝ in Filter.atTop, Real.log y ^ 6 ≤ (ε^3/(55^3*72)) * y := by
      filter_upwards [hb, Filter.eventually_ge_atTop (1:ℝ)] with y hy hy1
      have hl : (0:ℝ) ≤ Real.log y := Real.log_nonneg hy1
      have hy' : ‖Real.log y ^ 6‖ ≤ (ε^3/(55^3*72)) * ‖y‖ := by simpa using hy
      rw [Real.norm_of_nonneg (pow_nonneg hl 6), Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ y)] at hy'
      exact hy'
    exact Filter.eventually_atTop.1 hb'
  obtain ⟨Y, hY⟩ := hlog
  refine ⟨max (Nat.ceil Y) 9, fun x hx => ?_⟩
  have hx9 : 9 ≤ x := le_trans (le_max_right _ _) hx
  have hxY : Y ≤ (x : ℝ) := by
    have h1 : Nat.ceil Y ≤ x := le_trans (le_max_left _ _) hx
    exact le_trans (Nat.le_ceil Y) (by exact_mod_cast h1)
  have hxR : (9:ℝ) ≤ (x : ℝ) := by exact_mod_cast hx9
  have hxpos : (0:ℝ) < (x : ℝ) := by linarith
  set L := Real.log (x : ℝ) with hLdef
  have hL1 : 1 ≤ L := by
    have h9 : Real.log (9:ℝ) ≤ Real.log (x:ℝ) := Real.log_le_log (by norm_num) hxR
    have h9eq : Real.log (9:ℝ) = 2 * Real.log 3 := by
      rw [show (9:ℝ) = 3^2 from by norm_num, Real.log_pow]
      push_cast
      ring
    have h23 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
    have h2 : (0.69:ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    rw [h9eq] at h9
    rw [hLdef]
    linarith
  have hL0 : 0 ≤ L := by linarith
  set M := ((2*x)^2+1 : ℕ) with hMdef
  set J := Nat.log 8 M with hJdef
  set K := Nat.log 2 M with hKdef
  have hM0 : M ≠ 0 := by simp [hMdef]
  -- log M ≤ 5 L
  have hlogM : Real.log (M : ℝ) ≤ 5 * L := by
    have hMle : (M : ℝ) ≤ 9 * (x:ℝ)^2 := by
      have h1 : (M : ℝ) = 4*(x:ℝ)^2 + 1 := by
        simp only [hMdef]
        push_cast
        ring
      nlinarith
    have hMpos : (0:ℝ) < (M:ℝ) := by
      have : 0 < M := by simp [hMdef]
      exact_mod_cast this
    have h1 : Real.log (M:ℝ) ≤ Real.log (9 * (x:ℝ)^2) := Real.log_le_log hMpos hMle
    have h2 : Real.log (9 * (x:ℝ)^2) = Real.log 9 + 2 * L := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      rw [hLdef]
      push_cast
      ring
    have h3 : Real.log 9 ≤ 3 * L := by
      have h9 : Real.log (9:ℝ) = 2 * Real.log 3 := by
        rw [show (9:ℝ) = 3^2 from by norm_num, Real.log_pow]
        push_cast
        ring
      have h23 : Real.log 3 ≤ Real.log (x:ℝ) := Real.log_le_log (by norm_num) (by linarith)
      rw [h9]
      nlinarith
    linarith
  -- K bound
  have hKb : (K : ℝ) ≤ 10 * L := by
    have hpK : (2:ℝ)^K ≤ (M:ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hM0
    have h1 : (K:ℝ) * Real.log 2 ≤ Real.log (M:ℝ) := by
      have h := Real.log_le_log (by norm_num) hpK
      rw [Real.log_pow] at h
      exact h
    have h2 : (0.69:ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hK0 : (0:ℝ) ≤ (K:ℝ) := by positivity
    nlinarith
  -- a bound
  have ha3 : ((2^(J+1) : ℕ) : ℝ)^3 ≤ 72 * (x:ℝ)^2 := by
    have h1 : ((2^(J+1) : ℕ) : ℝ)^3 = ((8^(J+1) : ℕ) : ℝ) := by
      rw [← Nat.cast_pow]
      have h8 : (2^(J+1))^3 = 8^(J+1) := by
        have h1 : (2^(J+1))^3 = 2^((J+1)*3) := (pow_mul 2 (J+1) 3).symm
        have h2 : (8:ℕ)^(J+1) = 2^(3*(J+1)) := by
          rw [show (8:ℕ) = 2^3 from by norm_num, pow_mul]
        rw [h1, h2, Nat.mul_comm]
      rw [h8]
    have h2 : ((8^(J+1) : ℕ) : ℝ) ≤ 8 * (M:ℝ) := by
      have hlt : M < 8 ^ (J+1) := by
        have h := Nat.lt_pow_succ_log_self (show 1 < 8 by norm_num) M
        simpa [hJdef, Nat.succ_eq_add_one] using h
      have hle : (8:ℕ)^J ≤ M := Nat.pow_log_le_self 8 hM0
      have h3 : ((8^(J+1) : ℕ) : ℝ) = 8 * ((8^J : ℕ) : ℝ) := by
        rw [pow_succ']
        push_cast
        ring
      rw [h3]
      have : ((8^J : ℕ) : ℝ) ≤ (M:ℝ) := by exact_mod_cast hle
      nlinarith
    have h4 : 8 * ((M:ℝ)) ≤ 72 * (x:ℝ)^2 := by
      have h1 : (M : ℝ) = 4*(x:ℝ)^2 + 1 := by
        simp only [hMdef]
        push_cast
        ring
      nlinarith
    rw [h1]
    linarith
  -- assemble
  set A := ((Finset.Ioc x (2*x)).filter
      (fun n => ¬ Nat.Prime (n^2+1) ∧ ArithmeticFunction.vonMangoldt (n^2+1) ≠ 0)).card with hA
  set P := (∑ n ∈ (Finset.Ioc x (2*x)).filter (fun n => ¬ Nat.Prime (n^2+1)),
      ArithmeticFunction.vonMangoldt (n^2+1)) with hP
  have hpp : P ≤ (A : ℝ) * Real.log (M : ℝ) := by
    rw [hP, hA]
    exact pp_bound x
  have hcb' : A ≤ 2^(J+1) * (K+1) := by
    rw [hA]
    have hcb := card_bound x
    simpa [hJdef, hMdef, hKdef] using hcb
  have hcardR : (A : ℝ) ≤ ((2^(J+1) : ℕ) : ℝ) * ((K + 1 : ℕ) : ℝ) := by
    have h1 : (A : ℝ) ≤ ((2^(J+1) * (K+1) : ℕ) : ℝ) := Nat.cast_le.mpr hcb'
    calc (A : ℝ) ≤ ((2^(J+1) * (K+1) : ℕ) : ℝ) := h1
      _ = ((2^(J+1) : ℕ) : ℝ) * ((K + 1 : ℕ) : ℝ) := by push_cast; ring
  have hlogM0 : 0 ≤ Real.log (M:ℝ) := by
    have h1 : (1:ℝ) ≤ (M:ℝ) := by
      have h2 : 1 ≤ M := by simp [hMdef]
      exact_mod_cast h2
    exact Real.log_nonneg h1
  have hbR : ((K + 1 : ℕ) : ℝ) ≤ 11 * L := by
    have h1 : ((K + 1 : ℕ) : ℝ) = (K:ℝ) + 1 := by push_cast; ring
    rw [h1]
    linarith
  have haR0 : (0:ℝ) ≤ ((2^(J+1) : ℕ) : ℝ) := by positivity
  have hstep1 : (A : ℝ) * Real.log (M:ℝ) ≤ (((2^(J+1) : ℕ) : ℝ) * ((K + 1 : ℕ) : ℝ)) * Real.log (M:ℝ) :=
    mul_le_mul_of_nonneg_right hcardR hlogM0
  have hstep2 : (((2^(J+1) : ℕ) : ℝ) * ((K + 1 : ℕ) : ℝ)) * Real.log (M:ℝ)
      ≤ ((2^(J+1) : ℕ) : ℝ) * (11*L) * (5*L) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hbR haR0
    · exact hlogM
    · exact hlogM0
    · have h2 : (0:ℝ) ≤ 11 * L := by linarith
      exact mul_nonneg haR0 h2
  have hpp2 : P ≤ ((2^(J+1) : ℕ) : ℝ) * (11*L) * (5*L) := le_trans (le_trans hpp hstep1) hstep2
  have hpp2' : P ≤ 55 * ((2^(J+1) : ℕ) : ℝ) * L^2 := by
    have he : ((2^(J+1) : ℕ) : ℝ) * (11*L) * (5*L) = 55 * ((2^(J+1) : ℕ) : ℝ) * L^2 := by ring
    rw [he] at hpp2
    exact hpp2
  have hnonneg : (0:ℝ) ≤ P := by
    rw [hP]
    exact Finset.sum_nonneg (fun n _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hL6 : L^6 ≤ (ε^3/(55^3*72)) * (x:ℝ) := hY (x:ℝ) hxY
  have h66 : ((2^(J+1) : ℕ) : ℝ)^3 * L^6 ≤ (72 * (x:ℝ)^2) * ((ε^3/(55^3*72)) * (x:ℝ)) := by
    apply mul_le_mul ha3 hL6 (by positivity) (by positivity)
  have hbound : (55 * ((2^(J+1) : ℕ) : ℝ) * L^2)^3 ≤ (ε * (x:ℝ))^3 := by
    have hexp : (55 * ((2^(J+1) : ℕ) : ℝ) * L^2)^3 = 55^3 * (((2^(J+1) : ℕ) : ℝ)^3 * L^6) := by ring
    rw [hexp]
    have h2 : 55^3 * (((2^(J+1) : ℕ) : ℝ)^3 * L^6)
        ≤ 55^3 * ((72 * (x:ℝ)^2) * ((ε^3/(55^3*72)) * (x:ℝ))) :=
      mul_le_mul_of_nonneg_left h66 (by positivity)
    have hconst : (55:ℝ)^3 * (72 * (ε^3/(55^3*72))) = ε^3 := by
      have h55 : (55:ℝ)^3 ≠ 0 := by norm_num
      field_simp
    have h3 : 55^3 * ((72 * (x:ℝ)^2) * ((ε^3/(55^3*72)) * (x:ℝ))) = (ε * (x:ℝ))^3 := by
      calc 55^3 * ((72 * (x:ℝ)^2) * ((ε^3/(55^3*72)) * (x:ℝ)))
          = (55^3 * (72 * (ε^3/(55^3*72)))) * ((x:ℝ)^2 * (x:ℝ)) := by ring
        _ = ε^3 * ((x:ℝ)^2 * (x:ℝ)) := by rw [hconst]
        _ = (ε * (x:ℝ))^3 := by ring
    linarith [h2, h3]
  have hpp3 : P^3 ≤ (55 * ((2^(J+1) : ℕ) : ℝ) * L^2)^3 := pow_le_pow_left₀ hnonneg hpp2' 3
  have hcube : P^3 ≤ (ε * (x:ℝ))^3 := le_trans hpp3 hbound
  have hεx0 : (0:ℝ) ≤ ε * (x:ℝ) := by positivity
  exact (pow_le_pow_iff_left₀ hnonneg hεx0 (by norm_num : (3:ℕ) ≠ 0)).mp hcube
