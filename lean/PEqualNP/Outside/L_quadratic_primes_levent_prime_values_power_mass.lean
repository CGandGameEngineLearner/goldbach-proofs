import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_prime_values_power_mass :
    let block := fun x : ℕ => Finset.Ioc x (2*x);
    let pp := fun x : ℕ => ∑ n ∈ (block x).filter (fun n => ¬ Nat.Prime (n^2+1)), ArithmeticFunction.vonMangoldt (n^2+1);
    ∀ ε : ℝ, 0<ε → ∃ X : ℕ, ∀ x ≥ X, pp x ≤ ε*x := by
  dsimp only
  intro ε hε
  set pp : ℕ → ℝ := fun x => ∑ n ∈ (Finset.Ioc x (2*x)).filter (fun n => ¬ Nat.Prime (n^2+1)), ArithmeticFunction.vonMangoldt (n^2+1) with hppdef
  change ∃ X : ℕ, ∀ x ≥ X, pp x ≤ ε * (x:ℝ)
  have hlog12 : ∀ t : ℝ, 1 ≤ t → Real.log t ≤ 12 * t^(1/12:ℝ) := by
    intro t ht
    have ht0 : (0:ℝ) < t := by linarith
    have hpos : (0:ℝ) < t^(1/12:ℝ) := Real.rpow_pos_of_pos ht0 _
    have h1 : Real.log (t^(1/12:ℝ)) = (1/12) * Real.log t := Real.log_rpow ht0 _
    have h2 : Real.log (t^(1/12:ℝ)) ≤ t^(1/12:ℝ) - 1 := Real.log_le_sub_one_of_pos hpos
    have h3 : (0:ℝ) ≤ t^(1/12:ℝ) := le_of_lt hpos
    nlinarith
  have hlogbd : ∀ x : ℕ, 2 ≤ x → Real.log ((2*(x:ℝ))^2+1) ≤ 4 * Real.log (2*(x:ℝ)) := by
    intro x hx
    have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
    have h5 : (0:ℝ) < (2*(x:ℝ))^2+1 := by positivity
    have h1 : Real.log ((2*(x:ℝ))^2+1) ≤ Real.log (8*(x:ℝ)^2) := by
      apply Real.log_le_log h5
      nlinarith
    have h2 : Real.log (8*(x:ℝ)^2) = 3*Real.log 2 + 2*Real.log (x:ℝ) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      have h8 : Real.log (8:ℝ) = 3*Real.log 2 := by
        rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
      push_cast
      linarith
    have h3 : Real.log (2*(x:ℝ)) = Real.log 2 + Real.log (x:ℝ) := by
      rw [Real.log_mul (by norm_num) (by linarith)]
    have hlx : (0:ℝ) ≤ Real.log (x:ℝ) := Real.log_nonneg hx1
    have hl2 : (0:ℝ) ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num))
    linarith
  have hcount : ∀ x : ℕ, 2 ≤ x → (((Finset.Ioc x (2*x)).filter (fun n => ArithmeticFunction.vonMangoldt (n^2+1) ≠ 0 ∧ ¬ (n^2+1).Prime)).card : ℝ) ≤ 100*(x : ℝ)^(2/3 : ℝ)*Real.log (2*(x : ℝ)) := by
    intro x hx
    classical
    set S : Finset ℕ := (Finset.Ioc x (2*x)).filter
      (fun n => ArithmeticFunction.vonMangoldt (n^2+1) ≠ 0 ∧ ¬ (n^2+1).Prime) with hS
    set N : ℕ := Nat.floor (((2*(x:ℝ))^2+1)^(1/3:ℝ)) with hN
    set K : ℕ := Nat.log 2 ((2*x)^2+1) with hK
    have hxR : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
    have hx1 : (1:ℝ) ≤ (x:ℝ) := by linarith
    have hx0 : (0:ℝ) ≤ (x:ℝ) := by linarith
    have hsq : ∀ n m : ℕ, n^2 = m^2 → n = m := by
      intro n m h
      rcases Nat.lt_trichotomy n m with h' | h' | h'
      · exfalso
        have : n^2 < m^2 := Nat.pow_lt_pow_left h' (by norm_num)
        omega
      · exact h'
      · exfalso
        have : m^2 < n^2 := Nat.pow_lt_pow_left h' (by norm_num)
        omega
    -- ### Step 1: structure of every member of S
    have hdata : ∀ n ∈ S, ∃ p k : ℕ, p.Prime ∧ 3 ≤ k ∧ n^2+1 = p^k ∧ p ≤ N ∧ k ≤ K := by
      intro n hn
      obtain ⟨hmem, hL, hnp⟩ := Finset.mem_filter.mp hn
      have hn2x : n ≤ 2*x := (Finset.mem_Ioc.mp hmem).2
      have hn1 : 1 ≤ n := by
        have := (Finset.mem_Ioc.mp hmem).1
        omega
      have hIP : IsPrimePow (n^2+1) := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hL
      obtain ⟨k, hklog, hkpos, p, hple, heq, hp⟩ := (isPrimePow_nat_iff_bounded_log (n^2+1)).mp hIP
      have hk1 : k ≠ 1 := by
        intro h1
        apply hnp
        rw [heq, h1, pow_one]
        exact hp
      have hk2 : k ≠ 2 := by
        intro h2
        have hp2 : p^2 = n^2+1 := by
          have h := heq
          rw [h2] at h
          exact h.symm
        have hlt : n < p := by
          rcases Nat.lt_or_ge n p with h' | h'
          · exact h'
          · exfalso
            have hle : p^2 ≤ n^2 := Nat.pow_le_pow_left h' 2
            omega
        have hlt2 : p < n+1 := by
          rcases Nat.lt_or_ge p (n+1) with h' | h'
          · exact h'
          · exfalso
            have hle : (n+1)^2 ≤ p^2 := Nat.pow_le_pow_left h' 2
            nlinarith
        omega
      have hk3 : 3 ≤ k := by omega
      have hpmem : n^2+1 ≤ (2*x)^2+1 := Nat.add_le_add_right (Nat.pow_le_pow_left hn2x 2) 1
      have hp3 : p^3 ≤ n^2+1 := by
        calc p^3 ≤ p^k := Nat.pow_le_pow_right hp.one_le hk3
          _ = n^2+1 := heq.symm
      have hpM : (p:ℝ)^3 ≤ (2*(x:ℝ))^2+1 := by
        have h1 : ((p:ℝ))^3 ≤ ((n^2+1 : ℕ) : ℝ) := by
          calc ((p:ℝ))^3 = ((p^3 : ℕ) : ℝ) := by push_cast; ring
            _ ≤ ((n^2+1 : ℕ) : ℝ) := by exact_mod_cast hp3
        have h2 : ((n^2+1 : ℕ) : ℝ) ≤ (2*(x:ℝ))^2+1 := by
          calc ((n^2+1 : ℕ) : ℝ) ≤ (((2*x)^2+1 : ℕ) : ℝ) := by exact_mod_cast hpmem
            _ = (2*(x:ℝ))^2+1 := by push_cast; ring
        linarith
      have hpN : p ≤ N := by
        rw [hN]
        apply Nat.le_floor
        have hp0 : (0:ℝ) ≤ (p:ℝ) := by positivity
        have hstep : (p:ℝ) = ((p:ℝ)^3)^(1/3:ℝ) := by
          have h := Real.pow_rpow_inv_natCast (x := (p:ℝ)) hp0 (n := 3) (by norm_num)
          simpa using h.symm
        rw [hstep]
        exact Real.rpow_le_rpow (by positivity) hpM (by norm_num)
      have hkK : k ≤ K := by
        rw [hK]
        exact le_trans hklog (Nat.log_mono_right hpmem)
      exact ⟨p, k, hp, hk3, heq, hpN, hkK⟩
    -- ### Step 2: injective map into pairs (prime, exponent)
    let Q : ℕ → Prop := fun n => ∃ p k : ℕ, p.Prime ∧ 3 ≤ k ∧ n^2+1 = p^k ∧ p ≤ N ∧ k ≤ K
    let f : ℕ → ℕ × ℕ := fun n =>
      if h : Q n then (Classical.choose h, Classical.choose (Classical.choose_spec h)) else (0, 0)
    have hf_spec : ∀ n ∈ S, (f n).1.Prime ∧ 3 ≤ (f n).2 ∧ n^2+1 = (f n).1^(f n).2 ∧ (f n).1 ≤ N ∧ (f n).2 ≤ K := by
      intro n hn
      have hex : Q n := hdata n hn
      have hval : f n = (Classical.choose hex, Classical.choose (Classical.choose_spec hex)) := by
        simp only [f, dite_eq_left hex]
      rw [hval]
      exact Classical.choose_spec (Classical.choose_spec hex)
    have hmaps : Set.MapsTo f (↑S : Set ℕ) ↑((Finset.range (N+1)).filter Nat.Prime ×ˢ Finset.range (K+1)) := by
      intro n hn
      have hspec := hf_spec n hn
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_range]
      refine ⟨⟨by omega, hspec.1⟩, by omega⟩
    have hinj : (↑S : Set ℕ).InjOn f := by
      intro n hn m hm hnm
      have hn' := hf_spec n hn
      have hm' := hf_spec m hm
      have h1 : (f n).1 = (f m).1 := by rw [hnm]
      have h2 : (f n).2 = (f m).2 := by rw [hnm]
      have he : n^2+1 = m^2+1 := by
        rw [hn'.2.2.1, hm'.2.2.1, h1, h2]
      exact hsq n m (by omega)
    -- ### Step 3: cardinality bound
    have hcardS := Finset.card_le_card_of_injOn f hmaps hinj
    set T : Finset (ℕ × ℕ) := (Finset.range (N+1)).filter Nat.Prime ×ˢ Finset.range (K+1) with hT
    have hcardT : S.card ≤ ((N+1) * (K+1) : ℕ) := by
      calc S.card ≤ T.card := hcardS
        _ = ((Finset.range (N+1)).filter Nat.Prime).card * (Finset.range (K+1)).card := by
              rw [hT, Finset.card_product]
        _ ≤ (N+1) * (K+1) := by
              apply Nat.mul_le_mul _ (le_of_eq (Finset.card_range _))
              exact le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_range _))
    -- ### Step 4: real bounds
    have hNle : ((N:ℝ) + 1) ≤ 3 * (x:ℝ)^(2/3:ℝ) := by
      rw [hN]
      have hr0 : (0:ℝ) ≤ (((2*(x:ℝ))^2+1)^(1/3:ℝ)) := Real.rpow_nonneg (by positivity) _
      have hcube : ((x:ℝ)^(2/3:ℝ))^3 = (x:ℝ)^2 := by
        rw [← Real.rpow_mul_natCast hx0 (2/3:ℝ) 3]
        norm_num [Real.rpow_two]
      have hA : (2*(x:ℝ))^2+1 ≤ (2 * (x:ℝ)^(2/3:ℝ))^3 := by nlinarith
      have hB : (((2*(x:ℝ))^2+1)^(1/3:ℝ)) ≤ ((2 * (x:ℝ)^(2/3:ℝ))^3)^(1/3:ℝ) :=
        Real.rpow_le_rpow (by positivity) hA (by norm_num)
      have h2c : (0:ℝ) ≤ 2 * (x:ℝ)^(2/3:ℝ) := by
        have := Real.rpow_nonneg hx0 (2/3:ℝ)
        linarith
      have hC : ((2 * (x:ℝ)^(2/3:ℝ))^3)^(1/3:ℝ) = 2 * (x:ℝ)^(2/3:ℝ) := by
        have h := Real.pow_rpow_inv_natCast (x := 2 * (x:ℝ)^(2/3:ℝ)) h2c (n := 3) (by norm_num)
        simpa using h
      have hNfloor : ((Nat.floor (((2*(x:ℝ))^2+1)^(1/3:ℝ)) : ℕ) : ℝ) ≤ ((2*(x:ℝ))^2+1)^(1/3:ℝ) :=
        Nat.floor_le hr0
      have hx23 : (1:ℝ) ≤ (x:ℝ)^(2/3:ℝ) := Real.one_le_rpow hx1 (by norm_num)
      linarith
    have hKle : ((K:ℝ) + 1) ≤ 7 * Real.log (2*(x:ℝ)) := by
      rw [hK]
      have hKne : (2*x)^2+1 ≠ 0 := by positivity
      have h2K : (2:ℝ)^(Nat.log 2 ((2*x)^2+1)) ≤ (((2*x)^2+1 : ℕ) : ℝ) := by
        have h := Nat.pow_log_le_self 2 hKne
        exact_mod_cast h
      have hcast : (((2*x)^2+1 : ℕ) : ℝ) = (2*(x:ℝ))^2+1 := by push_cast; ring
      have h2K' : (2:ℝ)^(Nat.log 2 ((2*x)^2+1)) ≤ (2*(x:ℝ))^2+1 := by rw [← hcast]; exact h2K
      have hKlog : ((Nat.log 2 ((2*x)^2+1) : ℕ) : ℝ) * Real.log 2 ≤ Real.log ((2*(x:ℝ))^2+1) := by
        have h := Real.log_le_log (by positivity) h2K'
        rwa [Real.log_pow] at h
      have hMle : Real.log ((2*(x:ℝ))^2+1) ≤ 4 * Real.log (2*(x:ℝ)) := hlogbd x hx
      have hL1 : (1:ℝ) ≤ Real.log (2*(x:ℝ)) := by
        rw [Real.le_log_iff_exp_le (by positivity)]
        nlinarith [Real.exp_one_lt_three]
      have hK6 : ((Nat.log 2 ((2*x)^2+1) : ℕ) : ℝ) ≤ 6 * Real.log (2*(x:ℝ)) := by
        have hl2 : (2/3:ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
        have hKnn : (0:ℝ) ≤ ((Nat.log 2 ((2*x)^2+1) : ℕ) : ℝ) := by positivity
        nlinarith
      linarith
    have hLnn : (0:ℝ) ≤ Real.log (2*(x:ℝ)) := by
      have : (1:ℝ) ≤ Real.log (2*(x:ℝ)) := by
        rw [Real.le_log_iff_exp_le (by positivity)]
        nlinarith [Real.exp_one_lt_three]
      linarith
    have hxnn : (0:ℝ) ≤ (x:ℝ)^(2/3:ℝ) := Real.rpow_nonneg hx0 _
    have hcardR : ((S.card : ℕ) : ℝ) ≤ ((N:ℝ) + 1) * ((K:ℝ) + 1) := by
      have h := hcardT
      calc ((S.card : ℕ) : ℝ) ≤ (((N+1) * (K+1) : ℕ) : ℝ) := by exact_mod_cast h
        _ = ((N:ℝ) + 1) * ((K:ℝ) + 1) := by push_cast; ring
    have hprod : ((N:ℝ) + 1) * ((K:ℝ) + 1) ≤ (3 * (x:ℝ)^(2/3:ℝ)) * (7 * Real.log (2*(x:ℝ))) :=
      mul_le_mul hNle hKle (by linarith) (by positivity)
    nlinarith
  set D : ℝ := 57600 * (2:ℝ)^(1/6:ℝ) with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  obtain ⟨X0, hX0⟩ : ∃ X0 : ℕ, (D/ε)^6 < (X0:ℝ) := exists_nat_gt _
  refine ⟨max 2 (X0+1), ?_⟩
  intro x hxX
  have hx2 : 2 ≤ x := le_trans (le_max_left 2 (X0+1)) hxX
  have hX0le : X0 + 1 ≤ x := le_trans (le_max_right 2 (X0+1)) hxX
  have hxX0 : (X0:ℝ) < (x:ℝ) := by exact_mod_cast (Nat.lt_of_succ_le hX0le)
  have hxgt : (D/ε)^6 < (x:ℝ) := by linarith
  have hx2R : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx2
  have hxpos : (0:ℝ) < (x:ℝ) := by linarith
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by linarith
  have hx0 : (0:ℝ) ≤ (x:ℝ) := le_of_lt hxpos
  set L : ℝ := Real.log (2*(x:ℝ)) with hLdef
  have hL1 : (1:ℝ) ≤ L := by
    rw [hLdef]
    rw [Real.le_log_iff_exp_le (by positivity)]
    nlinarith [Real.exp_one_lt_three, hx2R]
  have hLnn : (0:ℝ) ≤ L := by linarith
  set S : Finset ℕ := (Finset.Ioc x (2*x)).filter (fun n => ArithmeticFunction.vonMangoldt (n^2+1) ≠ 0 ∧ ¬ (n^2+1).Prime) with hS
  have hsum : pp x = ∑ n ∈ S, ArithmeticFunction.vonMangoldt (n^2+1) := by
    rw [hppdef, hS]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro n hn
      obtain ⟨hm, hLne, hnp⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨hm, hnp⟩
    · intro n hn hnotin
      have hnp : ¬ Nat.Prime (n^2+1) := (Finset.mem_filter.mp hn).2
      have hL0 : ArithmeticFunction.vonMangoldt (n^2+1) = 0 := by
        by_contra hne
        exact hnotin (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1, hne, hnp⟩)
      exact hL0
  have hterm : ∀ n ∈ S, ArithmeticFunction.vonMangoldt (n^2+1) ≤ 4 * L := by
    intro n hn
    obtain ⟨hmem, hLne, hnp⟩ := Finset.mem_filter.mp hn
    have hn2x : n ≤ 2*x := (Finset.mem_Ioc.mp hmem).2
    have h1 : ArithmeticFunction.vonMangoldt (n^2+1) ≤ Real.log ((n^2+1 : ℕ) : ℝ) :=
      ArithmeticFunction.vonMangoldt_le_log
    have hpos : (0:ℝ) < ((n^2+1 : ℕ) : ℝ) := by positivity
    have hmemle : n^2+1 ≤ (2*x)^2+1 := Nat.add_le_add_right (Nat.pow_le_pow_left hn2x 2) 1
    have hle : ((n^2+1 : ℕ) : ℝ) ≤ (2*(x:ℝ))^2+1 := by
      calc ((n^2+1:ℕ):ℝ) ≤ (((2*x)^2+1:ℕ):ℝ) := by exact_mod_cast hmemle
        _ = (2*(x:ℝ))^2+1 := by push_cast; ring
    have h3 : Real.log ((n^2+1:ℕ):ℝ) ≤ Real.log ((2*(x:ℝ))^2+1) := Real.log_le_log hpos hle
    have h4 : Real.log ((2*(x:ℝ))^2+1) ≤ 4 * L := by
      rw [hLdef]
      exact hlogbd x hx2
    linarith
  have hSbound : ∑ n ∈ S, ArithmeticFunction.vonMangoldt (n^2+1) ≤ (S.card : ℝ) * (4 * L) := by
    calc ∑ n ∈ S, ArithmeticFunction.vonMangoldt (n^2+1) ≤ ∑ n ∈ S, (4 * L) := Finset.sum_le_sum hterm
      _ = (S.card : ℝ) * (4 * L) := by
            rw [Finset.sum_const, nsmul_eq_mul]
  have hcard := hcount x hx2
  have hx23 : (0:ℝ) ≤ (x:ℝ)^(2/3:ℝ) := Real.rpow_nonneg hx0 _
  have hLs : L^2 ≤ 144 * (2*(x:ℝ))^(1/6:ℝ) := by
    rw [hLdef]
    have ht1 : (1:ℝ) ≤ 2*(x:ℝ) := by linarith
    have ht0 : (0:ℝ) < 2*(x:ℝ) := by linarith
    have hLb : Real.log (2*(x:ℝ)) ≤ 12 * (2*(x:ℝ))^(1/12:ℝ) := hlog12 _ ht1
    have hLnn' : (0:ℝ) ≤ Real.log (2*(x:ℝ)) := Real.log_nonneg ht1
    have h12nn : (0:ℝ) ≤ (2*(x:ℝ))^(1/12:ℝ) := Real.rpow_nonneg ht0.le _
    have hsq : ((2*(x:ℝ))^(1/12:ℝ))^2 = (2*(x:ℝ))^(1/6:ℝ) := by
      rw [← Real.rpow_mul_natCast ht0.le (1/12:ℝ) 2]
      norm_num
    nlinarith [hLb, hLnn', h12nn, hsq]
  have hprod : (x:ℝ)^(2/3:ℝ) * (2*(x:ℝ))^(1/6:ℝ) = (2:ℝ)^(1/6:ℝ) * (x:ℝ)^(5/6:ℝ) := by
    have h1 : (2*(x:ℝ))^(1/6:ℝ) = (2:ℝ)^(1/6:ℝ) * (x:ℝ)^(1/6:ℝ) :=
      Real.mul_rpow (by norm_num) hx0
    have h2 : (x:ℝ)^(2/3:ℝ) * (x:ℝ)^(1/6:ℝ) = (x:ℝ)^(5/6:ℝ) := by
      rw [← Real.rpow_add hxpos (2/3:ℝ) (1/6:ℝ)]
      norm_num
    calc (x:ℝ)^(2/3:ℝ) * (2*(x:ℝ))^(1/6:ℝ) = (x:ℝ)^(2/3:ℝ) * ((2:ℝ)^(1/6:ℝ) * (x:ℝ)^(1/6:ℝ)) := by rw [h1]
      _ = (2:ℝ)^(1/6:ℝ) * ((x:ℝ)^(2/3:ℝ) * (x:ℝ)^(1/6:ℝ)) := by ring
      _ = (2:ℝ)^(1/6:ℝ) * (x:ℝ)^(5/6:ℝ) := by rw [h2]
  have hpbound : pp x ≤ D * (x:ℝ)^(5/6:ℝ) := by
    have hstep1 : (S.card : ℝ) * (4 * L) ≤ (100 * (x:ℝ)^(2/3:ℝ) * L) * (4 * L) :=
      mul_le_mul_of_nonneg_right hcard (by linarith)
    have hstep2 : (100 * (x:ℝ)^(2/3:ℝ) * L) * (4 * L) = 400 * ((x:ℝ)^(2/3:ℝ) * L^2) := by ring
    have hstep3 : 400 * ((x:ℝ)^(2/3:ℝ) * L^2) ≤ 400 * ((x:ℝ)^(2/3:ℝ) * (144 * (2*(x:ℝ))^(1/6:ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul_of_nonneg_left hLs hx23
    have hstep4 : 400 * ((x:ℝ)^(2/3:ℝ) * (144 * (2*(x:ℝ))^(1/6:ℝ))) = 57600 * ((x:ℝ)^(2/3:ℝ) * (2*(x:ℝ))^(1/6:ℝ)) := by ring
    calc pp x = ∑ n ∈ S, ArithmeticFunction.vonMangoldt (n^2+1) := hsum
      _ ≤ (S.card : ℝ) * (4 * L) := hSbound
      _ ≤ 400 * ((x:ℝ)^(2/3:ℝ) * L^2) := by linarith
      _ ≤ 57600 * ((x:ℝ)^(2/3:ℝ) * (2*(x:ℝ))^(1/6:ℝ)) := by linarith
      _ = 57600 * ((2:ℝ)^(1/6:ℝ) * (x:ℝ)^(5/6:ℝ)) := by rw [hprod]
      _ = D * (x:ℝ)^(5/6:ℝ) := by rw [hD]; ring
  have hDnn : (0:ℝ) ≤ D := le_of_lt hDpos
  have hDivpos : (0:ℝ) < D/ε := div_pos hDpos hε
  have hx6 : D/ε ≤ (x:ℝ)^(1/6:ℝ) := by
    have h1 : ((D/ε)^6)^(1/6:ℝ) = D/ε := by
      have h := Real.pow_rpow_inv_natCast (x := D/ε) hDivpos.le (n := 6) (by norm_num)
      simpa using h
    have h2 : ((D/ε)^6)^(1/6:ℝ) ≤ (x:ℝ)^(1/6:ℝ) :=
      Real.rpow_le_rpow (le_of_lt (pow_pos hDivpos 6)) hxgt.le (by norm_num)
    linarith
  have hxsum : (x:ℝ)^(1/6:ℝ) * (x:ℝ)^(5/6:ℝ) = (x:ℝ) := by
    rw [← Real.rpow_add hxpos (1/6:ℝ) (5/6:ℝ)]
    norm_num
  have hDε : D ≤ ε * (x:ℝ)^(1/6:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hx6 (le_of_lt hε)
    have h2 : ε * (D/ε) = D := by field_simp
    linarith
  calc pp x ≤ D * (x:ℝ)^(5/6:ℝ) := hpbound
    _ ≤ (ε * (x:ℝ)^(1/6:ℝ)) * (x:ℝ)^(5/6:ℝ) :=
          mul_le_mul_of_nonneg_right hDε (Real.rpow_nonneg hx0 _)
    _ = ε * (x:ℝ) := by rw [mul_assoc, hxsum]
