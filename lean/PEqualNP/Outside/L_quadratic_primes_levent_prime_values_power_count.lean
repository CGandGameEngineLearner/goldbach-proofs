import Mathlib

private lemma quad_no_square : ∀ n p j : ℕ, 0 < n → 0 < j → n^2+1 ≠ p^(2*j) := by
  intro n p j hn hj h
  have hsq : n^2+1 = (p^j)^2 := by
    rw [h, ← pow_mul]
    ring_nf
  have hlt : n < p^j := by
    by_contra hc
    have h2 : (p^j)^2 ≤ n^2 := Nat.pow_le_pow_left (not_lt.mp hc) 2
    omega
  have h2 : (n+1)^2 ≤ (p^j)^2 := Nat.pow_le_pow_left hlt 2
  have h3 : n^2 + 1 < (n+1)^2 := by nlinarith [hn]
  omega

private lemma rpow_third_cube (a : ℝ) (ha : 0 ≤ a) : ((a^(3:ℕ) : ℝ))^(1/3:ℝ) = a := by
  have h1 : a^(3:ℕ) = a^(3:ℝ) := (Real.rpow_natCast a 3).symm
  rw [h1, ← Real.rpow_mul ha 3 (1/3:ℝ)]
  norm_num

private lemma cube_root_le {p M : ℕ} (h : p^3 ≤ M) : (p:ℝ) ≤ (M:ℝ)^(1/3:ℝ) := by
  have hp : ((p:ℝ))^(3:ℕ) ≤ (M:ℝ) := by exact_mod_cast h
  have h1 : ((p:ℝ)^(3:ℕ))^(1/3:ℝ) ≤ (M:ℝ)^(1/3:ℝ) :=
    Real.rpow_le_rpow (by positivity) hp (by norm_num)
  have h2 : ((p:ℝ)^(3:ℕ))^(1/3:ℝ) = (p:ℝ) := rpow_third_cube (p:ℝ) (by positivity)
  rwa [h2] at h1

private lemma cube_root_bound {M : ℕ} {x : ℕ} (hM : (M:ℝ) ≤ 8*(x:ℝ)^2) :
    (M:ℝ)^(1/3:ℝ) ≤ 2*(x:ℝ)^(2/3:ℝ) := by
  have h1 : (M:ℝ)^(1/3:ℝ) ≤ (8*(x:ℝ)^(2:ℕ))^(1/3:ℝ) :=
    Real.rpow_le_rpow (by positivity) hM (by norm_num)
  have h2 : (8*(x:ℝ)^(2:ℕ))^(1/3:ℝ) = 2*(x:ℝ)^(2/3:ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 8) (by positivity : (0:ℝ) ≤ (x:ℝ)^(2:ℕ))]
    have h8 : (8:ℝ)^(1/3:ℝ) = 2 := by
      rw [show (8:ℝ) = 2^(3:ℕ) by norm_num]
      exact rpow_third_cube 2 (by norm_num)
    have hx2 : ((x:ℝ)^(2:ℕ))^(1/3:ℝ) = (x:ℝ)^(2/3:ℝ) := by
      have h1 : (x:ℝ)^(2:ℕ) = (x:ℝ)^(2:ℝ) := (Real.rpow_natCast (x:ℝ) 2).symm
      rw [h1, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (x:ℝ)) 2 (1/3:ℝ)]
      norm_num
    rw [h8, hx2]
  rw [h2] at h1
  exact h1

theorem PEqualNP.Outside.L_quadratic_primes_levent_prime_values_power_count : let block := fun x : ℕ => Finset.Ioc x (2*x); ∃ C : ℝ, 0<C ∧ ∀ x : ℕ, 2≤x → (((block x).filter (fun n => ArithmeticFunction.vonMangoldt (n^2+1)≠0 ∧ ¬ (n^2+1).Prime)).card : ℝ) ≤ C*(x : ℝ)^(2/3 : ℝ)*Real.log (2*(x : ℝ)) := by
  dsimp only
  refine ⟨13, by norm_num, ?_⟩
  intro x hx
  classical
  have hxR : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  set M : ℕ := (2*x)^2 + 1 with hM
  set T : ℝ := (M:ℝ)^(1/3:ℝ) with hT
  set K : ℕ := Nat.log 2 M with hK
  set S : Finset ℕ := (Finset.Ioc x (2*x)).filter (fun n => ArithmeticFunction.vonMangoldt (n^2+1) ≠ 0 ∧ ¬ (n^2+1).Prime) with hS
  have hMpos_nat : 0 < M := by rw [hM]; positivity
  have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast hMpos_nat
  have hTpos : (0:ℝ) < T := by rw [hT]; exact Real.rpow_pos_of_pos hMpos _
  -- structure of every element of the filtered set
  have hkey : ∀ n ∈ S, ∃ k : ℕ, 3 ≤ k ∧ k ≤ K ∧ Nat.Prime ((n^2+1).minFac) ∧
      (n^2+1).minFac ≤ ⌊T⌋₊ ∧ n^2+1 = (n^2+1).minFac ^ k := by
    intro n hn
    rw [hS] at hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨hxn, hnx2⟩, hΛ, hnp⟩ := hn
    have hn0 : 0 < n := by omega
    have hp : Nat.Prime ((n^2+1).minFac) := Nat.minFac_prime (by nlinarith)
    have hpp : IsPrimePow (n^2+1) := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
    obtain ⟨k, hkle, hkpos, heq⟩ := (isPrimePow_nat_iff_bounded_log_minFac (n^2+1)).mp hpp
    have hk2 : 2 ≤ k := by
      rcases k with _ | _ | k
      · omega
      · exfalso
        apply hnp
        rw [heq, pow_one]
        exact hp
      · omega
    have hk3 : 3 ≤ k := by
      rcases Nat.even_or_odd k with hev | hod
      · obtain ⟨j, hj⟩ := hev
        exfalso
        have hjpos : 0 < j := by omega
        have he : (n^2+1).minFac ^ k = (n^2+1).minFac ^ (2*j) := by
          rw [hj, show j + j = 2 * j by omega]
        exact quad_no_square n ((n^2+1).minFac) j hn0 hjpos (heq.trans he)
      · obtain ⟨j, hj⟩ := hod
        omega
    have hnm : n^2+1 ≤ M := by
      rw [hM]
      have h2 := Nat.pow_le_pow_left hnx2 2
      omega
    have hp3 : (n^2+1).minFac ^ 3 ≤ n^2+1 := by
      calc (n^2+1).minFac ^ 3 ≤ (n^2+1).minFac ^ k :=
            Nat.pow_le_pow_right hp.pos hk3
        _ = n^2+1 := heq.symm
    have hple : (n^2+1).minFac ≤ ⌊T⌋₊ := by
      apply Nat.le_floor
      rw [hT]
      exact cube_root_le (le_trans hp3 hnm)
    refine ⟨k, hk3, ?_, hp, hple, heq⟩
    calc k ≤ Nat.log 2 (n^2+1) := hkle
      _ ≤ Nat.log 2 M := Nat.log_mono_right hnm
      _ = K := hK.symm
  set P1 : Finset ℕ := (Finset.Icc 1 ⌊T⌋₊).filter Nat.Prime with hP1
  set P2 : Finset ℕ := Finset.Icc 3 K with hP2
  set Pairs : Finset (ℕ × ℕ) := P1 ×ˢ P2 with hPairs
  let f : ℕ → ℕ × ℕ := fun n => ((n^2+1).minFac, Nat.log ((n^2+1).minFac) (n^2+1))
  have hlogkey : ∀ (n : ℕ) (hn : n ∈ S),
      Nat.log ((n^2+1).minFac) (n^2+1) = Classical.choose (hkey n hn) := by
    intro n hn
    obtain ⟨hk3, hkK, hp, hple, heq⟩ := Classical.choose_spec (hkey n hn)
    have h := Nat.log_pow hp.one_lt (Classical.choose (hkey n hn))
    rw [← heq] at h
    exact h
  have hf_maps : Set.MapsTo f (S:Set ℕ) (Pairs:Set (ℕ × ℕ)) := by
    intro n hn
    simp only [Finset.mem_coe] at hn
    obtain ⟨hk3, hkK, hp, hple, heq⟩ := Classical.choose_spec (hkey n hn)
    have hfval : f n = ((n^2+1).minFac, Classical.choose (hkey n hn)) := by
      simp only [f, hlogkey n hn]
    have hmem1 : (n^2+1).minFac ∈ P1 := by
      rw [hP1]
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨le_trans (by norm_num) hp.two_le, hple⟩, hp⟩
    have hmem2 : Classical.choose (hkey n hn) ∈ P2 := by
      rw [hP2]
      exact Finset.mem_Icc.mpr ⟨hk3, hkK⟩
    rw [hfval, hPairs, Finset.mem_coe, Finset.mem_product]
    exact ⟨hmem1, hmem2⟩
  have hkey2 : ∀ n ∈ S, n^2+1 = (n^2+1).minFac ^ Nat.log ((n^2+1).minFac) (n^2+1) := by
    intro n hn
    obtain ⟨hk3, hkK, hp, hple, heq⟩ := Classical.choose_spec (hkey n hn)
    rw [hlogkey n hn]
    exact heq
  have hf_inj : (S:Set ℕ).InjOn f := by
    intro a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    have hab' : ((a^2+1).minFac, Nat.log ((a^2+1).minFac) (a^2+1))
        = ((b^2+1).minFac, Nat.log ((b^2+1).minFac) (b^2+1)) := hab
    simp only [Prod.mk.injEq] at hab'
    obtain ⟨hpeq, hlogeq⟩ := hab'
    have h3 : (a^2+1).minFac ^ Nat.log ((a^2+1).minFac) (a^2+1)
        = (b^2+1).minFac ^ Nat.log ((b^2+1).minFac) (b^2+1) := by
      rw [hlogeq, hpeq]
    have h1 : a^2+1 = b^2+1 := (hkey2 a ha).trans (h3.trans (hkey2 b hb).symm)
    have hsq : a^2 = b^2 := by omega
    exact Nat.pow_left_injective (by norm_num) hsq
  have hcardS : S.card ≤ Pairs.card := Finset.card_le_card_of_injOn f hf_maps hf_inj
  have hP1nat : P1.card ≤ ⌊T⌋₊ := by
    have h := Finset.card_filter_le (Finset.Icc 1 ⌊T⌋₊) Nat.Prime
    rw [hP1]
    simpa using h
  have hP2nat : P2.card ≤ K := by
    have h1 : P2.card ≤ (Finset.Icc 1 K).card := by
      rw [hP2]
      apply Finset.card_le_card
      intro m hm
      simp only [Finset.mem_Icc] at hm ⊢
      omega
    have h2 : (Finset.Icc 1 K).card = K := by simp
    omega
  have hcardPairs : (Pairs.card : ℝ) = (P1.card : ℝ) * (P2.card : ℝ) := by
    rw [hPairs, Finset.card_product]
    push_cast
    ring
  have h5 : (S.card : ℝ) ≤ T * (K:ℝ) := by
    have hTnn : (0:ℝ) ≤ T := le_of_lt hTpos
    have hP1r : (P1.card : ℝ) ≤ T := by
      have h1 : (P1.card : ℝ) ≤ ((⌊T⌋₊ : ℕ) : ℝ) := by exact_mod_cast hP1nat
      have h2 : ((⌊T⌋₊ : ℕ) : ℝ) ≤ T := (Nat.le_floor_iff (le_of_lt hTpos)).mp le_rfl
      linarith
    have hP2r : (P2.card : ℝ) ≤ (K:ℝ) := by exact_mod_cast hP2nat
    calc (S.card : ℝ) ≤ (Pairs.card : ℝ) := by exact_mod_cast hcardS
      _ = (P1.card : ℝ) * (P2.card : ℝ) := hcardPairs
      _ ≤ T * (K:ℝ) := mul_le_mul hP1r hP2r (Nat.cast_nonneg _) hTnn
  -- the two real bounds
  have hTeq : T = (M:ℝ)^(1/3:ℝ) := hT
  have hMle : (M:ℝ) ≤ 8*(x:ℝ)^2 := by
    have hMeq : (M:ℝ) = (2*(x:ℝ))^2 + 1 := by
      rw [hM]
      push_cast
      ring
    have hx1 : (1:ℝ) ≤ (x:ℝ)^2 := by nlinarith [hxR]
    rw [hMeq]
    nlinarith [hx1]
  have hTle : T ≤ 2*(x:ℝ)^(2/3:ℝ) := by
    rw [hTeq]
    exact cube_root_bound hMle
  have hMlog : Real.log (M:ℝ) ≤ 3 * Real.log (2*(x:ℝ)) := by
    have hx2 : (2:ℝ) ≤ 2*(x:ℝ) := by linarith
    have hpos : (0:ℝ) < 2*(x:ℝ) := by linarith
    have hMeq : (M:ℝ) = (2*(x:ℝ))^2 + 1 := by
      rw [hM]
      push_cast
      ring
    have h1 : (M:ℝ) ≤ 2*(2*(x:ℝ))^2 := by
      rw [hMeq]
      nlinarith [sq_nonneg (2*(x:ℝ)), hpos]
    have h2 : Real.log (M:ℝ) ≤ Real.log (2*(2*(x:ℝ))^2) := Real.log_le_log hMpos h1
    have h3 : Real.log (2*(2*(x:ℝ))^2) = Real.log 2 + 2*Real.log (2*(x:ℝ)) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    rw [h3] at h2
    have h4 : Real.log 2 ≤ Real.log (2*(x:ℝ)) := Real.log_le_log (by norm_num) hx2
    linarith
  have hK1 : (K:ℝ) ≤ Real.log (M:ℝ) / Real.log 2 := by
    have hpow : (2:ℝ)^(K:ℝ) ≤ (M:ℝ) := by
      have h := Nat.pow_log_le_self 2 (ne_of_gt hMpos_nat)
      rw [← hK] at h
      have h' : (2:ℝ)^K ≤ (M:ℝ) := by exact_mod_cast h
      rwa [← Real.rpow_natCast] at h'
    have hlog : Real.log ((2:ℝ)^(K:ℝ)) ≤ Real.log (M:ℝ) :=
      Real.log_le_log (Real.rpow_pos_of_pos (by norm_num) K) hpow
    have hKlog : Real.log ((2:ℝ)^(K:ℝ)) = (K:ℝ) * Real.log 2 := by
      rw [Real.rpow_natCast, Real.log_pow]
    rw [hKlog] at hlog
    rw [le_div_iff₀ (Real.log_pos (by norm_num))]
    exact hlog
  have hK2 : (K:ℝ) ≤ 6 * Real.log (2*(x:ℝ)) := by
    have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2' : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlogx : (0:ℝ) ≤ Real.log (2*(x:ℝ)) := Real.log_nonneg (by linarith)
    have hmid : Real.log (M:ℝ) / Real.log 2 ≤ 3 * Real.log (2*(x:ℝ)) / Real.log 2 := by
      rw [div_le_div_iff_of_pos_right hlog2]
      exact hMlog
    have hstep : 3 * Real.log (2*(x:ℝ)) / Real.log 2 ≤ 6 * Real.log (2*(x:ℝ)) := by
      rw [div_le_iff₀ hlog2]
      nlinarith [hlog2', hlogx]
    linarith
  have hKnn : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
  have hxpow : (0:ℝ) ≤ (x:ℝ)^(2/3:ℝ) := Real.rpow_nonneg (by positivity) _
  have hlogx2 : (0:ℝ) ≤ Real.log (2*(x:ℝ)) := Real.log_nonneg (by linarith)
  have hstep1 : T * (K:ℝ) ≤ (2*(x:ℝ)^(2/3:ℝ)) * (6*Real.log (2*(x:ℝ))) :=
    mul_le_mul hTle hK2 hKnn (by positivity)
  have hstep2 : (2*(x:ℝ)^(2/3:ℝ)) * (6*Real.log (2*(x:ℝ)))
      = 12 * ((x:ℝ)^(2/3:ℝ) * Real.log (2*(x:ℝ))) := by ring
  have hstep3 : 12 * ((x:ℝ)^(2/3:ℝ) * Real.log (2*(x:ℝ)))
      ≤ 13 * (x:ℝ)^(2/3:ℝ) * Real.log (2*(x:ℝ)) := by
    nlinarith [mul_nonneg hxpow hlogx2]
  linarith [h5, hstep1, hstep2, hstep3]
