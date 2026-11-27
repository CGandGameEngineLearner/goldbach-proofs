import Mathlib

/-!
# PREPUB goldbach: `L-goldbach-dyadic-sum-avoiding-mask`

Dyadic sum-avoiding mask: for every `W > 0` there is a modulus `M > 1` coprime to `W` and a
subset `S ⊆ [0,M)` with `M ≤ 8 |S|` such that no sum `a + b` (`a, b ∈ S`) is congruent to a
power of two modulo `M`.

Construction: take the Mersenne number `M = 2^n - 1` with `n = W! + 1` (so `M` is coprime to
`W`: a prime `p ∣ W` would give `2^(p-1) ≡ 1 [MOD p]`, hence `2^n ≡ 2 ≢ 1 [MOD p]`), and
`S = {2^(n-1) + 2 + 2 j : j < 2^(n-2) - 1}`.  Then `a + b ≡ 5 + 2 (i+j) [MOD M]` is odd and
`> 1`, while the residues of powers of two are `2^(k % n) ∈ {1, 2, ..., 2^(n-1)}`, the only odd
one of which is `1`.  Self-contained, Mathlib only.
-/

namespace PEqualNP.Outside

lemma coprime_fermat_factorial (W : ℕ) (hW : 0 < W) :
    Nat.Coprime W (2^(W.factorial + 1) - 1) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hg
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hg
  have hpW : p ∣ W := hpdvd.trans (Nat.gcd_dvd_left W (2^(W.factorial + 1) - 1))
  have hpM : p ∣ 2^(W.factorial + 1) - 1 :=
    hpdvd.trans (Nat.gcd_dvd_right W (2^(W.factorial + 1) - 1))
  have hpWge : p ≤ W := Nat.le_of_dvd hW hpW
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2dvd : (2:ℕ) ∣ 2^(W.factorial + 1) := ⟨2^(W.factorial), by rw [pow_succ]; ring⟩
    have hsub : 2^(W.factorial + 1) - (2^(W.factorial + 1) - 1) = 1 := by
      have h1 : 1 ≤ 2^(W.factorial + 1) := by
        have := pow_pos (by norm_num : (0:ℕ) < 2) (W.factorial + 1)
        omega
      omega
    have h1 : (2:ℕ) ∣ 1 := by
      rw [← hsub]
      exact Nat.dvd_sub h2dvd hpM
    omega
  have hpodd : 3 ≤ p := by
    have := hp.two_le
    omega
  have hW2 : 2 ≤ W := by omega
  have hle : p - 1 ≤ W.factorial := by
    have h1 : p - 1 ≤ W - 1 := by omega
    have h2 : W - 1 ≤ W.factorial := by
      have := Nat.self_le_factorial W
      omega
    omega
  have hdvd : p - 1 ∣ W.factorial := Nat.dvd_factorial (by omega) (by omega)
  have hfact : Fact p.Prime := ⟨hp⟩
  have hp2ne : (2 : ZMod p) ≠ 0 := by
    intro hd
    have hd' : ((2:ℕ) : ZMod p) = 0 := hd
    rw [ZMod.natCast_eq_zero_iff] at hd'
    have h2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd'
    omega
  have hFz : ((2 : ZMod p))^(p-1) = 1 := ZMod.pow_card_sub_one_eq_one hp2ne
  have hF : 2^(p-1) ≡ 1 [MOD p] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    push_cast
    exact hFz
  have hFW : 2^(W.factorial) ≡ 1 [MOD p] := by
    have heq : W.factorial = (p-1) * (W.factorial / (p-1)) := by
      rw [Nat.mul_comm]
      exact (Nat.div_mul_cancel hdvd).symm
    rw [heq, pow_mul]
    simpa using hF.pow (W.factorial / (p-1))
  have h2n : 2^(W.factorial + 1) ≡ 1 [MOD p] := by
    have h : (1:ℕ) ≡ 2^(W.factorial + 1) [MOD p] := by
      rw [Nat.modEq_iff_dvd' (by
        have := pow_pos (by norm_num : (0:ℕ) < 2) (W.factorial + 1)
        omega)]
      exact hpM
    exact h.symm
  have h21 : 2^(W.factorial + 1) ≡ 2 [MOD p] := by
    rw [pow_succ]
    calc 2^(W.factorial) * 2 ≡ 1 * 2 [MOD p] := hFW.mul (Nat.ModEq.refl 2)
      _ = 2 := by ring
  have h12 : (1:ℕ) ≡ 2 [MOD p] := h2n.symm.trans h21
  have hp1 : p ∣ 1 := by
    rw [← Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 2)]
    exact h12
  have : p ≤ 1 := Nat.le_of_dvd (by norm_num) hp1
  omega

lemma pow_two_mod_mersenne (n k : ℕ) (hn : 2 ≤ n) :
    2^k % (2^n - 1) = 2^(k % n) := by
  set M := 2^n - 1 with hM
  have hpow : 0 < 2^n := pow_pos (by norm_num : (0:ℕ) < 2) n
  have hM2 : 2 ≤ M := by
    have h : 2^2 ≤ 2^n := Nat.pow_le_pow_right (by norm_num) hn
    have h4 : 2^2 = 4 := by norm_num
    simp only [hM]; omega
  have hMeq : 2^n = M + 1 := by simp only [hM]; omega
  have h1 : 2^n ≡ 1 [MOD M] := by
    rw [Nat.ModEq]
    show 2^n % M = 1 % M
    rw [hMeq, Nat.add_mod, Nat.mod_self, Nat.zero_add]
    rw [Nat.mod_eq_of_lt (show 1 < M by omega), Nat.mod_eq_of_lt (show 1 < M by omega)]
  have hk : 2^k ≡ 2^(k % n) [MOD M] := by
    have hsplit : k = n * (k / n) + k % n := (Nat.div_add_mod k n).symm
    conv_lhs => rw [hsplit]
    rw [pow_add, pow_mul]
    calc (2^n)^(k/n) * 2^(k%n) ≡ 1^(k/n) * 2^(k%n) [MOD M] :=
          h1.pow (k/n) |>.mul (Nat.ModEq.refl _)
      _ = 2^(k%n) := by rw [one_pow, one_mul]
  have hlt : 2^(k % n) < M := by
    have h1 : k % n ≤ n - 1 := by
      have := Nat.mod_lt k (by omega : 0 < n)
      omega
    have h2 : 2^(k%n) ≤ 2^(n-1) := Nat.pow_le_pow_right (by norm_num) h1
    have h3 : 2^(n-1) * 2 = 2^n := by rw [← pow_succ]; congr 1; omega
    have h4 : 2 ≤ 2^(n-1) := by
      calc 2 = 2^1 := by norm_num
        _ ≤ 2^(n-1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [hM]; omega
  rw [Nat.ModEq] at hk
  rw [Nat.mod_eq_of_lt hlt] at hk
  exact hk

private lemma L_goldbach_dyadic_sum_avoiding_mask :
    ∀ W : ℕ, 0 < W → ∃ M : ℕ, 1 < M ∧ Nat.Coprime W M ∧ ∃ S : Finset ℕ, S ⊆ Finset.range M ∧ M ≤ 8 * S.card ∧ ∀ (a b k : ℕ), a ∈ S → b ∈ S → (a+b)%M ≠ (2^k)%M := by
  intro W hW
  rcases Nat.lt_or_ge W 2 with h1 | h2
  · have hW1 : W = 1 := by omega
    subst hW1
    refine ⟨3, by norm_num, by norm_num, {0}, ?_, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_singleton] at hx
      subst hx
      simp
    · simp
    · intro a b k ha hb
      simp only [Finset.mem_singleton] at ha hb
      subst ha hb
      intro hcon
      have hcon' : 2^k % 3 = 0 := by
        have h : ((0:ℕ) + 0) % 3 = 0 := by norm_num
        rw [h] at hcon
        exact hcon.symm
      have hdvd : 3 ∣ 2^k := Nat.dvd_of_mod_eq_zero hcon'
      have hp3 : Nat.Prime 3 := by norm_num
      have h2dvd : 3 ∣ 2 := hp3.dvd_of_dvd_pow hdvd
      omega
  · set n : ℕ := W.factorial + 1 with hn
    have hn3 : 3 ≤ n := by
      have hfac : 2 ≤ W.factorial := by
        have := Nat.self_le_factorial W
        omega
      omega
    set B : ℕ := 2^(n-2) with hBdef
    have hB2 : 2 ≤ B := by
      have h : 2^1 ≤ 2^(n-2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2' : 2^1 = 2 := by norm_num
      omega
    have hArel : 2^(n-1) = 2 * B := by
      have e : n - 2 + 1 = n - 1 := by omega
      calc 2^(n-1) = 2^(n-2+1) := by rw [e]
        _ = 2^(n-2) * 2 := pow_succ _ _
        _ = 2 * B := by rw [hBdef]; ring
    have hBrel : 2^n = 2 * 2^(n-1) := by
      have e : n - 1 + 1 = n := by omega
      calc 2^n = 2^(n-1+1) := by rw [e]
        _ = 2^(n-1) * 2 := pow_succ _ _
        _ = 2 * 2^(n-1) := by ring
    obtain ⟨B', hB'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : B ≠ 0)
    have hA2 : 2^(n-1) = 2*B' + 2 := by rw [hArel, hB']; omega
    have hpow2 : 2^n = 4*B' + 4 := by rw [hBrel, hA2]; ring
    have hB'1 : 1 ≤ B' := by omega
    refine ⟨2^n - 1, ?_, ?_, ?_⟩
    · rw [hpow2]; omega
    · exact coprime_fermat_factorial W hW
    · refine ⟨(Finset.range B').image (fun j => 2^(n-1) + 2 + 2*j), ?_, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_image, Finset.mem_range] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        simp only [Finset.mem_range]
        rw [hA2, hpow2]
        omega
      · rw [Finset.card_image_of_injOn]
        · simp
          rw [hpow2]
          omega
        · intro x _ y _ hxy
          simp only at hxy
          omega
      · intro a b k ha hb
        simp only [Finset.mem_image, Finset.mem_range] at ha hb
        obtain ⟨j1, hj1, rfl⟩ := ha
        obtain ⟨j2, hj2, rfl⟩ := hb
        have hsum : (2^(n-1) + 2 + 2*j1) + (2^(n-1) + 2 + 2*j2)
            = (2^n - 1) + (5 + 2*(j1+j2)) := by
          rw [hA2, hpow2]
          omega
        have hrM : 5 + 2*(j1+j2) < 2^n - 1 := by
          rw [hpow2]
          omega
        have hmod1 : ((2^(n-1) + 2 + 2*j1) + (2^(n-1) + 2 + 2*j2)) % (2^n - 1) = 5 + 2*(j1+j2) := by
          rw [hsum, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hrM]
        rw [hmod1, pow_two_mod_mersenne n k (by omega)]
        intro hcon
        rcases Nat.eq_zero_or_pos (k % n) with hk0 | hkpos
        · rw [hk0] at hcon
          simp only [pow_zero] at hcon
          omega
        · obtain ⟨m, hm⟩ : ∃ m, k % n = m + 1 := ⟨k % n - 1, by omega⟩
          rw [hm, pow_succ] at hcon
          omega

end PEqualNP.Outside

/-! Canonical module-named statement (platform checker requires a declaration
named exactly after the gap module: `Conjectures.Goldbach.DyadicSumAvoidingMask`). -/

theorem Conjectures.Goldbach.DyadicSumAvoidingMask :
    ∀ W : ℕ, 0 < W → ∃ M : ℕ, 1 < M ∧ Nat.Coprime W M ∧ ∃ S : Finset ℕ, S ⊆ Finset.range M ∧ M ≤ 8 * S.card ∧ ∀ (a b k : ℕ), a ∈ S → b ∈ S → (a+b)%M ≠ (2^k)%M := by
  exact PEqualNP.Outside.L_goldbach_dyadic_sum_avoiding_mask
