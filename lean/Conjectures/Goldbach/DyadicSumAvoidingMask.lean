import Mathlib

/-! Self-contained proof of `L-goldbach-dyadic-sum-avoiding-mask`. -/

namespace PEqualNP.Outside

theorem L_goldbach_dyadic_sum_avoiding_mask :
    ∀ W : ℕ, 0 < W → ∃ M : ℕ, 1 < M ∧ Nat.Coprime W M ∧
      ∃ S : Finset ℕ, S ⊆ Finset.range M ∧ M ≤ 8 * S.card ∧
        ∀ (a b k : ℕ), a ∈ S → b ∈ S → (a + b) % M ≠ (2 ^ k) % M := by
  intro W hW
  obtain ⟨s, hsge, hsprime⟩ := Nat.exists_infinite_primes (max W 5 + 1)
  have hsW : W < s := by omega
  have hs5 : 5 < s := by omega
  have hs3 : 3 ≤ s := by omega
  let L : ℕ := 2 ^ (s - 3)
  let M : ℕ := 8 * L - 1
  have hLpos : 0 < L := by positivity
  have hL1 : 1 ≤ L := Nat.one_le_two_pow
  have hMdef : M = 2 ^ s - 1 := by
    dsimp [M, L]
    have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [h8, ← pow_add, show 3 + (s - 3) = s by omega]
  have hMgt1 : 1 < M := by
    dsimp [M]
    omega
  let S : Finset ℕ := Finset.Ico (3 * L) (4 * L)
  have hScard : S.card = L := by
    dsimp [S]
    rw [Nat.card_Ico]
    omega
  have hSsub : S ⊆ Finset.range M := by
    intro x hx
    rw [Finset.mem_range]
    rw [Finset.mem_Ico] at hx
    have hxlt : x < 4 * L := hx.2
    have h4M : 4 * L < M := by
      dsimp [M]
      omega
    omega
  have hMle : M ≤ 8 * S.card := by
    rw [hScard]
    dsimp [M]
    omega
  have hcop : Nat.Coprime W M := by
    by_contra hnot
    obtain ⟨p, hp, hpW, hpM⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
    have hp2 : p ≠ 2 := by
      intro hp_eq
      subst hp_eq
      have hEven : Even M := even_iff_two_dvd.mpr hpM
      have hOdd : Odd M := by
        dsimp [M]
        refine ⟨4 * L - 1, by omega⟩
      exact (Nat.not_even_iff_odd.mpr hOdd) hEven
    have hpgt2 : 2 < p := by
      have h2le := hp.two_le
      omega
    have hpWle : p ≤ W := Nat.le_of_dvd hW hpW
    have hps : p < s := lt_of_le_of_lt hpWle hsW
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro hzero
      have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
      omega
    have hMcast : ((M : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff M p).mpr hpM
    have hpow : (2 : ZMod p) ^ s = 1 := by
      have hcast : ((2 ^ s - 1 : ℕ) : ZMod p) = 0 := by
        rw [← hMdef]
        exact hMcast
      rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat,
        Nat.cast_one] at hcast
      exact sub_eq_zero.mp hcast
    have hdvd_s : orderOf (2 : ZMod p) ∣ s :=
      (orderOf_dvd_iff_pow_eq_one).mpr hpow
    have hdvd_p1 : orderOf (2 : ZMod p) ∣ p - 1 :=
      ZMod.orderOf_dvd_card_sub_one h2ne
    rcases (Nat.dvd_prime hsprime).mp hdvd_s with h1 | hsEq
    · have h2eq1 : (2 : ZMod p) = 1 := (orderOf_eq_one_iff).mp h1
      have hone : (1 : ZMod p) = 0 := by
        have htwo : (2 : ZMod p) = (1 : ZMod p) + 1 := by norm_num
        rw [htwo] at h2eq1
        have := congrArg (fun x : ZMod p => x - 1) h2eq1
        simpa using this
      have hdiv : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).mp (by simpa only [Nat.cast_one] using hone)
      have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) hdiv
      omega
    · have hsle : s ≤ p - 1 := Nat.le_of_dvd (by omega) (hsEq ▸ hdvd_p1)
      omega
  refine ⟨M, hMgt1, hcop, S, hSsub, hMle, ?_⟩
  intro a b k ha hb heq
  rw [Finset.mem_Ico] at ha hb
  have halo : 6 * L ≤ a + b := by omega
  have habM : a + b < M := by
    dsimp [M]
    omega
  have hleft : (a + b) % M = a + b := Nat.mod_eq_of_lt habM
  have hcycle : (2 ^ k) % M = (2 ^ (k % s)) % M := by
    have hbase : 2 ^ s ≡ 1 [MOD M] := by
      rw [Nat.ModEq]
      have hsum : 2 ^ s = M + 1 := by omega
      rw [hsum]
      simp [hMgt1]
    have hk : 2 ^ k = 2 ^ (k % s) * (2 ^ s) ^ (k / s) := by
      conv_lhs => rw [← Nat.mod_add_div k s]
      rw [pow_add, pow_mul]
    rw [hk]
    have hm : 2 ^ (k % s) * (2 ^ s) ^ (k / s) ≡ 2 ^ (k % s) [MOD M] := by
      simpa using (Nat.ModEq.refl (2 ^ (k % s))).mul (Nat.ModEq.pow (k / s) hbase)
    exact hm
  have hrlt : k % s < s := Nat.mod_lt _ (by omega)
  have hrle : k % s ≤ s - 1 := by omega
  have h4L : 2 ^ (s - 1) = 4 * L := by
    dsimp [L]
    rw [show s - 1 = (s - 3) + 2 by omega, pow_add]
    norm_num
    ring
  have hpowle : 2 ^ (k % s) ≤ 4 * L := by
    calc
      2 ^ (k % s) ≤ 2 ^ (s - 1) := Nat.pow_le_pow_right (by norm_num) hrle
      _ = 4 * L := h4L
  have hpowlt : 2 ^ (k % s) < M := by
    dsimp [M]
    omega
  have hright : (2 ^ k) % M < 6 * L := by
    rw [hcycle, Nat.mod_eq_of_lt hpowlt]
    omega
  rw [hleft] at heq
  omega

end PEqualNP.Outside
