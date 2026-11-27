import Mathlib

/-!
# PREPUB twin-primes: `L-twin-primes-cofactor-sieve-root-count`
素模局部坏类计数：对素数模 `ℓ`，仿射同余 `r·a ≡ 2 (mod ℓ)`（`r` 奇素数）在 `{0,…,ℓ-1}`
中除 `a = 0` 外恰有一个解，除非 `ℓ = 2` 或 `ℓ = r`（此时 `2` 为 `0` 或 `r` 的倍数）
只剩 `a = 0`；故坏类数为 `if ℓ = 2 ∨ ℓ = r then 1 else 2`。自包含，仅 Mathlib。
-/

theorem Conjectures.TwinPrimes.CofactorSieveRootCount :
    ∀ (r ℓ : ℕ), r.Prime → 2 < r → ℓ.Prime →
      ((Finset.range ℓ).filter (fun a => a % ℓ = 0 ∨ (r*a) % ℓ = 2 % ℓ)).card =
        if ℓ = 2 ∨ ℓ = r then 1 else 2 := by
  intro r ℓ hr hr2 hℓ
  have hℓ2 : 2 ≤ ℓ := hℓ.two_le
  by_cases hcase : ℓ = 2 ∨ ℓ = r
  · -- degenerate cases: only `a = 0`
    rcases hcase with h2 | hrℓ
    · -- ℓ = 2
      have hrodd : r % 2 = 1 := by
        rcases hr.eq_two_or_odd with h | h
        · omega
        · exact h
      have hfilter : (Finset.range ℓ).filter
          (fun a => a % ℓ = 0 ∨ (r*a) % ℓ = 2 % ℓ) = {0} := by
        rw [h2]
        ext a
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        constructor
        · rintro ⟨ha, h0 | heq⟩
          · have : a = 0 ∨ a = 1 := by omega
            rcases this with h | h
            · exact h
            · rw [h] at h0; norm_num at h0
          · rw [show 2 % 2 = 0 by norm_num] at heq
            have : a = 0 ∨ a = 1 := by omega
            rcases this with h | h
            · exact h
            · rw [h, mul_one, hrodd] at heq
              norm_num at heq
        · rintro rfl
          exact ⟨by norm_num, Or.inl (by norm_num)⟩
      rw [hfilter, Finset.card_singleton, if_pos (Or.inl h2)]
    · -- ℓ = r
      rw [hrℓ]
      have hfilter : (Finset.range r).filter
          (fun a => a % r = 0 ∨ (r*a) % r = 2 % r) = {0} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        constructor
        · rintro ⟨ha, h0 | heq⟩
          · rw [Nat.mod_eq_of_lt ha] at h0; exact h0
          · exfalso
            have hmod : (r * a) % r = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right r a)
            rw [hmod] at heq
            have h2r : 2 % r = 2 := Nat.mod_eq_of_lt hr2
            rw [h2r] at heq
            norm_num at heq
        · rintro rfl
          exact ⟨by omega, Or.inl (Nat.zero_mod r)⟩
      rw [hfilter, Finset.card_singleton, if_pos (Or.inr rfl)]
  · -- non-degenerate: `{0} ∪ {a₀}` with `a₀` the unique nontrivial root
    push_neg at hcase
    obtain ⟨hℓ2ne, hℓrne⟩ := hcase
    have h2lt : 2 < ℓ := by
      rcases lt_or_eq_of_le hℓ2 with h | h
      · exact h
      · exact absurd h.symm hℓ2ne
    have h2mod : 2 % ℓ = 2 := Nat.mod_eq_of_lt h2lt
    have hndvd : ¬ ℓ ∣ r := by
      rintro ⟨k, hk⟩
      rcases hr.eq_one_or_self_of_dvd ℓ ⟨k, hk⟩ with h | h
      · omega
      · exact hℓrne h
    have _ : Fact ℓ.Prime := ⟨hℓ⟩
    have _ : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hr0 : (r : ZMod ℓ) ≠ 0 := by
      intro h
      exact hndvd ((ZMod.natCast_eq_zero_iff r ℓ).mp h)
    let w : ZMod ℓ := (2 : ZMod ℓ) / (r : ZMod ℓ)
    let a0 : ℕ := w.val
    have ha0cast : (a0 : ZMod ℓ) = w := ZMod.natCast_zmod_val w
    have hmul : (r : ZMod ℓ) * (a0 : ZMod ℓ) = (2 : ZMod ℓ) := by
      rw [ha0cast]
      dsimp only [w]
      field_simp
    have hmod : (r * a0) % ℓ = 2 % ℓ := by
      have hcast : ((r * a0 : ℕ) : ZMod ℓ) = (2 : ZMod ℓ) := by
        push_cast
        exact hmul
      exact (ZMod.natCast_eq_natCast_iff' (r*a0) 2 ℓ).mp hcast
    have ha0lt : a0 < ℓ := ZMod.val_lt w
    have ha0ne : a0 ≠ 0 := by
      intro h
      have hzero : (2 : ZMod ℓ) = 0 := by
        rw [← hmul, h]; simp
      have hdvd : ℓ ∣ 2 := (ZMod.natCast_eq_zero_iff 2 ℓ).mp hzero
      have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
      omega
    have hfilter : (Finset.range ℓ).filter
        (fun a => a % ℓ = 0 ∨ (r*a) % ℓ = 2 % ℓ) = {0, a0} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hv, h0 | heq⟩
        · left
          rw [Nat.mod_eq_of_lt hv] at h0; exact h0
        · right
          have hcast : ((r*v : ℕ) : ZMod ℓ) = ((r*a0 : ℕ) : ZMod ℓ) := by
            rw [ZMod.natCast_eq_natCast_iff' (r*v) (r*a0) ℓ]
            rw [heq, hmod]
          push_cast at hcast
          have hvv : (v : ZMod ℓ) = (a0 : ZMod ℓ) := mul_left_cancel₀ hr0 hcast
          have hvvmod : v % ℓ = a0 % ℓ := (ZMod.natCast_eq_natCast_iff' v a0 ℓ).mp hvv
          rwa [Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt ha0lt] at hvvmod
      · rintro (h | h)
        · subst h
          exact ⟨hℓ.pos, Or.inl (Nat.zero_mod ℓ)⟩
        · subst h
          exact ⟨ha0lt, Or.inr hmod⟩
    have hnot : (0 : ℕ) ∉ ({a0} : Finset ℕ) := by
      simp only [Finset.mem_singleton]
      exact fun h => ha0ne h.symm
    have hcard : ({0, a0} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem hnot]
      simp
    rw [hfilter, hcard, if_neg (not_or.mpr ⟨hℓ2ne, hℓrne⟩)]
