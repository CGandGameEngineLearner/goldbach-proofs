import Mathlib

set_option maxRecDepth 3000 in
theorem PEqualNP.Outside.L_goldbach_finite_rough_prototype_61 :
    ∀ n : ℕ, 4 ≤ n → Even n → (n:ℝ) < Real.exp (Real.exp 5) → ∃ p : ℕ, Nat.Prime p ∧ 2 ≤ n-p ∧ (n-p).primeFactorsList.length ≤ 61 := by
  intro n hn heven htop
  by_cases hsmall : n < 22
  · have small : ∀ a : Fin 22, 4 ≤ a.val → a.val % 2 = 0 → ∃ p : Fin 20,
          p.val.Prime ∧ (a.val-p.val).Prime := by decide
    obtain ⟨p, hp, hq⟩ := small ⟨n,hsmall⟩ hn (by obtain ⟨k,hk⟩ := heven; change n % 2 = 0; omega)
    refine ⟨p.val, hp, hq.two_le, ?_⟩
    change (n-p.val).Prime at hq
    rw [Nat.primeFactorsList_prime hq]
    simp
  have table : ∀ a : Fin 210, a.val % 2 = 0 → ∃ p : Fin 20,
      p.val.Prime ∧ (a.val + 210 - p.val).Coprime 210 := by decide
  let r : Fin 210 := ⟨n % 210, Nat.mod_lt _ (by decide)⟩
  have hpar : r.val % 2 = 0 := by
    obtain ⟨k, hk⟩ := heven
    dsimp [r]
    omega
  obtain ⟨p, hp, hcop⟩ := table r hpar
  have hp_lt := p.isLt
  have hs : 2 ≤ n - p.val := by omega
  have hmod : Nat.ModEq 210 (n-p.val) (r.val+210-p.val) := by
    change (n - p.val) % 210 = (n % 210 + 210 - p.val) % 210
    omega
  have hcop' : Nat.Coprime (n-p.val) 210 := hmod.gcd_eq.trans hcop
  have rough : ∀ q ∈ (n-p.val).primeFactorsList, 11 ≤ q := by
    intro q hq
    by_contra! hsmallq
    have prime := Nat.prime_of_mem_primeFactorsList hq
    have hdiv := Nat.dvd_of_mem_primeFactorsList hq
    have bad : ∀ x : Fin 11, x.val.Prime → x.val ∣ 210 := by decide
    have hone := Nat.eq_one_of_dvd_coprimes hcop' hdiv (bad ⟨q,hsmallq⟩ prime)
    exact prime.ne_one hone
  have listBound (xs : List ℕ) (h : ∀ q ∈ xs, 11 ≤ q) : 11^xs.length ≤ xs.prod := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      rw [List.length_cons, pow_succ', List.prod_cons]
      exact Nat.mul_le_mul (h _ (by simp)) (ih (fun q hq => h _ (by simp [hq])))
  have hpower := listBound _ rough
  rw [Nat.prod_primeFactorsList (by omega)] at hpower
  have he : Real.exp 1 ≤ (27183/10000:ℝ) := by linarith only [Real.exp_one_lt_d9]
  have he5 : Real.exp 5 < 297/2 := calc
    Real.exp 5 = Real.exp 1 ^ (5:ℕ) := (Real.exp_one_pow 5).symm
    _ ≤ (27183/10000:ℝ)^5 := pow_le_pow_left₀ (Real.exp_pos _).le he _
    _ < _ := by norm_num
  have he297 : Real.exp 1 ^ (297:ℕ) < (11:ℝ)^124 := calc
    _ ≤ (27183/10000:ℝ)^297 := pow_le_pow_left₀ (Real.exp_pos _).le he _
    _ < _ := by
      rw [div_pow, div_lt_iff₀ (by positivity)]
      exact_mod_cast (show (27183:ℕ)^297 < 11^124 * 10000^297 by decide)
  have hlogs := Real.log_lt_log (by positivity) he297
  rw [Real.log_pow, Real.log_pow, Real.log_exp, mul_one] at hlogs
  norm_num at hlogs
  have hcap : (n:ℝ) < (11:ℝ)^62 := calc
    _ < Real.exp (Real.exp 5) := htop
    _ < Real.exp (62 * Real.log 11) := Real.exp_lt_exp.mpr (by linarith only [he5, hlogs])
    _ = (11:ℝ)^62 := by
      have hlogpow := Real.log_pow (11:ℝ) 62
      norm_num only [Nat.cast_ofNat] at hlogpow
      rw [← hlogpow, Real.exp_log (by positivity)]
      norm_num
  refine ⟨p.val, hp, hs, ?_⟩
  by_contra! hlong
  have hpow62 : (11:ℕ)^62 ≤ 11^(n-p.val).primeFactorsList.length :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hn62 : (11:ℕ)^62 ≤ n := hpow62.trans (hpower.trans (Nat.sub_le _ _))
  exact (not_le_of_gt hcap) (by exact_mod_cast hn62)
