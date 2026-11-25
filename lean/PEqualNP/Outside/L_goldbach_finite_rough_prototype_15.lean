import Mathlib

private def covers (good : ℕ → Bool)  : ℕ → ℕ → Bool
  | 0, lo => good lo
  | k + 1, lo => covers good k lo && covers good k (lo+2^k)

private theorem covers_spec (good : ℕ → Bool) (d lo n : ℕ)
    (h : covers good d lo = true) (hlo : lo ≤ n) (hhi : n < lo+2^d) : good n = true := by
  induction d generalizing lo with
  | zero =>
    simp only [pow_zero] at hhi
    have he : n = lo := by omega
    simpa [covers, he] using h
  | succ d ih =>
    rw [covers, Bool.and_eq_true] at h
    rw [pow_succ] at hhi
    by_cases hs : n < lo+2^d
    · exact ih lo h.1 hlo hs
    · exact ih (lo+2^d) h.2 (by omega) (by omega)

private def good (i : ℕ) : Bool := ([3,5,7,11,31,43,61,79,149,197] : List ℕ).any (fun p => decide (Nat.Coprime ((2*i+30030-p) % 30030) 30030))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem wheelCheck : covers good 14 0 = true := by decide


private theorem wheel : ∀ a : ℕ, a < 30030 → Even a → ∃ p ∈ ({3,5,7,11,31,43,61,79,149,197} : Finset ℕ), Nat.Coprime ((a+30030-p) % 30030) 30030 := by
  intro a ha hev
  obtain ⟨i, hi⟩ := hev
  have h2 : a = 2*i := by omega
  have hpass := covers_spec good 14 0 i wheelCheck (by omega) (by norm_num; omega)
  rw [good, List.any_eq_true] at hpass
  obtain ⟨p, hp, hcop⟩ := hpass
  refine ⟨p, ?_, ?_⟩
  · simpa using hp
  · rw [h2]
    exact of_decide_eq_true hcop

set_option maxRecDepth 4096 in
private theorem liftCandidate : ∀ n : ℕ, 200 ≤ n → Even n → ∃ p : ℕ, Nat.Prime p ∧ p < n ∧ 2 ≤ n-p ∧ Nat.Coprime (n-p) 30030 := by
  intro n hn hev
  have he : Even (n % 30030) := by
    obtain ⟨i,hi⟩ := hev
    exact ⟨(n % 30030) / 2, by omega⟩
  obtain ⟨p, hp, hcp⟩ := wheel (n % 30030) (Nat.mod_lt _ (by decide)) he
  have prop : p.Prime ∧ p ≤ 197 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨p, prop.1, by omega, by omega, ?_⟩
  have heq : (n % 30030 + 30030 - p) % 30030 = (n-p) % 30030 := by omega
  rw [heq] at hcp
  change Nat.gcd (n-p) 30030 = 1
  rw [Nat.gcd_comm, Nat.gcd_rec 30030 (n-p)]
  exact hcp

private theorem factorPower : ∀ s y : ℕ, 2 ≤ s → 2 ≤ y → (∀ p, Nat.Prime p → p ∣ s → y ≤ p) → y^(s.primeFactorsList.length) ≤ s := by
  intro s y hs hy hdiv
  have hprod (l : List ℕ) (h : ∀ x ∈ l, y ≤ x) : y ^ l.length ≤ l.prod := by
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.length_cons, pow_succ, List.prod_cons, mul_comm a]
      exact Nat.mul_le_mul (ih (fun x hx => h x (List.mem_cons_of_mem _ hx))) (h a (by simp))
  calc
    y ^ s.primeFactorsList.length ≤ s.primeFactorsList.prod := hprod _ (by
      intro x hx
      exact hdiv x (Nat.prime_of_mem_primeFactorsList hx) (Nat.dvd_of_mem_primeFactorsList hx))
    _ = s := Nat.prod_primeFactorsList (by omega)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem smallPairs : ∀ a : Fin 200, 4 ≤ a.val → Even a.val →
    ∃ p ∈ ({2,3,5,7,11,13,17,19} : Finset ℕ), Nat.Prime p ∧ Nat.Prime (a.val-p) := by decide


private theorem powExpFrac (a b : ℕ) (hb : 0 < b) :
    (Real.exp ((a:ℝ)/b))^b = (Real.exp 1)^a := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  congr 1
  have hb' : (b:ℝ) ≠ 0 := by positivity
  field_simp

private theorem upperExp (a b : ℕ) (x : ℝ) (hb : 0 < b) (hx : 0 ≤ x)
    (hcert : (2718282 / 1000000 : ℝ)^a < x^b) : Real.exp ((a:ℝ)/b) < x := by
  have hu : Real.exp 1 ≤ 2718282 / 1000000 := by linarith [Real.exp_one_lt_d9]
  by_contra! hn
  have h1 : x^b ≤ (Real.exp ((a:ℝ)/b))^b := by gcongr
  rw [powExpFrac a b hb] at h1
  have h2 : (Real.exp 1)^a ≤ (2718282/1000000:ℝ)^a :=
    pow_le_pow_left₀ (Real.exp_pos _).le hu _
  exact (not_lt_of_ge (h1.trans h2)) hcert

private theorem lowerExp (a b : ℕ) (x : ℝ) (hb : 0 < b)
    (hcert : x^b < (2718281 / 1000000 : ℝ)^a) : x < Real.exp ((a:ℝ)/b) := by
  have hl : (2718281/1000000 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  by_contra! hn
  have h1 : (Real.exp ((a:ℝ)/b))^b ≤ x^b := by gcongr
  rw [powExpFrac a b hb] at h1
  have h2 : (2718281/1000000:ℝ)^a ≤ (Real.exp 1)^a := pow_le_pow_left₀ (by norm_num) hl _
  exact (not_lt_of_ge (h2.trans h1)) hcert


theorem PEqualNP.Outside.L_goldbach_finite_rough_prototype_15 : ∀ n : ℕ, 4 ≤ n → Even n → (n:ℝ) < Real.exp (Real.exp (19/5)) → ∃ p : ℕ, Nat.Prime p ∧ 2 ≤ n-p ∧ (n-p).primeFactorsList.length ≤ 15 := by
  intro n hn hev hupper
  by_cases hlo : n < 200
  · obtain ⟨p, _, hp, hq⟩ := smallPairs ⟨n,hlo⟩ hn hev
    exact ⟨p, hp, hq.two_le, by simp only [Nat.primeFactorsList_prime hq, List.length_cons, List.length_nil]; decide⟩
  obtain ⟨p, hp, hp_lt, hdiff, hcop⟩ := liftCandidate n (by omega) hev
  refine ⟨p, hp, hdiff, ?_⟩
  have hprime (q : ℕ) (hq : Nat.Prime q) (hd : q ∣ n - p) : 17 ≤ q := by
    by_contra! hsmall
    have ht : ∀ a : Fin 17, Nat.Prime a.val → a.val ∣ 30030 := by decide
    obtain h1 := Nat.eq_one_of_dvd_coprimes hcop hd (ht ⟨q,hsmall⟩ hq)
    exact hq.ne_one h1
  have hpower := factorPower (n-p) 17 hdiff (by decide) hprime
  by_contra! hlen
  have hh : (17:ℕ)^(16:ℕ) ≤ n := calc
    _ ≤ 17^(n-p).primeFactorsList.length := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ n-p := hpower
    _ ≤ n := Nat.sub_le _ _
  have hh' : (17:ℝ)^(16:ℕ) ≤ n := by exact_mod_cast hh
  have hl : (45/16:ℝ) < Real.log 17 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr (upperExp 45 16 17 (by decide) (by norm_num) (by norm_num))
  have hhx := upperExp 19 5 (4471/100) (by decide) (by norm_num) (by norm_num)
  norm_num only [Nat.cast_ofNat, div_one] at hhx
  have he : Real.exp (19/5) < (16:ℝ)*Real.log 17 := by linarith
  have hexp := Real.exp_lt_exp.mpr he
  rw [show (16:ℝ)*Real.log 17 = ((16:ℕ):ℝ)*Real.log 17 by norm_num, Real.exp_nat_mul, Real.exp_log (by norm_num)] at hexp
  exact (not_lt_of_ge hh') (hupper.trans hexp)
