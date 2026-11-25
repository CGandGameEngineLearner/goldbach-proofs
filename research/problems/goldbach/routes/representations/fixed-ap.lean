import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Chebyshev

namespace GoldbachFixedAP
noncomputable section

def ap (q a n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k

def evenMass (n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (n+1)).filter (fun k => ¬Nat.Coprime k 2), ArithmeticFunction.vonMangoldt k

theorem liftFour (n : ℕ) :
    ap 2 1 n = ap 4 1 n + ap 4 3 n ∧
    ap 1 0 n = ap 4 1 n + ap 4 3 n + evenMass n := by
  unfold ap evenMass
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  constructor <;> apply Finset.sum_congr rfl <;> intro k _
  · split_ifs <;> first | omega | simp_all
  · have parity : Nat.Coprime k 2 ↔ k%2=1 := by rw [Nat.coprime_comm,Nat.coprime_two_left, Nat.odd_iff]
    simp only [parity]
    split_ifs <;> first | omega | simp_all

theorem normalization (q a n : ℕ) : ap q a n = ap q (a%q) n := by simp [ap]

abbrev ExplicitInput := ∀ q a n : ℕ, 3≤q → q≤105 → a<q → Nat.Coprime a q →
  8000000000≤n → |ap q a n-(n:ℝ)/q.totient| ≤ (n:ℝ)/(840*Real.log (n:ℝ))
abbrev Parent := ∀ q a n : ℕ, 1≤q → q≤105 → Nat.Coprime a q → 10^16≤n →
  (n:ℝ)<Real.exp (Real.exp (19/5)) → |ap q a n-(n:ℝ)/q.totient| ≤ (n:ℝ)/100

theorem fromBMOR (bmor : ExplicitInput)
    (nonunit : ∀ q n : ℕ, 1≤q → 1≤n →
      (∑ k ∈ (Finset.range (n+1)).filter (fun k => ¬ Nat.Coprime k q), ArithmeticFunction.vonMangoldt k)
        ≤ (q.primeFactors.card:ℝ)*Real.log n) : Parent := by
  intro q a n hq h105 cop hn hmax
  have hn1 : 1≤n := by omega
  have nr : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have log1 : 1≤Real.log (n:ℝ) := by
    have h3 : (3:ℝ)≤n := by exact_mod_cast (show 3≤n by omega)
    exact (Real.le_log_iff_exp_le nr).mpr (Real.exp_one_lt_d9.le.trans (by linarith))
  have small (q a : ℕ) (hq : 3≤q) (hu : q≤105) (ha : Nat.Coprime a q) :
      |ap q a n-(n:ℝ)/q.totient| ≤ (n:ℝ)/840 := by
    rw [normalization q a n]
    have hcop : Nat.Coprime (a%q) q := by
      change (a%q).gcd q = 1
      rw [← Nat.gcd_rec q a]
      exact ha.symm
    apply (bmor q (a%q) n hq hu (Nat.mod_lt _ (by omega)) hcop (by omega)).trans
    exact div_le_div_of_nonneg_left nr.le (by norm_num) (by linarith)
  by_cases h : 3≤q
  · linarith only [small q a h h105 cop,nr]
  have e1 := small 4 1 (by decide) (by decide) (by decide)
  have e3 := small 4 3 (by decide) (by decide) (by decide)
  rw [show Nat.totient 4=2 by decide] at e1 e3
  have both : |ap 4 1 n+ap 4 3 n-(n:ℝ)| ≤ 2*((n:ℝ)/840) := by
    rw [show ap 4 1 n+ap 4 3 n-(n:ℝ) = (ap 4 1 n-(n:ℝ)/2)+(ap 4 3 n-(n:ℝ)/2) by ring]
    exact (abs_add_le ..).trans (by norm_num at e1 e3 ⊢; linarith)
  rcases (show q=1 ∨ q=2 by omega) with rfl | rfl
  · have ev := nonunit 2 n (by decide) hn1
    change evenMass n ≤ _ at ev
    rw [show (Nat.primeFactors 2).card=1 by
      rw [Nat.prime_two.primeFactors]
      simp] at ev
    have epos : 0≤evenMass n := Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
    have lmax : Real.log (n:ℝ) < 81 := by
      have hb : Real.log (n:ℝ)<Real.exp (19/5) := (Real.log_lt_iff_lt_exp nr).mpr hmax
      have h4 : Real.exp (19/5) ≤ Real.exp ((4:ℕ)*1) := Real.exp_le_exp.mpr (by norm_num)
      rw [Real.exp_nat_mul] at h4
      have p : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      linarith only [hb,h4,pow_le_pow_left₀ (Real.exp_pos 1).le p 4]
    rw [normalization 1 a n,Nat.mod_one,(liftFour n).2,Nat.totient_one,Nat.cast_one,div_one]
    rw [show ap 4 1 n+ap 4 3 n+evenMass n-(n:ℝ)=(ap 4 1 n+ap 4 3 n-(n:ℝ))+evenMass n by ring]
    apply (abs_add_le ..).trans
    rw [abs_of_nonneg epos]
    have big : (10^16:ℝ)≤n := by exact_mod_cast hn
    norm_num at ev
    linarith
  · have ar : a%2=1 := by rw [Nat.coprime_comm,Nat.coprime_two_left,Nat.odd_iff] at cop; exact cop
    rw [normalization 2 a n,ar,(liftFour n).1,show Nat.totient 2=1 by decide,Nat.cast_one,div_one]
    linarith only [both,nr]

def theta (q a n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q),
    (if k.Prime then ArithmeticFunction.vonMangoldt k else 0)

def powers (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), (if k.Prime then 0 else ArithmeticFunction.vonMangoldt k)

theorem ap_theta (q a n : ℕ) : 0 ≤ ap q a n - theta q a n ∧
    ap q a n - theta q a n ≤ powers n := by
  unfold ap theta powers
  rw [← Finset.sum_sub_distrib, Finset.sum_filter]
  constructor
  · apply Finset.sum_nonneg
    intro k _
    split_ifs <;> simp_all [ArithmeticFunction.vonMangoldt_nonneg]
  · apply Finset.sum_le_sum
    intro k _
    split_ifs <;> simp_all [ArithmeticFunction.vonMangoldt_nonneg]

/-- The global contribution of all proper prime powers is below `n / 200` from `10^16`. -/
theorem higherPowers : ∀ n : ℕ, 10^16 ≤ n → powers n ≤ (n:ℝ)/200 := by
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hNpos : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hpsi : Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ) ≤
      2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := Chebyshev.psi_sub_theta_le hN
  have hsum_eq : powers n = Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ) := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
    simp only [powers, Finset.sum_filter]
    rw [Nat.floor_natCast]
    have hrange : Finset.range (n+1) = insert 0 (Finset.Ioc (0:ℕ) n) := by
      apply Finset.ext
      intro k
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
      constructor
      · intro h
        by_cases hk : k = 0
        · exact Or.inl hk
        · exact Or.inr ⟨Nat.pos_of_ne_zero hk, Nat.le_of_lt_succ h⟩
      · intro h
        rcases h with rfl | h
        · exact Nat.succ_pos n
        · exact Nat.lt_succ_of_le h.2
    rw [hrange, Finset.sum_insert (by simp)]
    have hzero : ArithmeticFunction.vonMangoldt 0 = 0 := by simp
    rw [ite_eq_right Nat.not_prime_zero, hzero, zero_add]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hp : k.Prime <;> simp [hp]
  rw [hsum_eq]
  have hlog : Real.log (n : ℝ) ≤ 4 * (n : ℝ) ^ (1/4 : ℝ) := by
    have h := Real.log_le_rpow_div hNpos.le (show (0:ℝ) < 1/4 by norm_num)
    convert h using 1
    field_simp
  have hmain : 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤
      8 * (n : ℝ) ^ (3/4 : ℝ) := by
    calc
      2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ)
          ≤ 2 * Real.sqrt (n : ℝ) * (4 * (n : ℝ) ^ (1/4 : ℝ)) := by gcongr
      _ = 8 * (Real.sqrt (n : ℝ) * (n : ℝ) ^ (1/4 : ℝ)) := by ring
      _ = 8 * ((n : ℝ) ^ (1/2 : ℝ) * (n : ℝ) ^ (1/4 : ℝ)) := by rw [Real.sqrt_eq_rpow]
      _ = 8 * (n : ℝ) ^ (3/4 : ℝ) := by
        rw [← Real.rpow_add hNpos]
        norm_num
  have hbase : (10000 : ℝ) ≤ (n : ℝ) ^ (1/4 : ℝ) := by
    have hpow : ((10^16 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hpow' : (10:ℝ)^16 ≤ (n:ℝ) := by norm_num at hpow ⊢; exact hpow
    have := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (10:ℝ)^16) hpow'
      (show (0:ℝ) ≤ 1/4 by norm_num)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 10)] at this
    norm_num at this
    exact this
  have hsmall : 8 * (n : ℝ) ^ (3/4 : ℝ) ≤ (n : ℝ) / 200 := by
    let x : ℝ := (n : ℝ) ^ (1/4 : ℝ)
    have hxpos : 0 < x := Real.rpow_pos_of_pos hNpos _
    have hx : 10000 ≤ x := hbase
    have hn_eq : (n : ℝ) = x^4 := by
      dsimp [x]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      norm_num
    have hn34 : (n : ℝ) ^ (3/4 : ℝ) = x^3 := by
      dsimp [x]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      norm_num
    have hxpow : x^3 * 1600 ≤ x^4 := by
      calc
        x^3 * 1600 ≤ x^3 * x := by
          exact mul_le_mul_of_nonneg_left (by linarith : (1600:ℝ) ≤ x) (pow_nonneg hxpos.le 3)
        _ = x^4 := by ring
    rw [hn34, hn_eq]
    calc
      (8:ℝ) * x^3 ≤ x^4 / 200 := by
        exact (le_div_iff₀ (by norm_num : (0:ℝ) < 200)).mpr (by nlinarith [hxpow])
  calc
    Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ)
        ≤ 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := hpsi
    _ ≤ 8 * (n : ℝ) ^ (3/4 : ℝ) := hmain
    _ ≤ (n:ℝ)/200 := hsmall

/-- The conditional route from the prime-only estimate and the global power budget. -/
theorem thetaReduction
    (primes : ∀ q a n : ℕ, 1 ≤ q → q ≤ 105 → Nat.Coprime a q → 10^16 ≤ n →
      (n:ℝ) < Real.exp (Real.exp (19/5)) → |theta q a n - (n:ℝ)/q.totient| ≤ (n:ℝ)/200)
    (higher : ∀ n : ℕ, 10^16 ≤ n → powers n ≤ (n:ℝ)/200) : Parent :=
  fromTheta primes higher

theorem fromTheta
    (primes : ∀ q a n : ℕ, 1 ≤ q → q ≤ 105 → Nat.Coprime a q → 10^16 ≤ n →
      (n:ℝ) < Real.exp (Real.exp (19/5)) → |theta q a n - (n:ℝ)/q.totient| ≤ (n:ℝ)/200)
    (higher : ∀ n : ℕ, 10^16 ≤ n → powers n ≤ (n:ℝ)/200) : Parent := by
  intro q a n hq h105 hcop hn hmax
  have ht := abs_le.mp (primes q a n hq h105 hcop hn hmax)
  obtain ⟨hlo,hhi⟩ := ap_theta q a n
  have hp := higher n hn
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hdecomp : ap q a n = theta q a n + (ap q a n - theta q a n) := by ring
  rw [hdecomp]
  apply abs_le.mpr
  constructor <;> linarith

end
end GoldbachFixedAP
