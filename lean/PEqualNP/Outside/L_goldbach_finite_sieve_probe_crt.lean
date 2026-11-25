import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_sieve_probe_crt :
    ∀ n d e : ℕ, 0 < d → 0 < e → (∃ p : ℕ, p % d = n % d ∧ p % e = 1 % e) ↔ n % (Nat.gcd d e) = 1 % (Nat.gcd d e) := by
  intro n d e hd he
  constructor
  · rintro ⟨p, hpd, hpe⟩
    have hd1 : p % Nat.gcd d e = p % d % Nat.gcd d e :=
      (Nat.mod_mod_of_dvd p (Nat.gcd_dvd_left d e)).symm
    have hd2 : n % Nat.gcd d e = n % d % Nat.gcd d e :=
      (Nat.mod_mod_of_dvd n (Nat.gcd_dvd_left d e)).symm
    have he1 : p % Nat.gcd d e = p % e % Nat.gcd d e :=
      (Nat.mod_mod_of_dvd p (Nat.gcd_dvd_right d e)).symm
    have he2 : 1 % Nat.gcd d e = 1 % e % Nat.gcd d e :=
      (Nat.mod_mod_of_dvd 1 (Nat.gcd_dvd_right d e)).symm
    rw [hd2, ← hpd, ← hd1, he1, hpe, ← he2]
  · intro hg
    set g := Nat.gcd d e
    have hbez : (g : ℤ) = (d : ℤ) * Nat.gcdA d e + (e : ℤ) * Nat.gcdB d e :=
      Nat.gcd_eq_gcd_ab d e
    have hng : (1 : ℤ) - (n : ℤ) = (g : ℤ) * (((1 / g : ℕ) : ℤ) - ((n / g : ℕ) : ℤ)) := by
      have h1 : g * (1 / g) + 1 % g = 1 := Nat.div_add_mod 1 g
      have h2 : g * (n / g) + n % g = n := Nat.div_add_mod n g
      have h1z : (g : ℤ) * ((1 / g : ℕ) : ℤ) + ((1 % g : ℕ) : ℤ) = 1 := by exact_mod_cast h1
      have h2z : (g : ℤ) * ((n / g : ℕ) : ℤ) + ((n % g : ℕ) : ℤ) = (n : ℤ) := by exact_mod_cast h2
      have hgz : ((n % g : ℕ) : ℤ) = ((1 % g : ℕ) : ℤ) := by exact_mod_cast hg
      rw [mul_sub]
      linarith
    set k : ℤ := ((1 / g : ℕ) : ℤ) - ((n / g : ℕ) : ℤ)
    set x : ℤ := (n : ℤ) + (d : ℤ) * (Nat.gcdA d e * k)
    set m : ℤ := (d : ℤ) * (e : ℤ)
    have hm_ne : m ≠ 0 := by
      have hd0 : (d : ℤ) ≠ 0 := by omega
      have he0 : (e : ℤ) ≠ 0 := by omega
      exact mul_ne_zero hd0 he0
    have hr_nonneg : 0 ≤ x % m := Int.emod_nonneg x hm_ne
    refine ⟨(x % m).toNat, ?_, ?_⟩
    · have hpz : (((x % m).toNat : ℕ) : ℤ) = x % m := Int.toNat_of_nonneg hr_nonneg
      have hdiv : m * (x / m) + x % m = x := Int.ediv_add_emod x m
      have hstep : (((x % m).toNat : ℕ) : ℤ) = (n : ℤ) + (d : ℤ) * (Nat.gcdA d e * k - (e : ℤ) * (x / m)) := by
        rw [hpz, show x % m = x - m * (x / m) by linarith]
        dsimp only [x, m]
        ring
      have hmod : (((x % m).toNat : ℕ) : ℤ) % (d : ℤ) = (n : ℤ) % (d : ℤ) := by
        rw [hstep, Int.add_mul_emod_self_left]
      exact Int.ofNat.inj (by rw [Int.natCast_emod, Int.natCast_emod]; exact hmod)
    · have hpz : (((x % m).toNat : ℕ) : ℤ) = x % m := Int.toNat_of_nonneg hr_nonneg
      have hdiv : m * (x / m) + x % m = x := Int.ediv_add_emod x m
      have hstep : (((x % m).toNat : ℕ) : ℤ) = (1 : ℤ) + (e : ℤ) * (-(Nat.gcdB d e * k) - (d : ℤ) * (x / m)) := by
        rw [hpz, show x % m = x - m * (x / m) by linarith]
        dsimp only [x, m]
        rw [show (n : ℤ) = 1 - (g : ℤ) * k by linarith, hbez]
        ring
      have hmod : (((x % m).toNat : ℕ) : ℤ) % (e : ℤ) = (1 : ℤ) % (e : ℤ) := by
        rw [hstep, Int.add_mul_emod_self_left]
      exact Int.ofNat.inj (by rw [Int.natCast_emod, Int.natCast_emod, Nat.cast_one]; exact hmod)
