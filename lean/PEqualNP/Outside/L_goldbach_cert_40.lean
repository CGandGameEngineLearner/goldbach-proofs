import Mathlib

private def goldbachCert40Term (a b : Nat) : Complex :=
  Complex.exp (((2 * Real.pi * (a : Real) * b / 40 : Real) : Complex) * Complex.I)

private lemma goldbachCert40Shift (a : Nat) (ha : Odd a) (b : Nat) :
    goldbachCert40Term a (b + 20) = -goldbachCert40Term a b := by
  unfold goldbachCert40Term
  have harg :
      (((2 * Real.pi * (a : Real) * (b + 20) / 40 : Real) : Complex) * Complex.I) =
        (((2 * Real.pi * (a : Real) * b / 40 : Real) : Complex) * Complex.I) +
          (((Real.pi * (a : Real) : Real) : Complex) * Complex.I) := by
    push_cast
    ring
  have hphaseArg :
      (((Real.pi * (a : Real) : Real) : Complex) * Complex.I) =
        (a : Complex) * (Real.pi * Complex.I) := by
    push_cast
    ring
  have hphase :
      Complex.exp (((Real.pi * (a : Real) : Real) : Complex) * Complex.I) = -1 := by
    rw [hphaseArg]
    calc
      Complex.exp ((a : Complex) * (Real.pi * Complex.I)) =
          Complex.exp (Real.pi * Complex.I) ^ a := Complex.exp_nat_mul _ _
      _ = (-1 : Complex) ^ a := by rw [Complex.exp_pi_mul_I]
      _ = -1 := ha.neg_one_pow
  rw [harg, Complex.exp_add, hphase]
  ring

theorem PEqualNP.Outside.L_goldbach_cert_40 :
    forall a : Nat, Nat.Coprime a 40 ->
      Finset.sum ((Finset.range 40).filter (fun b => Nat.Coprime b 40))
        (fun b => Complex.exp (((2 * Real.pi * (a : Real) * b / 40 : Real) : Complex) * Complex.I)) /
          (16 : Complex) = (0 : Complex) / 16 := by
  intro a ha
  have haOdd : Odd a := by
    by_contra hNotOdd
    have hEven : Even a := (even_or_odd a).resolve_right hNotOdd
    cases hEven with
    | intro k hk =>
      have hdiv : Dvd.dvd 2 a := Exists.intro k (by omega)
      have hgcd : Dvd.dvd 2 (Nat.gcd a 40) := Nat.dvd_gcd hdiv (by norm_num)
      have hcop : Nat.gcd a 40 = 1 := ha.gcd_eq_one
      rw [hcop] at hgcd
      omega
  have hunitSet :
      (Finset.range 40).filter (fun b => Nat.Coprime b 40) =
        ({1, 21, 3, 23, 7, 27, 9, 29, 11, 31, 13, 33, 17, 37, 19, 39} : Finset Nat) := by
    decide
  have hsum :
      Finset.sum ((Finset.range 40).filter (fun b => Nat.Coprime b 40))
        (fun b => goldbachCert40Term a b) = 0 := by
    rw [hunitSet]
    simp [Finset.sum_insert]
    have h21 : goldbachCert40Term a 21 = -goldbachCert40Term a 1 := by
      simpa using goldbachCert40Shift a haOdd 1
    have h23 : goldbachCert40Term a 23 = -goldbachCert40Term a 3 := by
      simpa using goldbachCert40Shift a haOdd 3
    have h27 : goldbachCert40Term a 27 = -goldbachCert40Term a 7 := by
      simpa using goldbachCert40Shift a haOdd 7
    have h29 : goldbachCert40Term a 29 = -goldbachCert40Term a 9 := by
      simpa using goldbachCert40Shift a haOdd 9
    have h31 : goldbachCert40Term a 31 = -goldbachCert40Term a 11 := by
      simpa using goldbachCert40Shift a haOdd 11
    have h33 : goldbachCert40Term a 33 = -goldbachCert40Term a 13 := by
      simpa using goldbachCert40Shift a haOdd 13
    have h37 : goldbachCert40Term a 37 = -goldbachCert40Term a 17 := by
      simpa using goldbachCert40Shift a haOdd 17
    have h39 : goldbachCert40Term a 39 = -goldbachCert40Term a 19 := by
      simpa using goldbachCert40Shift a haOdd 19
    rw [h21, h23, h27, h29, h31, h33, h37, h39]
    ring
  change Finset.sum ((Finset.range 40).filter (fun b => Nat.Coprime b 40))
      (fun b => goldbachCert40Term a b) / (16 : Complex) = (0 : Complex) / 16
  rw [hsum]
