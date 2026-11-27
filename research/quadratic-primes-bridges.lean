import Mathlib

open scoped BigOperators

namespace QuadraticPrimes

noncomputable section

private def block (x : ℕ) := Finset.Ioc x (2 * x)
private def budget (x : ℕ) : ℝ := (x : ℝ) * Real.log x
private def roots (a p : ℕ) :=
  (Finset.range p).filter fun r => p ∣ r ^ 2 + a
private def primes (x : ℕ) :=
  (Finset.Ioc x ((2 * x) ^ 2 + 1)).filter fun p =>
    p.Prime ∧ p ^ 100000 ≤ (2 * x) ^ 132301
private def window (x p : ℕ) :=
  (block x).filter fun n => p ^ 100000 ≤ n ^ 132301
private def band (a x n : ℕ) :=
  (n ^ 2 + a).primeFactors.filter fun p => x < p ∧ p ^ 100000 ≤ n ^ 132301

private def middleMass (a x : ℕ) : ℝ :=
  ∑ n ∈ block x, ∑ p ∈ band a x n, ((n ^ 2 + a).factorization p : ℝ) * Real.log p

private def repeatMass (a x : ℕ) : ℝ :=
  ∑ n ∈ block x, ∑ p ∈ band a x n,
    (((n ^ 2 + a).factorization p - 1 : ℕ) : ℝ) * Real.log p

private def incidenceMass (a x : ℕ) : ℝ :=
  ∑ p ∈ primes x, (((window x p).filter fun n => p ∣ n ^ 2 + a).card : ℝ) * Real.log p

private def zeroMode (a x : ℕ) : ℝ :=
  ∑ p ∈ primes x, ((window x p).card : ℝ) * ((roots a p).card : ℝ) / p * Real.log p

private def angle (p k : ℕ) (t : ℝ) := 2 * Real.pi * k * t / p

private def coefficient (a x p k : ℕ) : ℝ :=
  (∑ r ∈ roots a p, ∑ n ∈ window x p, Real.cos (angle p k ((n : ℝ) - r))) / p

private def frequencies (p : ℕ) (low : Bool) :=
  (Finset.Ico 1 p).filter fun k =>
    if low then min k (p - k) ≤ Nat.sqrt p else Nat.sqrt p < min k (p - k)

private def modes (a x : ℕ) (low : Bool) : ℝ :=
  ∑ p ∈ primes x, (∑ k ∈ frequencies p low, coefficient a x p k) * Real.log p

/-- QP-0063. Choose the high-mode witness beyond all eventual thresholds. -/
theorem middleSavingBridge
    (zeroBound : ∃ t : ℕ, ∀ x ≥ t, zeroMode 1 x ≤ (2 / 5 : ℝ) * budget x)
    (splitModes : ∀ x, incidenceMass 1 x = zeroMode 1 x + modes 1 x true + modes 1 x false)
    (repeatBound : ∃ t : ℕ, ∀ x ≥ t, repeatMass 1 x ≤ (1 / 100 : ℝ) * budget x)
    (lowBound : ∃ t : ℕ, ∀ x ≥ t, modes 1 x true ≤ (1 / 5 : ℝ) * budget x)
    (highBound : ∀ B : ℕ, ∃ x : ℕ, B < x ∧ modes 1 x false ≤ (19 / 50 : ℝ) * budget x)
    (splitMass : ∀ a x : ℕ, 0 < a → middleMass a x = incidenceMass a x + repeatMass a x) :
    ∃ d : ℝ, 0 < d ∧ ∀ B : ℕ, ∃ x : ℕ,
      B < x ∧ middleMass 1 x ≤ (1 - d) * (x : ℝ) * Real.log x := by
  obtain ⟨zeroThreshold, hzero⟩ := zeroBound
  obtain ⟨repeatThreshold, hrepeat⟩ := repeatBound
  obtain ⟨lowThreshold, hlow⟩ := lowBound
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro B
  obtain ⟨x, hx, hhigh⟩ := highBound (max (max B zeroThreshold) (max repeatThreshold lowThreshold))
  refine ⟨x, by omega, ?_⟩
  rw [splitMass 1 x (by decide), splitModes x, mul_assoc]
  change zeroMode 1 x + modes 1 x true + modes 1 x false + repeatMass 1 x ≤
    (1 - 1 / 100 : ℝ) * budget x
  linarith only [hzero x (by omega), hlow x (by omega), hhigh, hrepeat x (by omega)]

private def mangoldtMass (x : ℕ) : ℝ :=
  ∑ n ∈ block x, ArithmeticFunction.vonMangoldt (n ^ 2 + 1)

private def powerMass (x : ℕ) : ℝ :=
  ∑ n ∈ (block x).filter (fun n => ¬ (n ^ 2 + 1).Prime),
    ArithmeticFunction.vonMangoldt (n ^ 2 + 1)

private def primeMass (x : ℕ) : ℝ :=
  ∑ n ∈ (block x).filter (fun n => (n ^ 2 + 1).Prime), Real.log ((n ^ 2 + 1 : ℕ) : ℝ)

/-- QP-0071. A linear Mangoldt lower bound dominates the proper-power mass. -/
theorem primeValuesBridge
    (powerBound : ∀ ε : ℝ, 0 < ε → ∃ t : ℕ, ∀ x ≥ t, powerMass x ≤ ε * x)
    (splitMass : ∀ x, mangoldtMass x = primeMass x + powerMass x)
    (recurrent : ∃ c : ℝ, 0 < c ∧ ∀ B : ℕ, ∃ x : ℕ, B < x ∧ c * x ≤ mangoldtMass x)
    (extract : ∀ x, 0 < primeMass x → ∃ n ∈ block x, ∃ p : ℕ, p.Prime ∧ n ^ 2 + 1 = p) :
    ∀ B : ℕ, ∃ n p : ℕ, B < n ∧ p.Prime ∧ p ∣ n ^ 2 + 1 ∧ n ^ 2 < p ^ 1 := by
  obtain ⟨c, hc, hmass⟩ := recurrent
  obtain ⟨threshold, hpower⟩ := powerBound (c / 2) (by linarith)
  intro B
  obtain ⟨x, hx, hlower⟩ := hmass (max B threshold)
  have xpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hprod := mul_pos hc xpos
  obtain ⟨n, hn, p, hp, heq⟩ :=
    extract x (by linarith only [hpower x (by omega), splitMass x, hlower, hprod])
  have hxn : x < n := (Finset.mem_Ioc.mp hn).1
  exact ⟨n, p, by omega, hp, heq ▸ dvd_refl _, by simp [← heq]⟩

end

end QuadraticPrimes
