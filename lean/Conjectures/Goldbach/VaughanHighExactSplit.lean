import Mathlib

set_option maxHeartbeats 2000000
open scoped Classical

theorem Conjectures.Goldbach.VaughanHighExactSplit :
  let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let Λ := ArithmeticFunction.vonMangoldt; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let U := fun n : ℕ => ⌊(n : ℝ) ^ (1 / 6 : ℝ)⌋₊; let u := fun (n m : ℕ) => if m ^ 3 ≤ n then 0 else (∑ d ∈ (Nat.divisors m).filter (fun d => d ≤ U n), μ d * Real.log ((m / d : ℕ) : ℝ)) - (∑ d ∈ (Nat.divisors m).filter (fun d => d ≤ U n), μ d * ∑ l ∈ (Nat.divisors (m / d)).filter (fun l => l ≤ U n), Λ l); let v := fun (n m : ℕ) => if m ^ 3 ≤ n then 0 else ∑ a ∈ (Nat.divisors m).filter (fun a => U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let highLambda := fun (n k : ℕ) => if k ^ 3 ≤ n then 0 else Λ k; (∀ n m : ℕ, highLambda n m = u n m + v n m) ∧ (∀ n : ℕ, I n (highLambda n) (highLambda n) = I n (u n) (u n) + 2 * I n (u n) (v n) + I n (v n) (v n)) := by
  intro E S Q arcs I Λ μ U u v high
  have point (n m : ℕ) : high n m = u n m + v n m := by
    by_cases hm : m^3 ≤ n
    · simp [high,u,v,hm]
    let Z : ArithmeticFunction ℝ := ArithmeticFunction.zeta
    let M : ArithmeticFunction ℝ := ArithmeticFunction.moebius
    let A : ArithmeticFunction ℝ := ⟨fun d => if d ≤ U n then M d else 0, by simp⟩
    let B : ArithmeticFunction ℝ := ⟨fun d => if d ≤ U n then Λ d else 0, by simp [Λ]⟩
    have hconv (f g : ArithmeticFunction ℝ) (j : ℕ) :
        (f*g) j = ∑ d ∈ j.divisors, f d * g (j/d) := by
      rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun i j => f i*g j)]
    have hM (j : ℕ) : M j = μ j := rfl
    have hA (j : ℕ) : A j = if j ≤ U n then μ j else 0 := rfl
    have hB (j : ℕ) : B j = if j ≤ U n then Λ j else 0 := rfl
    have hshort : U n < m := by
      by_contra bad
      have hnat : m ≤ U n := by omega
      have hreal : (m:ℝ) ≤ (n:ℝ)^(1/6:ℝ) :=
        (show (m:ℝ) ≤ (U n:ℝ) by exact_mod_cast hnat).trans (Nat.floor_le (by positivity))
      have hp := pow_le_pow_left₀ (Nat.cast_nonneg m) hreal 6
      rw [← Real.rpow_mul_natCast (by positivity : (0:ℝ) ≤ n)] at hp
      norm_num at hp
      have hp' : m^6 ≤ n := by exact_mod_cast hp
      have : m^3 ≤ m^6 := by rcases Nat.eq_zero_or_pos m with rfl | pos; simp; exact Nat.pow_le_pow_right pos (by decide)
      omega
    have ident : Λ = B + A*ArithmeticFunction.log - A*(B*Z) + ((M-A)*Z)*(Λ-B) := by
      have hz : M*Z = 1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
      have hl : Λ*Z = ArithmeticFunction.log := ArithmeticFunction.vonMangoldt_mul_zeta
      rw [← hl]
      calc Λ = B+(M*Z)*(Λ-B) := by rw [hz,one_mul]; ring
           _ = _ := by ring
    have hev := congrArg (fun f : ArithmeticFunction ℝ => f m) ident
    have hsub (f g : ArithmeticFunction ℝ) (i : ℕ) : (f-g) i = f i - g i := rfl
    change Λ m = B m + (A*ArithmeticFunction.log) m - (A*(B*Z)) m + (((M-A)*Z)*(Λ-B)) m at hev
    simp only [hB,
      if_neg (Nat.not_le_of_gt hshort),zero_add] at hev
    rw [hconv A ArithmeticFunction.log, hconv A (B*Z), hconv ((M-A)*Z) (Λ-B)] at hev
    have hrem (j : ℕ) : ((M-A)*Z) j = ∑ d ∈ j.divisors.filter (fun d => U n < d), μ d := by
      rw [ArithmeticFunction.coe_mul_zeta_apply, Finset.sum_filter]
      apply Finset.sum_congr rfl; intro d _
      simp only [hsub,hM,hA]
      by_cases hd : d ≤ U n <;> simp [hd, ← Nat.not_le]
    have hlow (j : ℕ) : (B*Z) j = ∑ d ∈ j.divisors.filter (fun d => d ≤ U n), Λ d := by
      rw [ArithmeticFunction.coe_mul_zeta_apply,Finset.sum_filter]
      rfl
    simp only [hsub,hB,hA,hrem,hlow,ArithmeticFunction.log_apply] at hev
    simp only [high,u,v,if_neg hm,Finset.sum_filter]
    simpa only [Finset.sum_filter, ite_mul, mul_ite, sub_ite, sub_self, sub_zero,
      zero_mul, mul_zero, ← Nat.not_le, ite_not] using hev
  refine ⟨point, ?_⟩
  intro n
  have hA : MeasurableSet (arcs n) := by
    dsimp only [arcs]; simp only [Set.ofPred_exists, Set.ofPred_and]; measurability
  have hi (a b : ℕ → ℝ) : IntervalIntegrable ((arcs n)ᶜ.indicator (fun t => S n a t*S n b t*E (-(n:ℝ)*t))) MeasureTheory.volume 0 1 := by
    have hc : Continuous (fun t => S n a t*S n b t*E (-(n:ℝ)*t)) := by dsimp only [S,E]; fun_prop
    exact ⟨(hc.intervalIntegrable 0 1).1.indicator hA.compl,(hc.intervalIntegrable 0 1).2.indicator hA.compl⟩
  have hadd (a b c : ℕ → ℝ) : I n (a+b) c = I n a c + I n b c := by
    dsimp only [I]
    rw [← intervalIntegral.integral_add (hi a c) (hi b c)]
    apply intervalIntegral.integral_congr; intro t _
    by_cases h : t ∈ (arcs n)ᶜ
    · simp only [Set.indicator_of_mem h,S,Pi.add_apply,Complex.ofReal_add,add_mul,Finset.sum_add_distrib]
    · simp [Set.indicator_of_notMem h]
  have hcomm (a b : ℕ → ℝ) : I n a b = I n b a := by dsimp only [I]; simp_rw [mul_comm (S n a _) (S n b _)]
  have hw : high n = u n + v n := funext (point n)
  rw [hw, hadd, hcomm (u n) (u n+v n), hcomm (v n) (u n+v n), hadd, hadd, hcomm (v n) (u n)]
  ring
