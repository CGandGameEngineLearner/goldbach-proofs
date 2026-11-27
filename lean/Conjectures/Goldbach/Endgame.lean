import Mathlib

theorem Conjectures.Goldbach.Endgame :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0;
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I);
    let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t));
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
    let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))};
    let low := fun (n k : ℕ) => if k^3≤n then w k else 0;
    let high := fun (n k : ℕ) => w k-low n k;
    let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t);
    let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume;
    let minor := fun n : ℕ => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun t => (S n w t)^2*E (-(n:ℝ)*t)) t) (0:ℝ) 1 MeasureTheory.volume;
    let major := fun n : ℕ => intervalIntegral (fun t => (arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; (((∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ n : ℕ, N≤n → Even n → c*(n:ℝ) ≤ (major n).re) → (∀ e : ℝ, 0<e → ∃ N : ℕ, ∀ n : ℕ, N≤n → Even n → -(e*(n:ℝ)) ≤ (minor n).re) → ∃ N : ℕ, ∀ n : ℕ, N≤n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n)) → ((∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ n : ℕ, N≤n → Even n → c*(n:ℝ) ≤ (major n).re)) → (∀ n:ℕ, I n w w=I n (low n) (low n)+2*I n (low n) (high n)+I n (high n) (high n)) → (∀ e:ℝ, 0<e → ∃ N:ℕ, ∀ n:ℕ, N≤n → ‖I n (low n) (low n)‖≤e*(n:ℝ)) → (∀ e:ℝ, 0<e → ∃ N:ℕ, ∀ n:ℕ, N≤n → ‖I n (low n) (high n)‖≤e*(n:ℝ)) → (∀ e:ℝ, 0<e → ∃ N:ℕ, ∀ n:ℕ, N≤n → Even n → -(e*(n:ℝ))≤(I n (high n) (high n)).re) → ∃ N:ℕ, ∀ n:ℕ, N≤n → Even n → ∃ p q:ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n := by
  intro w E S Q arcs low high f I minor major transfer majorFloor split lowLow lowHigh highHigh
  apply transfer majorFloor
  intro ε hε
  obtain ⟨Nll, hll⟩ := lowLow (ε / 4) (by positivity)
  obtain ⟨Nlh, hlh⟩ := lowHigh (ε / 4) (by positivity)
  obtain ⟨Nhh, hhh⟩ := highHigh (ε / 4) (by positivity)
  refine ⟨max Nll (max Nlh Nhh), ?_⟩
  intro n hn hEven
  have hll' := hll n ((le_max_left _ _).trans hn)
  have hn' : max Nlh Nhh ≤ n := (le_max_right _ _).trans hn
  have hlh' := hlh n ((le_max_left _ _).trans hn')
  have hhh' := hhh n ((le_max_right _ _).trans hn') hEven
  have hrealLowLow := (abs_le.mp ((Complex.abs_re_le_norm _).trans hll')).1
  have hrealLowHigh := (abs_le.mp ((Complex.abs_re_le_norm _).trans hlh')).1
  have hminor : minor n = I n w w := by simp only [minor, I, pow_two]
  have hre := congrArg Complex.re (split n)
  simp [Complex.add_re, Complex.mul_re] at hre
  rw [hminor, hre]
  linarith only [hrealLowLow, hrealLowHigh, hhh']
