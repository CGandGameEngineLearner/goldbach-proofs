import Mathlib

open scoped Classical
set_option maxHeartbeats 2000000

theorem Conjectures.Goldbach.BulkOffCoherenceTransfer :
  (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let J := fun (n : ℕ) (v : ℝ → ℝ) => (intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => (v u:ℂ)*S n (high n) u*S n (high n) u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume).re; let τ := fun n : ℕ => 1/(2304*(1+(Real.log (n:ℝ))^2)); let small := fun (n : ℕ) (t : ℝ) => max (-(τ n)) (min (τ n) (1-K n t)); ∀ n : ℕ, 2 ≤ n → |J n (small n)| ≤ (n:ℝ)/1152) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let J := fun (n : ℕ) (v : ℝ → ℝ) => (intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => (v u:ℂ)*S n (high n) u*S n (high n) u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume).re; let τ := fun n : ℕ => 1/(2304*(1+(Real.log (n:ℝ))^2)); let small := fun (n : ℕ) (t : ℝ) => max (-(τ n)) (min (τ n) (1-K n t)); ∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/1152 ≤ J n (fun t => 1-K n t-small n t)) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let J := fun (n : ℕ) (v : ℝ → ℝ) => (intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => (v u:ℂ)*S n (high n) u*S n (high n) u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume).re; ∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/576 ≤ J n (fun t => 1-K n t)) := by
  intro hsmall hrest w E S Q arcs low high I L K J
  let τ := fun n : ℕ => 1/(2304*(1+(Real.log (n:ℝ))^2))
  let small := fun (n : ℕ) (t : ℝ) => max (-(τ n)) (min (τ n) (1-K n t))
  change ∀ n : ℕ, 2 ≤ n → |J n (small n)| ≤ (n:ℝ)/1152 at hsmall
  change ∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/1152 ≤ J n (fun t => 1-K n t-small n t) at hrest
  obtain ⟨N,hN⟩ := hrest
  refine ⟨max N 2, ?_⟩
  intro n hn he
  have hs := (abs_le.mp (hsmall n (by omega))).1
  have hr := hN n (by omega) he
  have hA : MeasurableSet (arcs n) := by
    dsimp only [arcs]
    simp only [Set.ofPred_exists, Set.ofPred_and]
    measurability
  let f := fun t : ℝ => S n (high n) t * S n (high n) t * E (-(n:ℝ)*t)
  let F := fun (v : ℝ → ℝ) t => (arcs n)ᶜ.indicator (fun u => (v u:ℂ) * f u) t
  have hc : Continuous f := by dsimp [f,S,E]; fun_prop
  have hK : Continuous (K n) := by dsimp [K]; fun_prop
  have hsm : Continuous (small n) := continuous_const.max (continuous_const.min (continuous_const.sub hK))
  have hi (v : ℝ → ℝ) (hv : Continuous v) :
      IntervalIntegrable (F v) MeasureTheory.volume 0 1 := by
    have hh := ((Complex.continuous_ofReal.comp hv).mul hc).intervalIntegrable (μ := MeasureTheory.volume) 0 1
    exact ⟨hh.1.indicator hA.compl, hh.2.indicator hA.compl⟩
  let r := fun t => 1-K n t-small n t
  have hlin : J n (fun t => 1-K n t) = J n (small n) + J n r := by
    have hadd : F (fun t => 1-K n t) = fun t => F (small n) t + F r t := by
      funext t
      by_cases ht : t ∈ (arcs n)ᶜ
      · simp only [F, r, Set.indicator_of_mem ht, Complex.ofReal_sub, Complex.ofReal_one]
        ring
      · simp [F, Set.indicator_of_notMem ht]
    have hh := intervalIntegral.integral_add (hi _ hsm) (hi r ((continuous_const.sub hK).sub hsm))
    rw [← hadd] at hh
    simpa only [F, f, J, Complex.add_re, mul_assoc] using congrArg Complex.re hh
  change -(n:ℝ)/1152 ≤ J n r at hr
  rw [hlin]
  linarith
