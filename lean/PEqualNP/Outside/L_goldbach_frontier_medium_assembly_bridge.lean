import Mathlib

/-!
# Medium-arc assembly bridge

Six inputs, each with its own epsilon threshold: the model floor on the whole
band, three modulus-band approximation errors, and two skirt floors. Allocating
epsilon/8 to each input and taking the sum of the thresholds yields the
medium-arc floor at scale epsilon. The three decomposition identities split the
core and the skirt into bands before the real parts are combined.
-/

private lemma complex_re_lower_of_norm_sub {z w : ℂ} {c : ℝ} (h : ‖z - w‖ ≤ c) :
    w.re - c ≤ z.re := by
  have h1 : -((z - w).re) ≤ ‖z - w‖ :=
    (neg_le_abs (z - w).re).trans (Complex.abs_re_le_norm (z - w))
  have h2 : (z - w).re = z.re - w.re := Complex.sub_re z w
  linarith

theorem PEqualNP.Outside.L_goldbach_frontier_medium_assembly_bridge :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let midArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let medCore := fun n : ℕ => intervalIntegral (fun t => (midArcs n \ arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let medSkirt := fun n : ℕ => intervalIntegral (fun t => (wideArcs n \ midArcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let Qqp := fun n : ℕ => ⌊Real.exp (Real.sqrt (Real.log (n:ℝ)))⌋₊; let Qzf := fun n : ℕ => ⌊(n:ℝ)^(1/10:ℝ)⌋₊; let K := fun (n : ℕ) (β : ℝ) => ∑ k ∈ Finset.range (n+1), E ((k:ℝ)*β); let medCoreBand := fun (n A B : ℕ) => intervalIntegral (fun t => {u : ℝ | ∃ q a : ℕ, A < q ∧ q ≤ B ∧ a ≤ q ∧ Nat.Coprime a q ∧ |u - (a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let modelBand := fun (n A B : ℕ) => ∑ q ∈ Finset.Ioc A B, ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), intervalIntegral (fun t => (((∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), E ((r:ℝ)*(a:ℝ)/(q:ℝ))) / (Nat.totient q : ℂ)) * K n (t - (a:ℝ)/(q:ℝ)))^2 * E (-(n:ℝ)*t)) ((a:ℝ)/(q:ℝ) - (Q n:ℝ)/((q:ℝ)*(n:ℝ))) ((a:ℝ)/(q:ℝ) + (Q n:ℝ)/((q:ℝ)*(n:ℝ))) MeasureTheory.volume; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowSkirt := fun n : ℕ => intervalIntegral (fun t => (lowWideArcs n \ arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let remSkirt := fun n : ℕ => intervalIntegral (fun t => ((wideArcs n \ midArcs n) \ (lowWideArcs n \ arcs n)).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → medCore n = medCoreBand n (Q n) (Qqp n) + medCoreBand n (Qqp n) (Qzf n) + medCoreBand n (Qzf n) (Q₁ n) ∧ modelBand n (Q n) (Q₁ n) = modelBand n (Q n) (Qqp n) + modelBand n (Qqp n) (Qzf n) + modelBand n (Qzf n) (Q₁ n) ∧ medSkirt n = lowSkirt n + remSkirt n) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (modelBand n (Q n) (Q₁ n)).re) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖medCoreBand n (Q n) (Qqp n) - modelBand n (Q n) (Qqp n)‖ ≤ e * (n : ℝ)) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖medCoreBand n (Qqp n) (Qzf n) - modelBand n (Qqp n) (Qzf n)‖ ≤ e * (n : ℝ)) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖medCoreBand n (Qzf n) (Q₁ n) - modelBand n (Qzf n) (Q₁ n)‖ ≤ e * (n : ℝ)) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (lowSkirt n).re) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (remSkirt n).re) → ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (medCore n + medSkirt n).re := by
  classical
  intro w E S Q arcs f Q₁ H midArcs wideArcs medCore medSkirt Qqp Qzf K medCoreBand modelBand
    lowWideArcs lowSkirt remSkirt hdec hmod hb1 hb2 hb3 hlow hrem e he
  obtain ⟨N0, hN0⟩ := hdec
  have he8 : 0 < e / 8 := by linarith
  obtain ⟨N1, hN1⟩ := hmod (e / 8) he8
  obtain ⟨N2, hN2⟩ := hb1 (e / 8) he8
  obtain ⟨N3, hN3⟩ := hb2 (e / 8) he8
  obtain ⟨N4, hN4⟩ := hb3 (e / 8) he8
  obtain ⟨N5, hN5⟩ := hlow (e / 8) he8
  obtain ⟨N6, hN6⟩ := hrem (e / 8) he8
  refine ⟨N0 + N1 + N2 + N3 + N4 + N5 + N6, ?_⟩
  intro n hn hEven
  have h0 : N0 ≤ n := by omega
  have h1 : N1 ≤ n := by omega
  have h2 : N2 ≤ n := by omega
  have h3 : N3 ≤ n := by omega
  have h4 : N4 ≤ n := by omega
  have h5 : N5 ≤ n := by omega
  have h6 : N6 ≤ n := by omega
  obtain ⟨hMed, hMod, hSk⟩ := hN0 n h0
  have hm' : -(e / 8 * (n : ℝ)) ≤
      (modelBand n (Q n) (Qqp n)).re + (modelBand n (Qqp n) (Qzf n)).re
        + (modelBand n (Qzf n) (Q₁ n)).re := by
    have h := hN1 n h1 hEven
    rw [hMod] at h
    simpa only [Complex.add_re] using h
  have hA : (modelBand n (Q n) (Qqp n)).re - e / 8 * (n : ℝ) ≤
      (medCoreBand n (Q n) (Qqp n)).re :=
    complex_re_lower_of_norm_sub (hN2 n h2 hEven)
  have hB : (modelBand n (Qqp n) (Qzf n)).re - e / 8 * (n : ℝ) ≤
      (medCoreBand n (Qqp n) (Qzf n)).re :=
    complex_re_lower_of_norm_sub (hN3 n h3 hEven)
  have hC : (modelBand n (Qzf n) (Q₁ n)).re - e / 8 * (n : ℝ) ≤
      (medCoreBand n (Qzf n) (Q₁ n)).re :=
    complex_re_lower_of_norm_sub (hN4 n h4 hEven)
  have hlow' : -(e / 8 * (n : ℝ)) ≤ (lowSkirt n).re := hN5 n h5 hEven
  have hrem' : -(e / 8 * (n : ℝ)) ≤ (remSkirt n).re := hN6 n h6 hEven
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hen : (0 : ℝ) ≤ e * (n : ℝ) := mul_nonneg (le_of_lt he) hnn
  rw [hMed, hSk]
  simp only [Complex.add_re]
  linarith
