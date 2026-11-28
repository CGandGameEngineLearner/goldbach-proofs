import Mathlib

/-- Reduce cubic-residue Chen exceptions to the six admissible progressions modulo 42. -/

theorem Conjectures.Cuts.Cutb5112d9e7989398c8eb32c29
    (h₁ : let R : Finset ℕ := {4,10,16,22,28,40}
  ∀ n : ℕ, (n % 6=4 ∧ (∃ a b : ℕ, a<91 ∧ b<91 ∧ (a*(a+2)*b*(b+2)).Coprime 91 ∧ (a+b) % 91=n % 91 ∧ (∃ u : ℕ, u^3 % 7=a % 7) ∧ (∃ v : ℕ, v^3 % 13=b % 13))) ↔ n % 42 ∈ R)
    (h₂ : by
  classical
  exact ∀ (X Y : ℕ) (R : Finset ℕ) (P : ℕ → Bool), R ⊆ Finset.range 42 →
    ((Finset.Icc X Y).filter (fun n => n % 42 ∈ R ∧ P n)).card =
    ∑ r ∈ R, ((Finset.range (Y/42+1)).filter (fun k => X ≤ 42*k+r ∧ 42*k+r ≤ Y ∧ P (42*k+r))).card)
    (h₃ : by
  classical
  exact let ch := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length≤2
    let E := fun n : ℕ => ¬ (∃ p q : ℕ, ch p ∧ ch q ∧ p+q=n ∧ (∃ u : ℕ, u^3 % 7=p % 7) ∧ (∃ v : ℕ, v^3 % 13=q % 13))
    let R : Finset ℕ := {4,10,16,22,28,40}
    ∃ δ C : ℝ, 0<δ ∧ δ<1 ∧ 0<C ∧ ∃ T : ℕ, ∀ X : ℕ, T≤X → ∀ r ∈ R,
    ∀ W : Finset ℕ, (∀ k ∈ W, X≤42*k+r ∧ 42*k+r≤2*X ∧ E (42*k+r)) → (W.card:ℝ) ≤ C*(X:ℝ)^(1-δ))
    : (by
  classical
  exact let ch := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length≤2; ∃ δ C : ℝ, 0<δ ∧ δ<1 ∧ 0<C ∧ ∃ T : ℕ, ∀ X : ℕ, T≤X → (((Finset.Icc X (2*X)).filter (fun n : ℕ => n % 6=4 ∧ (∃ a b : ℕ, a<91 ∧ b<91 ∧ (a*(a+2)*b*(b+2)).Coprime 91 ∧ (a+b) % 91=n % 91 ∧ (∃ u : ℕ, u^3 % 7=a % 7) ∧ (∃ v : ℕ, v^3 % 13=b % 13)) ∧ ¬ (∃ p q : ℕ, ch p ∧ ch q ∧ p+q=n ∧ (∃ u : ℕ, u^3 % 7=p % 7) ∧ (∃ v : ℕ, v^3 % 13=q % 13)))).card:ℝ)≤C*(X:ℝ)^(1-δ)) := by
  classical
  intro ch
  obtain ⟨δ,C,hd,h1,hC,T,h3⟩ := h₃
  refine ⟨δ,6*C,hd,h1,by positivity,T,?_⟩
  intro X hX
  let R : Finset ℕ := {4,10,16,22,28,40}
  let E := fun n : ℕ => ¬ (∃ p q : ℕ, ch p ∧ ch q ∧ p+q=n ∧ (∃ u : ℕ, u^3 % 7=p % 7) ∧ (∃ v : ℕ, v^3 % 13=q % 13))
  let F := fun r : ℕ => ((Finset.range (2*X/42+1)).filter (fun k => X≤42*k+r ∧ 42*k+r≤2*X ∧ E (42*k+r))).card
  have rsub : R ⊆ Finset.range 42 := by decide
  have hr6 : R.card=6 := by decide
  have eqv (n : ℕ) :
      (n % 6=4 ∧ (∃ a b : ℕ, a<91 ∧ b<91 ∧ (a*(a+2)*b*(b+2)).Coprime 91 ∧ (a+b) % 91=n % 91 ∧ (∃ u : ℕ, u^3 % 7=a % 7) ∧ (∃ v : ℕ, v^3 % 13=b % 13)) ∧ E n)
        ↔ n % 42 ∈ R ∧ E n := by
    rw [← and_assoc,h₁ n]
  have heq := Finset.filter_congr (s:=Finset.Icc X (2*X)) (fun n _ => eqv n)
  have count := h₂ X (2*X) R (fun n => decide (E n)) rsub
  simp only [decide_eq_true_eq] at count
  have hreal : (((Finset.Icc X (2*X)).filter (fun n => n % 42 ∈ R ∧ E n)).card:ℝ) = ∑ r ∈ R, (F r:ℝ) := by
    rw [← Nat.cast_sum]
    exact congrArg (fun z : ℕ => (z:ℝ)) (by
      dsimp only [F]
      exact count)
  rw [heq,hreal]
  calc
    _ ≤ ∑ _r ∈ R, C*(X:ℝ)^(1-δ) := by
      apply Finset.sum_le_sum
      intro r hr
      apply h3 X hX r hr
      intro k hk
      exact (Finset.mem_filter.mp hk).2
    _ = 6*C*(X:ℝ)^(1-δ) := by rw [Finset.sum_const,hr6]; ring
