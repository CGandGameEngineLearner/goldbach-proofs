import Mathlib

/-- Separate the exceptional shared prime 3 and convert the remaining Chen pairs to adjacent indices. -/

theorem Conjectures.Cuts.Cute7d439a4d0a2fd4c0546d7ab
    (h₁ : let ch := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length ≤ 2
  ∀ t : ℕ, 1 ≤ t → ((∃ p q : ℕ, ch p ∧ ch q ∧ p+q=6*t+4 ∧ ch (q+6)) ↔
    (ch (6*t+1) ∧ ch (6*t+7)) ∨ ∃ a b : ℕ, a+b+1=t ∧ ch (6*a+5) ∧ ch (6*b+5) ∧ ch (6*b+11)))
    (h₂ : let ch := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length ≤ 2
  ∀ t : ℕ, 1 ≤ t → ((ch (6*t+1) ∧ ch (6*t+7)) ↔ Nat.Prime (6*t+1) ∧ Nat.Prime (6*t+7) ∧ Nat.Prime (2*t+1) ∧ Nat.Prime (2*t+3)))
    (h₃ : by
  classical
  exact let ch := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length ≤ 2
    let G := fun t : ℕ => (Finset.range t).filter (fun a => ch (6*a+5) ∧ ch (6*(t-1-a)+5) ∧ ch (6*(t-1-a)+11))
    let special := fun t : ℕ => Nat.Prime (6*t+1) ∧ Nat.Prime (6*t+7) ∧ Nat.Prime (2*t+1) ∧ Nat.Prime (2*t+3)
    ∃ δ C : ℝ, 0<δ ∧ δ<1 ∧ 0<C ∧ ∃ T : ℕ, ∀ X ≥ T,
      (((Finset.Icc X (2*X)).filter (fun n => n % 6=4 ∧ G (n/6)=∅ ∧ ¬ special (n/6))).card:ℝ) ≤ C*(X:ℝ)^(1-δ))
    : (by
  classical
  exact let ch := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length≤2; ∃ δ C : ℝ, 0<δ ∧ δ<1 ∧ 0<C ∧ ∃ T : ℕ, ∀ X : ℕ, T≤X → (((Finset.Icc X (2*X)).filter (fun n : ℕ => n % 6=4 ∧ ¬ (∃ p q : ℕ, ch p ∧ ch q ∧ p+q=n ∧ ch (q+6)))).card:ℝ)≤C*(X:ℝ)^(1-δ)) := by
  classical
  intro ch
  obtain ⟨δ,C,hδ,h1,hC,T,h3⟩ := h₃
  refine ⟨δ,C,hδ,h1,hC,max T 10,?_⟩
  intro X hX
  let G := fun t : ℕ => (Finset.range t).filter (fun a => ch (6*a+5) ∧ ch (6*(t-1-a)+5) ∧ ch (6*(t-1-a)+11))
  let special := fun t : ℕ => Nat.Prime (6*t+1) ∧ Nat.Prime (6*t+7) ∧ Nat.Prime (2*t+1) ∧ Nat.Prime (2*t+3)
  have index (t : ℕ) :
      (∃ a b : ℕ, a+b+1=t ∧ ch (6*a+5) ∧ ch (6*b+5) ∧ ch (6*b+11)) ↔ (G t).Nonempty := by
    constructor
    · rintro ⟨a,b,he,hp,hq,hr⟩
      have e : t-1-a=b := by omega
      exact ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp,e.symm ▸ hq,e.symm ▸ hr⟩⟩
    · rintro ⟨a,ha⟩
      obtain ⟨hl,hp,hq,hr⟩ := Finset.mem_filter.mp ha
      have := Finset.mem_range.mp hl
      exact ⟨a,t-1-a,by omega,hp,hq,hr⟩
  have e (n : ℕ) (hn : n ∈ Finset.Icc X (2*X)) :
      (n % 6=4 ∧ ¬ (∃ p q : ℕ, ch p ∧ ch q ∧ p+q=n ∧ ch (q+6))) ↔
      n % 6=4 ∧ G (n/6)=∅ ∧ ¬ special (n/6) := by
    apply and_congr_right
    intro hmod
    have hx0 := (Finset.mem_Icc.mp hn).1
    have ht : 1 ≤ n/6 := by omega
    have repr := h₁ (n/6) ht
    change (∃ p q : ℕ, ch p ∧ ch q ∧ p+q=6*(n/6)+4 ∧ ch (q+6)) ↔ _ at repr
    rw [show 6*(n/6)+4=n by omega,h₂ (n/6) ht,index] at repr
    rw [repr,not_or]
    change (¬ special (n/6)) ∧ ¬(G (n/6)).Nonempty ↔ _
    rw [Finset.not_nonempty_iff_eq_empty,and_comm]
  rw [Finset.filter_congr e]
  exact h3 X (le_trans (le_max_left _ _) hX)
