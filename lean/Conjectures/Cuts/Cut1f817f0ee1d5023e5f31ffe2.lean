import Mathlib

/-- Encode the two-factor Chen windows with a polynomial indexed by canonical prime factors. -/

theorem Conjectures.Cuts.Cut1f817f0ee1d5023e5f31ffe2
    (h₁ : ∀ p : ℕ, (∃ a b : ℕ, Nat.Prime a ∧ Nat.Prime b ∧ a*b=p+2 ∧ a^5≤p+2 ∧ p+2≤a^6) ↔
    (let a := (p+2).minFac
      let b := (p+2)/a
      Nat.Prime b ∧ a^4≤b ∧ b≤a^5))
    (h₂ : by
  classical
  exact ∀ (N : ℕ) (w : ℕ → Polynomial ℕ),
    let S := (Finset.range (N+1)).filter (fun p : ℕ => Nat.Prime p ∧ (let a := (p+2).minFac
      let b := (p+2)/a
      Nat.Prime b ∧ a^4≤b ∧ b≤a^5))
    let F := ((Finset.range (N+3)).product (Finset.range (N+3))).filter (fun z : ℕ × ℕ =>
      Nat.Prime z.1 ∧ Nat.Prime z.2 ∧ z.1^4≤z.2 ∧ z.2≤z.1^5 ∧ z.1*z.2≤N+2 ∧ Nat.Prime (z.1*z.2-2))
    ∑ p ∈ S, w (p+2) = ∑ z ∈ F, w (z.1*z.2))
    (h₃ : by
  classical
  exact ∀ (S : Finset ℕ) (n : ℕ),
    0 < ((∑ p ∈ S, Polynomial.monomial (p+2) (1:ℕ))^2).coeff (n+4) ↔ ∃ p ∈ S, ∃ q ∈ S, p+q=n)
    (h₄ : by
  classical
  exact let F := fun N : ℕ => ((Finset.range (N+3)).product (Finset.range (N+3))).filter (fun z : ℕ × ℕ =>
      Nat.Prime z.1 ∧ Nat.Prime z.2 ∧ z.1^4≤z.2 ∧ z.2≤z.1^5 ∧ z.1*z.2≤N+2 ∧ Nat.Prime (z.1*z.2-2))
    let P := fun N : ℕ => ∑ z ∈ F N, Polynomial.monomial (z.1*z.2) (1:ℕ)
    ∃ δ : ℝ, 0<δ ∧ δ<1 ∧ ∃ T : ℕ, ∀ X ≥ T,
      (((Finset.Icc X (2*X)).filter (fun n => n % 6=4 ∧ ((P (2*X))^2).coeff (n+4)=0)).card:ℝ) ≤ (X:ℝ)^(1-δ))
    : (by
  classical
  let chen := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length ≤ 2
  let split := fun p : ℕ => ∃ a b : ℕ, Nat.Prime a ∧ Nat.Prime b ∧ a*b=p+2 ∧ a^5 ≤ p+2 ∧ p+2 ≤ a^6
  exact ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ T : ℕ, ∀ X : ℕ, T ≤ X → (((Finset.Icc X (2*X)).filter (fun n => n % 6=4 ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n ∧ split p ∧ split q)).card:ℝ) ≤ (X:ℝ)^(1-δ)) := by
  classical
  intro _chen split
  obtain ⟨δ,hd,h1,T,h4⟩ := h₄
  refine ⟨δ,hd,h1,T,?_⟩
  intro X hX
  let N := 2*X
  let S := (Finset.range (N+1)).filter (fun p : ℕ => Nat.Prime p ∧ (let a := (p+2).minFac
      let b := (p+2)/a
      Nat.Prime b ∧ a^4≤b ∧ b≤a^5))
  let F := ((Finset.range (N+3)).product (Finset.range (N+3))).filter (fun z : ℕ × ℕ =>
      Nat.Prime z.1 ∧ Nat.Prime z.2 ∧ z.1^4≤z.2 ∧ z.2≤z.1^5 ∧ z.1*z.2≤N+2 ∧ Nat.Prime (z.1*z.2-2))
  let w := fun d : ℕ => Polynomial.monomial d (1:ℕ)
  let P := ∑ z ∈ F, w (z.1*z.2)
  have hp : (∑ p ∈ S, w (p+2)) = P := h₂ N w
  have hs (p : ℕ) : p ∈ S ↔ p≤N ∧ p.Prime ∧ split p := by
    simp only [S,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff,split,h₁ p]
  have co (n : ℕ) (hn : n≤N) :
      (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n ∧ split p ∧ split q) ↔ 0<(P^2).coeff (n+4) := by
    rw [← hp]
    change _ ↔ 0 < ((∑ p ∈ S, Polynomial.monomial (p+2) (1:ℕ))^2).coeff (n+4)
    rw [h₃]
    constructor
    · rintro ⟨p,q,pp,qp,hpq,ps,qs⟩
      exact ⟨p,(hs p).mpr ⟨by omega,pp,ps⟩,q,(hs q).mpr ⟨by omega,qp,qs⟩,hpq⟩
    · rintro ⟨p,hp,q,hq,he⟩
      obtain ⟨_,pp,ps⟩ := (hs p).mp hp
      obtain ⟨_,qp,qs⟩ := (hs q).mp hq
      exact ⟨p,q,pp,qp,he,ps,qs⟩
  have eqv (n : ℕ) (hn : n ∈ Finset.Icc X (2*X)) :
      (n % 6=4 ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n ∧ split p ∧ split q)
      ↔ n % 6=4 ∧ (P^2).coeff (n+4)=0 := by
    rw [co n (Finset.mem_Icc.mp hn).2]
    omega
  rw [Finset.filter_congr eqv]
  exact h4 X hX
