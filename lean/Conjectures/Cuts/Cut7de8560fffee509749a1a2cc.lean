import Mathlib

/-- Convert the moving fourth-power gap into a center coefficient of truncated prime polynomials. -/

theorem Conjectures.Cuts.Cut7de8560fffee509749a1a2cc
    (h₁ : ∀ m : ℕ, (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=2*m ∧ (Nat.dist p q)^4 ≤ (2*m)^3) ↔
    ∃ r : ℕ, r ≤ m ∧ 2*r^4 ≤ m^3 ∧ Nat.Prime (m-r) ∧ Nat.Prime (m+r))
    (h₂ : ∀ m : ℕ, (Finset.range (m+1)).filter (fun r => 2*r^4 ≤ m^3) =
    Finset.range (min m (Nat.sqrt (Nat.sqrt (m^3/2)))+1))
    (h₃ : by
  classical
  exact ∀ m R : ℕ, R ≤ m →
    let L := (Finset.Icc (m-R) m).filter Nat.Prime
    let H := (Finset.Icc m (m+R)).filter Nat.Prime
    ((∑ p ∈ L, Polynomial.monomial p (1:ℕ))*(∑ q ∈ H, Polynomial.monomial q (1:ℕ))).coeff (2*m) = ((Finset.range (R+1)).filter (fun r => Nat.Prime (m-r) ∧ Nat.Prime (m+r))).card)
    (h₄ : by
  classical
  exact let hits := fun m : ℕ =>
      let R := min m (Nat.sqrt (Nat.sqrt (m^3/2)))
      let L := (Finset.Icc (m-R) m).filter Nat.Prime
      let H := (Finset.Icc m (m+R)).filter Nat.Prime
      ((∑ p ∈ L, Polynomial.monomial p (1:ℕ))*(∑ q ∈ H, Polynomial.monomial q (1:ℕ))).coeff (2*m)
    ∀ ε : ℝ, 0<ε → ∀ A : ℕ, ∃ C : ℝ, 0<C ∧ ∃ T : ℕ, ∀ X H : ℕ, T ≤ X → H ≤ X →
      (X:ℝ)^((7:ℝ)/120+ε) ≤ (H:ℝ) →
      (((Finset.Icc (X-H) X).filter (fun n => Even n ∧ hits (n/2)=0)).card:ℝ) ≤ C*(H:ℝ)/(1+Real.log (X:ℝ))^A)
    : (by
  classical
  exact ∀ ε : ℝ, 0<ε → ∀ A : ℕ, ∃ C : ℝ, 0<C ∧ ∃ T : ℕ, ∀ X H : ℕ, T≤X → H≤X → (X:ℝ)^((7:ℝ)/120+ε) ≤ (H:ℝ) → (((Finset.Icc (X-H) X).filter (fun n : ℕ => Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n ∧ (Nat.dist p q)^4≤n^3)).card:ℝ) ≤ C*(H:ℝ)/(1+Real.log (X:ℝ))^A) := by
  classical
  intro ε hε A
  obtain ⟨C,hC,T,ha⟩ := h₄ ε hε A
  refine ⟨C,hC,T,?_⟩
  intro X H hT hH he
  let hits := fun m : ℕ =>
    let R := min m (Nat.sqrt (Nat.sqrt (m^3/2)))
    let L := (Finset.Icc (m-R) m).filter Nat.Prime
    let H := (Finset.Icc m (m+R)).filter Nat.Prime
    ((∑ p ∈ L, Polynomial.monomial p (1:ℕ))*(∑ q ∈ H, Polynomial.monomial q (1:ℕ))).coeff (2*m)
  have good (m : ℕ) :
      (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=2*m ∧ (Nat.dist p q)^4 ≤ (2*m)^3) ↔ 0<hits m := by
    let R := min m (Nat.sqrt (Nat.sqrt (m^3/2)))
    let G := (Finset.range (R+1)).filter (fun r => Nat.Prime (m-r) ∧ Nat.Prime (m+r))
    have co : hits m=G.card := h₃ m R (min_le_left _ _)
    rw [co,h₁,Finset.card_pos]
    constructor
    · rintro ⟨r,hr,hpow,hp,hq⟩
      have hb : r ∈ (Finset.range (m+1)).filter (fun r=>2*r^4 ≤ m^3) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hpow⟩
      rw [h₂] at hb
      exact ⟨r,Finset.mem_filter.mpr ⟨hb,hp,hq⟩⟩
    · rintro ⟨r,hr⟩
      obtain ⟨hb,hp,hq⟩ := Finset.mem_filter.mp hr
      change r ∈ Finset.range (min m (Nat.sqrt (Nat.sqrt (m^3/2)))+1) at hb
      rw [← h₂] at hb
      obtain ⟨hlo,hpow⟩ := Finset.mem_filter.mp hb
      exact ⟨r,by have := Finset.mem_range.mp hlo;omega,hpow,hp,hq⟩
  have eqv (n : ℕ) :
      (Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n ∧ (Nat.dist p q)^4 ≤ n^3) ↔
      Even n ∧ hits (n/2)=0 := by
    apply and_congr_right
    rintro ⟨m,rfl⟩
    rw [show m+m=2*m by omega,good]
    simp
  rw [Finset.filter_congr (s:=Finset.Icc (X-H) X) (fun n _=>eqv n)]
  exact ha X H hT hH he
