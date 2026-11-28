import Mathlib

/-- Estimate the support of separated Romanov representations using mixed collision energy. -/

theorem Conjectures.Cuts.Cut94fdb6d9ac4ec7ab2e59e3ea
    (h₁ : by
  classical
  exact ∀ (U : Finset ℕ) (a b : ℕ → ℕ),
    (∑ n ∈ U, a n*b n)^2 ≤ (U.filter (fun n => 0<a n ∧ 0<b n)).card * ∑ n ∈ U, (a n*b n)^2)
    (h₂ : by
  classical
  exact ∀ (U A B : Finset ℕ) (G F : ℕ → Finset ℕ) (i j : ℕ),
    (∀ n ∈ U, G n ⊆ A ∧ F n ⊆ B) →
    (∑ n ∈ U, (G n).card.choose i*(F n).card.choose j) =
      ∑ s ∈ A.powersetCard i, ∑ t ∈ B.powersetCard j, (U.filter (fun n => s ⊆ G n ∧ t ⊆ F n)).card)
    (h₃ : by
  classical
  exact ∀ (U : Finset ℕ) (a b : ℕ → ℕ),
    let K := fun i j : ℕ => ∑ n ∈ U, (a n).choose i*(b n).choose j
    (∑ n ∈ U, (a n*b n)^2) = K 1 1+2*K 2 1+2*K 1 2+4*K 2 2)
    (h₄ : by
  classical
  exact ∃ c D : ℝ, 0<c ∧ 0<D ∧ ∃ T : ℕ, ∀ X ≥ T,
    let L := Nat.log 2 X / 2
    let A := Finset.Icc 1 (L/2)
    let B := Finset.Icc (L/2+1) L
    let U := (Finset.Ico X (2*X)).filter Odd
    let K := fun i j : ℕ => ∑ s ∈ A.powersetCard i, ∑ t ∈ B.powersetCard j,
      (U.filter (fun n => ∀ e ∈ s ∪ t, Nat.Prime (n-2^e))).card
    c*(X:ℝ) ≤ (K 1 1:ℝ) ∧ ((K 1 1+2*K 2 1+2*K 1 2+4*K 2 2:ℕ):ℝ) ≤ D*(X:ℝ))
    : (by
  classical
  exact let J := fun a b m : ℕ => ((Finset.Icc a b).filter (fun e => Nat.Prime (m-2^e))).card; ∃ c : ℝ, 0 < c ∧ ∃ T : ℕ, ∀ X ≥ T, let L := Nat.log 2 X / 2; c*(X:ℝ) ≤ (((Finset.Ico X (2*X)).filter (fun m => Odd m ∧ 0<J 1 (L/2) m ∧ 0<J (L/2+1) L m)).card:ℝ)) := by
  classical
  intro J
  obtain ⟨c,D,hc,hD,T,h4⟩ := h₄
  refine ⟨c^2/D,by positivity,max T 1,?_⟩
  intro X hX L
  let A := Finset.Icc 1 (L/2)
  let B := Finset.Icc (L/2+1) L
  let U := (Finset.Ico X (2*X)).filter Odd
  let G := fun n : ℕ => A.filter (fun e => Nat.Prime (n-2^e))
  let F := fun n : ℕ => B.filter (fun e => Nat.Prime (n-2^e))
  let a := fun n => (G n).card
  let b := fun n => (F n).card
  let K := fun i j : ℕ => ∑ s ∈ A.powersetCard i, ∑ t ∈ B.powersetCard j,
    (U.filter (fun n => ∀ e ∈ s ∪ t, Nat.Prime (n-2^e))).card
  let V := U.filter (fun n => 0<a n ∧ 0<b n)
  have hsub (n : ℕ) (_ : n ∈ U) : G n ⊆ A ∧ F n ⊆ B :=
    ⟨Finset.filter_subset _ _,Finset.filter_subset _ _⟩
  have mix (i j : ℕ) : (∑ n ∈ U, (a n).choose i*(b n).choose j) = K i j := by
    change (∑ n ∈ U, (G n).card.choose i*(F n).card.choose j) = _
    rw [h₂ U A B G F i j hsub]
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro t ht
    apply congrArg Finset.card
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hn,hsn,htn⟩
      refine ⟨hn,?_⟩
      intro e he
      rcases Finset.mem_union.mp he with h|h
      · exact (Finset.mem_filter.mp (hsn h)).2
      · exact (Finset.mem_filter.mp (htn h)).2
    · rintro ⟨hn,h⟩
      refine ⟨hn,?_,?_⟩
      · intro e he
        exact Finset.mem_filter.mpr ⟨(Finset.mem_powersetCard.mp hs).1 he,h e (Finset.mem_union_left _ he)⟩
      · intro e he
        exact Finset.mem_filter.mpr ⟨(Finset.mem_powersetCard.mp ht).1 he,h e (Finset.mem_union_right _ he)⟩
  have first := mix 1 1
  simp only [Nat.choose_one_right] at first
  have second := h₃ U a b
  dsimp only at second
  simp_rw [mix] at second
  have cs := h₁ U a b
  rw [first,second] at cs
  have csR : (K 1 1:ℝ)^2 ≤ (V.card:ℝ)*((K 1 1+2*K 2 1+2*K 1 2+4*K 2 2:ℕ):ℝ) := by exact_mod_cast cs
  obtain ⟨low,upper⟩ := h4 X (le_trans (le_max_left _ _) hX)
  change c*(X:ℝ) ≤ (K 1 1:ℝ) at low
  change ((K 1 1+2*K 2 1+2*K 1 2+4*K 2 2:ℕ):ℝ) ≤ D*(X:ℝ) at upper
  have hx : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
  have bounds : (c*(X:ℝ))^2 ≤ (V.card:ℝ)*(D*(X:ℝ)) :=
    (pow_le_pow_left₀ (by positivity) low 2).trans (csR.trans (mul_le_mul_of_nonneg_left upper (by positivity)))
  have cancel : c^2*(X:ℝ) ≤ (V.card:ℝ)*D := by
    apply le_of_mul_le_mul_right (a := (X:ℝ)) _ hx
    nlinarith only [bounds]
  have out : V = (Finset.Ico X (2*X)).filter (fun n => Odd n ∧ 0<J 1 (L/2) n ∧ 0<J (L/2+1) L n) := by
    ext n
    simp only [V,U,Finset.mem_filter,a,b,G,F,A,B,J,and_assoc]
  rw [← out]
  calc
    c^2/D*(X:ℝ) = (c^2*(X:ℝ))/D := by ring
    _ ≤ (V.card:ℝ) := (div_le_iff₀ hD).mpr cancel
