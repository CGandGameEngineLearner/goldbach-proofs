import Mathlib

/-- Recover unique Romanov representations via anchored prime-tuple moments. -/

theorem Conjectures.Cuts.Cut98c4f7bd8e42ae076e187460
    (h₁ : by
  classical
  exact ∀ (U : Finset ℕ) (r : ℕ → ℕ) (M : ℕ), (∀ n ∈ U, r n ≤ M) →
    (((U.filter (fun n => r n=1)).card):ℤ) = ∑ j ∈ Finset.range M, (-1:ℤ)^j * ((j+1:ℕ):ℤ) * ((∑ n ∈ U, (r n).choose (j+1) : ℕ):ℤ))
    (h₂ : by
  classical
  exact ∀ (U A : Finset ℕ) (G : ℕ → Finset ℕ) (j : ℕ), (∀ n ∈ U, G n ⊆ A) →
    (∑ n ∈ U, (G n).card.choose j) = ∑ s ∈ A.powersetCard j, (U.filter (fun n => s ⊆ G n)).card)
    (h₃ : by
  classical
  exact ∀ (U s : Finset ℕ) (N : ℕ), U ⊆ Finset.range N → s.Nonempty →
    let d := s.sup (fun e => 2^e)
    (U.filter (fun n => ∀ e ∈ s, Nat.Prime (n-2^e))).card =
      ((Finset.range N).filter (fun p => p+d ∈ U ∧ ∀ e ∈ s, Nat.Prime (p+(d-2^e)))).card)
    (h₄ : by
  classical
  exact ∃ c : ℝ, 0<c ∧ ∃ T : ℕ, ∀ X H : ℕ, T ≤ X → X ≤ H^2 → H ≤ X →
    let A := Finset.Icc 1 (Nat.log 2 (X+H))
    let U := (Finset.Ico X (X+H)).filter Odd
    let J := fun j : ℕ => ∑ s ∈ A.powersetCard j,
      let d := s.sup (fun e => 2^e)
      ((Finset.range (X+H)).filter (fun p => p+d ∈ U ∧ ∀ e ∈ s, Nat.Prime (p+(d-2^e)))).card
    c*(H:ℝ) ≤ ((∑ j ∈ Finset.range A.card, (-1:ℤ)^j * ((j+1:ℕ):ℤ) * (J (j+1):ℤ)):ℝ))
    : (by
  classical
  exact let R := fun n : ℕ => ((Finset.Icc 1 (Nat.log 2 n)).filter (fun e => Nat.Prime (n-2^e))).card; ∃ c : ℝ, 0 < c ∧ ∃ T : ℕ, ∀ X H : ℕ, T ≤ X → X ≤ H^2 → H ≤ X → c*(H:ℝ) ≤ (((Finset.Ico X (X+H)).filter (fun n => Odd n ∧ R n=1)).card:ℝ)) := by
  classical
  intro R
  obtain ⟨c,hc,T,h4⟩ := h₄
  refine ⟨c,hc,T,?_⟩
  intro X H hX hH hHX
  let A := Finset.Icc 1 (Nat.log 2 (X+H))
  let U := (Finset.Ico X (X+H)).filter Odd
  let G := fun n : ℕ => A.filter (fun e => Nat.Prime (n-2^e))
  let J := fun j : ℕ => ∑ s ∈ A.powersetCard j,
    let d := s.sup (fun e => 2^e)
    ((Finset.range (X+H)).filter (fun p => p+d ∈ U ∧ ∀ e ∈ s, Nat.Prime (p+(d-2^e)))).card
  have hU : U ⊆ Finset.range (X+H) := by
    intro n hn
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1).2
  have hG (n : ℕ) (_ : n ∈ U) : G n ⊆ A := Finset.filter_subset _ _
  have equalR (n : ℕ) (hn : n ∈ U) : (G n).card = R n := by
    apply congrArg Finset.card
    ext e
    simp only [G,A,Finset.mem_filter,Finset.mem_Icc]
    constructor
    · rintro ⟨⟨he,_⟩,hp⟩
      have hpos := hp.pos
      exact ⟨⟨he,Nat.le_log_of_pow_le (by decide) (show 2^e ≤ n by omega)⟩,hp⟩
    · rintro ⟨⟨he,hle⟩,hp⟩
      exact ⟨⟨he,hle.trans (Nat.log_mono_right (Nat.le_of_lt (Finset.mem_range.mp (hU hn))))⟩,hp⟩
  have out : U.filter (fun n => (G n).card=1) = (Finset.Ico X (X+H)).filter (fun n=>Odd n ∧ R n=1) := by
    ext n
    constructor
    · intro hn
      obtain ⟨hnU,hr⟩ := Finset.mem_filter.mp hn
      obtain ⟨hwin,hodd⟩ := Finset.mem_filter.mp hnU
      exact Finset.mem_filter.mpr ⟨hwin,hodd,(equalR n hnU).symm.trans hr⟩
    · intro hn
      obtain ⟨hwin,hodd,hr⟩ := Finset.mem_filter.mp hn
      have hnU : n ∈ U := Finset.mem_filter.mpr ⟨hwin,hodd⟩
      exact Finset.mem_filter.mpr ⟨hnU,(equalR n hnU).trans hr⟩
  have moments (j : ℕ) : (∑ n ∈ U, (G n).card.choose (j+1)) = J (j+1) := by
    rw [h₂ U A G (j+1) hG]
    apply Finset.sum_congr rfl
    intro s hs
    obtain ⟨sub,hcard⟩ := Finset.mem_powersetCard.mp hs
    have sne : s.Nonempty := Finset.card_pos.mp (by omega)
    have hit : U.filter (fun n => s ⊆ G n) = U.filter (fun n => ∀ e ∈ s, Nat.Prime (n-2^e)) := by
      ext n
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hn,hh⟩
        exact ⟨hn,fun e he => (Finset.mem_filter.mp (hh he)).2⟩
      · rintro ⟨hn,hh⟩
        exact ⟨hn,fun e he => Finset.mem_filter.mpr ⟨sub he,hh e he⟩⟩
    rw [hit]
    exact h₃ U s (X+H) hU sne
  have inv := h₁ U (fun n => (G n).card) A.card (fun n hn => Finset.card_le_card (hG n hn))
  change (((U.filter (fun n => (G n).card=1)).card):ℤ) = _ at inv
  rw [out] at inv
  simp_rw [moments] at inv
  apply le_trans (h4 X H hX hH hHX)
  exact le_of_eq (by exact_mod_cast inv.symm)
