import Mathlib

theorem Conjectures.Cuts.Taskb22b91080dec3f4177674fe2 : (∀ (x1 x2 : Finset ℕ) (x3 : ℕ),   x1 ⊆ Finset.range x3 →     x2.Nonempty →       have x6 : ℕ := x2.sup fun (x6 : ℕ) => (2 : ℕ) ^ x6;       {x7 ∈ x1 | ∀ x8 ∈ x2, Nat.Prime (x7 - (2 : ℕ) ^ x8)}.card = {x7 ∈ Finset.range x3 | x7 + x6 ∈ x1 ∧ ∀ x8 ∈ x2, Nat.Prime (x7 + (x6 - (2 : ℕ) ^ x8))}.card) := by
  classical
  intro A E X hA hE
  let M := E.sup (fun e => 2 ^ e : ℕ → ℕ)
  let S := A.filter (fun n => ∀ e ∈ E, Nat.Prime (n - 2 ^ e))
  have bound {n : ℕ} (hn : n ∈ S) : M ≤ n := by
    obtain ⟨e, he, hM⟩ := E.exists_mem_eq_sup hE (fun e => 2 ^ e : ℕ → ℕ)
    have h := ((Finset.mem_filter.mp hn).2 e he).pos
    change E.sup _ ≤ n
    omega
  change S.card = ((Finset.range X).filter (fun m => m + M ∈ A ∧
    ∀ e ∈ E, Nat.Prime (m + (M - 2^e)))).card
  refine Finset.card_bij (fun n _ => n - M) ?_ ?_ ?_
  · intro n hn
    have hMn := bound hn
    obtain ⟨ha, hp⟩ := Finset.mem_filter.mp hn
    have hnX := Finset.mem_range.mp (hA ha)
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_, ?_⟩
    · simpa [Nat.sub_add_cancel hMn] using ha
    · intro e he
      have hpow : 2 ^ e ≤ M := Finset.le_sup (f := fun i => 2^i) he
      rw [show n - M + (M - 2^e) = n - 2^e by omega]
      exact hp e he
  · intro n hn m hm eq
    have := bound hn
    have := bound hm
    omega
  · intro m hm
    obtain ⟨_, hA', hp⟩ := Finset.mem_filter.mp hm
    refine ⟨m + M, Finset.mem_filter.mpr ⟨hA', ?_⟩, by omega⟩
    intro e he
    have hpow : 2 ^ e ≤ M := Finset.le_sup (f := fun i => 2^i) he
    rw [show m + M - 2^e = m + (M - 2^e) by omega]
    exact hp e he
