import Mathlib

theorem Conjectures.Cuts.Taskb22b91080dec3f4177674fe2 : (by
  classical
  exact ∀ (U s : Finset ℕ) (N : ℕ), U ⊆ Finset.range N → s.Nonempty →
    let d := s.sup (fun e => 2^e)
    (U.filter (fun n => ∀ e ∈ s, Nat.Prime (n-2^e))).card =
      ((Finset.range N).filter (fun p => p+d ∈ U ∧ ∀ e ∈ s, Nat.Prime (p+(d-2^e)))).card) := by
  classical
  intro U s N hu hs d
  have hd : ∃ e ∈ s, 2^e = d := by
    obtain ⟨e,he,heq⟩ := Finset.exists_mem_eq_sup s hs (fun e => (2:ℕ)^e)
    exact ⟨e,he,heq.symm⟩
  let A := U.filter (fun n => ∀ e ∈ s, Nat.Prime (n-2^e))
  let B := (Finset.range N).filter (fun p => p+d ∈ U ∧ ∀ e ∈ s, Nat.Prime (p+(d-2^e)))
  have bound (n : ℕ) (hn : n ∈ A) : d ≤ n := by
    obtain ⟨e,he,heq⟩ := hd
    have hp := ((Finset.mem_filter.mp hn).2 e he).pos
    omega
  have hle (e : ℕ) (he : e ∈ s) : 2^e ≤ d := Finset.le_sup (f := fun e => 2^e) he
  have im : A.image (fun n => n-d) = B := by
    ext p
    constructor
    · intro hp
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hp
      have hnd := bound n hn
      obtain ⟨hnU,hh⟩ := Finset.mem_filter.mp hn
      have hnlt := Finset.mem_range.mp (hu hnU)
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by simpa [Nat.sub_add_cancel hnd] using hnU, ?_⟩
      intro e he
      have := hle e he
      simpa only [show n-d+(d-2^e)=n-2^e by omega] using hh e he
    · intro hp
      obtain ⟨_,hU,hp'⟩ := Finset.mem_filter.mp hp
      refine Finset.mem_image.mpr ⟨p+d,Finset.mem_filter.mpr ⟨hU,?_⟩,by omega⟩
      intro e he
      have := hle e he
      simpa only [show p+d-2^e = p+(d-2^e) by omega] using hp' e he
  have inj : Set.InjOn (fun n : ℕ => n-d) A := by
    intro x hx y hy h
    have := bound x hx
    have := bound y hy
    dsimp at h; omega
  exact (Finset.card_image_of_injOn inj).symm.trans (congrArg Finset.card im)
