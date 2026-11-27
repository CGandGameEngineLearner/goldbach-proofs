import Mathlib

theorem Conjectures.Goldbach.BeaumontDenseOpenHit :
    ∀ {X : Type} [TopologicalSpace X] (O U : Set X), Dense O → IsOpen U → U.Nonempty → (O ∩ U).Nonempty := by
  intro X _inst O U hO hU hne
  obtain ⟨x, hxU, hxO⟩ := hO.inter_open_nonempty U hU hne
  exact ⟨x, hxO, hxU⟩
