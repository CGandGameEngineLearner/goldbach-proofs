import Mathlib

open scoped BigOperators

theorem Conjectures.Goldbach.BeaumontDenseOpenHit :
    ∀ {X : Type} [TopologicalSpace X] (O U : Set X), Dense O → IsOpen U → U.Nonempty → (O ∩ U).Nonempty := by
  intro X _ O U hO hU hUne
  simpa [Set.inter_comm] using hO.inter_open_nonempty U hU hUne
