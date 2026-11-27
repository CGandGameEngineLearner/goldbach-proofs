import Mathlib

theorem Conjectures.Goldbach.BeaumontDenseOpenHit :
  ∀ {X : Type} [TopologicalSpace X] (O U : Set X), Dense O → IsOpen U → U.Nonempty → (O ∩ U).Nonempty := by
  intro X _ O U hO hU hn
  simpa [Set.inter_comm] using (dense_iff_inter_open.mp hO U hU hn)
