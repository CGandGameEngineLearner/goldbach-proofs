import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

open NumberField

/-- A choice, for each infinite place w of E, of a complex embedding Φ w of E that induces w. -/
class PlaceEmbedding (E : Type*) [Field E] where
  Φ : _ → E →+* ℂ
  mk_Φ w : InfinitePlace.mk (Φ w) = w

export PlaceEmbedding (Φ mk_Φ)

attribute [simp] mk_Φ

noncomputable instance (priority := low) (E : Type*) [Field E] : PlaceEmbedding E :=
  ⟨_, InfinitePlace.mk_embedding⟩

