import Mathlib.Data.Finset.Card

/-! Reflection `k ↦ n - k` preserves the central window and is injective there.
Inclusion-exclusion then counts the overlap. To deduce a Goldbach representation,
one still needs an arithmetic lower bound for the relevant prime supports at `n`. -/

theorem PEqualNP.Outside.L_goldbach_central_support_overlap :
    let S := fun (n : ℕ) => (Finset.range (n+1)).filter (fun k => n<3*k ∧ 3*k<2*n);
    ∀ n (A B : Finset ℕ), A⊆S n → B⊆S n →
      A.card+B.card≤(S n).card+(A∩B.image (fun k => n-k)).card := by
  dsimp only
  intro n A B hA hB
  let W := (Finset.range (n+1)).filter (fun k => n<3*k ∧ 3*k<2*n)
  have hmem {k : ℕ} : k ∈ W ↔ k < n + 1 ∧ n < 3*k ∧ 3*k < 2*n := by
    simp only [W, Finset.mem_filter, Finset.mem_range]
  have hreflect : B.image (fun k => n - k) ⊆ W := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hk₁, hk₂, hk₃⟩ := hmem.mp (hB hk)
    exact hmem.mpr ⟨by omega, by omega, by omega⟩
  have hcard : (B.image (fun k => n - k)).card = B.card := by
    apply Finset.card_image_of_injOn
    intro i hi j hj heq
    have hi' := (hmem.mp (hB hi)).1
    have hj' := (hmem.mp (hB hj)).1
    change n - i = n - j at heq
    omega
  have hsub : A ∪ B.image (fun k => n-k) ⊆ W := Finset.union_subset hA hreflect
  have hu := Finset.card_le_card hsub
  have he := Finset.card_union_add_card_inter A (B.image (fun k => n-k))
  change A.card+B.card ≤ W.card+(A∩B.image (fun k => n-k)).card
  omega
