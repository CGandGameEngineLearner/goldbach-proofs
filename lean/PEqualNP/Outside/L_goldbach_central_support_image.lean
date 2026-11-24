import Mathlib

theorem PEqualNP.Outside.L_goldbach_central_support_image :
    let S := fun (n : ℕ) => (Finset.range (n+1)).filter (fun k => n<3*k ∧ 3*k<2*n)
    ∀ n (A:Finset ℕ), A⊆S n → (A.image (fun k => n-k)).card=A.card := by
  dsimp only
  intro n A hA
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  have ha' := Finset.mem_range.mp (Finset.mem_filter.mp (hA ha)).1
  have hb' := Finset.mem_range.mp (Finset.mem_filter.mp (hA hb)).1
  change n - a = n - b at hab
  omega
