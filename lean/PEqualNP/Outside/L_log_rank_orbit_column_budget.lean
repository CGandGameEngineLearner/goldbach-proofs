import Mathlib

theorem PEqualNP.Outside.L_log_rank_orbit_column_budget :
    ∀ (n k C : ℕ) (seed : Fin C → Finset (Fin n)), let shift := fun (S : Finset (Fin n)) (t : Fin n) => S.image (fun i => i+t); let orbit := fun (S : Finset (Fin n)) => (Finset.univ : Finset (Fin n)).image (shift S); (∀ i, (seed i).card=k) → let Y := Finset.univ.biUnion (fun i => orbit (seed i)); Y.card ≤ C*n ∧ ∀ B ∈ Y, B.card=k := by
  intro n k C seed
  dsimp only
  intro hk
  have hinj : ∀ t : Fin n, Function.Injective (fun i : Fin n => i + t) := by
    intro t x y h
    have hv : (x.val + t.val) % n = (y.val + t.val) % n := by
      have := congrArg Fin.val h
      simpa [Fin.val_add] using this
    have hmod : x.val + t.val ≡ y.val + t.val [MOD n] := hv
    have hxy : x.val ≡ y.val [MOD n] := Nat.ModEq.add_right_cancel' t.val hmod
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hxy x.isLt y.isLt)
  constructor
  · calc ((Finset.univ : Finset (Fin C)).biUnion (fun i => (Finset.univ : Finset (Fin n)).image (fun t => (seed i).image (fun j => j + t)))).card
        ≤ ∑ i : Fin C, ((Finset.univ : Finset (Fin n)).image (fun t => (seed i).image (fun j => j + t))).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin C, n := by
          apply Finset.sum_le_sum
          intro i _
          calc ((Finset.univ : Finset (Fin n)).image (fun t => (seed i).image (fun j => j + t))).card
              ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
            _ = n := by simp
      _ = C * n := by
          rw [Finset.sum_const_nat (fun i _ => rfl)]
          simp
  · intro B hB
    rw [Finset.mem_biUnion] at hB
    obtain ⟨i, -, hi⟩ := hB
    rw [Finset.mem_image] at hi
    obtain ⟨t, -, rfl⟩ := hi
    rw [Finset.card_image_of_injective _ (hinj t), hk i]
