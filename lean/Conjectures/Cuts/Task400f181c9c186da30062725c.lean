import Mathlib

theorem Conjectures.Cuts.Task400f181c9c186da30062725c : (have x1 : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun (x1 : ℕ → ℝ) (x2 x3 : ℕ) =>   have x4 : ℕ → ℕ → ℝ := fun (x4 x5 : ℕ) => ∑ x6 ∈ Finset.range x2 with x6 % x3 ^ (2 : ℕ) = x4 + x3 * x5, x1 x6;   ∑ x5 ∈ Finset.range x3, ∑ x6 ∈ Finset.range x3, (x4 x5 x6 - (∑ x7 ∈ Finset.range x3, x4 x5 x7) / ↑x3) ^ (2 : ℕ); have x2 : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun (x2 : ℕ → ℝ) (x3 x4 : ℕ) => ∑ x5 ∈ Finset.range x4, (∑ x6 ∈ Finset.range x3 with x6 % x4 = x5, x2 x6) ^ (2 : ℕ); ∀ (x3 : ℕ → ℝ) (x4 x5 : ℕ), (0 : ℕ) < x5 → x1 x3 x4 x5 = x2 x3 x4 (x5 ^ (2 : ℕ)) - x2 x3 x4 x5 / ↑x5) := by
  classical
  dsimp only
  intro w N p hp
  let mass (d r : ℕ) : ℝ := ∑ j ∈ Finset.range N with j % d = r, w j
  let lift (a b : ℕ) : ℝ := mass (p ^ 2) (a + p * b)
  change (∑ a ∈ Finset.range p, ∑ b ∈ Finset.range p,
    (lift a b - (∑ c ∈ Finset.range p, lift a c) / (p : ℝ)) ^ 2) =
    (∑ r ∈ Finset.range (p ^ 2), (mass (p ^ 2) r) ^ 2) -
      (∑ a ∈ Finset.range p, (mass p a) ^ 2) / (p : ℝ)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hdvd : p ∣ p ^ 2 := ⟨p, pow_two p⟩
  have hmod (j : ℕ) : j % p ^ 2 % p = j % p := Nat.mod_mod_of_dvd j hdvd
  have hres {a : ℕ} (ha : a < p) (b : ℕ) : (a + p * b) % p = a := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  have hquo {a : ℕ} (ha : a < p) (b : ℕ) : (a + p * b) / p = b := by
    rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt ha, zero_add]
  have hrow {a : ℕ} (ha : a < p) : (∑ b ∈ Finset.range p, lift a b) = mass p a := by
    unfold mass
    rw [← Finset.sum_fiberwise_of_maps_to
      (t := Finset.range p) (g := fun j => (j % p ^ 2) / p)
      (fun j _ => Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hp).mpr
        (by simpa only [pow_two] using Nat.mod_lt j (pow_pos hp 2)))) w]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    change (∑ j ∈ Finset.range N with j % p ^ 2 = a + p * b, w j) = _
    apply congrArg (fun s : Finset ℕ => ∑ j ∈ s, w j)
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hj, h⟩
      exact ⟨⟨hj, by rw [← hmod j, h, hres ha]⟩, by rw [h, hquo ha]⟩
    · rintro ⟨⟨hj, hra⟩, hrb⟩
      refine ⟨hj, ?_⟩
      calc
        j % p ^ 2 = (j % p ^ 2) % p + p * ((j % p ^ 2) / p) :=
          (Nat.mod_add_div _ _).symm
        _ = a + p * b := by rw [hmod j, hra, hrb]
  have hsquares :
      (∑ a ∈ Finset.range p, ∑ b ∈ Finset.range p, (lift a b) ^ 2) =
        ∑ r ∈ Finset.range (p ^ 2), (mass (p ^ 2) r) ^ 2 := by
    rw [← Finset.sum_product']
    refine Finset.sum_bij' (fun ab _ => ab.1 + p * ab.2) (fun r _ => (r % p, r / p))
      ?_ ?_ ?_ ?_ (fun _ _ => rfl)
    · intro ab hab
      rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
      apply Finset.mem_range.mpr
      calc
        ab.1 + p * ab.2 < p + p * ab.2 :=
          Nat.add_lt_add_right (Finset.mem_range.mp ha) _
        _ = p * (ab.2 + 1) := by ring
        _ ≤ p ^ 2 := by
          rw [pow_two]
          exact Nat.mul_le_mul_left p (Finset.mem_range.mp hb)
    · intro r hr
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt r hp),
        Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hp).mpr
          (by simpa only [pow_two] using Finset.mem_range.mp hr))⟩
    · intro ab hab
      have ha := Finset.mem_range.mp (Finset.mem_product.mp hab).1
      exact Prod.ext (hres ha _) (hquo ha _)
    · intro r _
      exact Nat.mod_add_div r p
  have hvariance {a : ℕ} (ha : a < p) :
      (∑ b ∈ Finset.range p, (lift a b - (∑ c ∈ Finset.range p, lift a c) / (p : ℝ)) ^ 2) =
        (∑ b ∈ Finset.range p, (lift a b) ^ 2) - (mass p a) ^ 2 / (p : ℝ) := by
    rw [hrow ha]
    let mean := mass p a / (p : ℝ)
    change (∑ b ∈ Finset.range p, (lift a b - mean) ^ 2) = _
    calc
      _ = ∑ b ∈ Finset.range p, ((lift a b) ^ 2 - (2 * mean) * lift a b + mean ^ 2) :=
        Finset.sum_congr rfl (fun _ _ => by ring)
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hrow ha,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        dsimp only [mean]
        field_simp [ne_of_gt hpR]
        ring
  calc
    _ = ∑ a ∈ Finset.range p, ((∑ b ∈ Finset.range p, (lift a b) ^ 2) -
        (mass p a) ^ 2 / (p : ℝ)) :=
      Finset.sum_congr rfl (fun _ ha => hvariance (Finset.mem_range.mp ha))
    _ = _ := by rw [Finset.sum_sub_distrib, hsquares, ← Finset.sum_div]
