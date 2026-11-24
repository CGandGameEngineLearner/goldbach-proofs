import Mathlib

namespace PEqualNP.Outside

theorem L_goldbach_ap_rational_phase :
    let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
    let ap := fun (q a N : ℕ) (f : ℕ → ℝ) =>
      Finset.sum ((Finset.range (N + 1)).filter (fun k => k % q = a)) f
    let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) =>
      Finset.sum (Finset.range (n + 1)) (fun k => (w k : ℂ) * E ((k : ℝ) * t))
    ∀ (N q h : ℕ) (f : ℕ → ℝ), 0 < q →
      S N f ((h : ℝ) / (q : ℝ)) =
        Finset.sum (Finset.range q) (fun a =>
          (ap q a N f : ℂ) * E ((h : ℝ) * (a : ℝ) / (q : ℝ))) := by
  dsimp only
  intro N q h f hq
  let E : ℝ → ℂ := fun x => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
  let t : ℝ := (h : ℝ) / (q : ℝ)
  have hE_nat (m : ℕ) : E (m : ℝ) = 1 := by
    dsimp [E]
    have harg : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) =
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [harg, Complex.exp_nat_mul]
    simp [Complex.exp_two_pi_mul_I]
  have hE_add_nat (x : ℝ) (m : ℕ) : E (x + (m : ℝ)) = E x := by
    dsimp [E]
    have harg : (((2 * Real.pi * (x + (m : ℝ)) : ℝ) : ℂ) * Complex.I) =
        ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I +
          ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [harg, Complex.exp_add]
    change E x * E (m : ℝ) = E x
    rw [hE_nat, mul_one]
  have hphase {k a : ℕ} (hka : k % q = a) :
      E ((k : ℝ) * t) = E ((h : ℝ) * (a : ℝ) / (q : ℝ)) := by
    have hkdecomp : k = q * (k / q) + a := by
      rw [← hka]
      exact (Nat.div_add_mod k q).symm
    have hk_real : (k : ℝ) = (q : ℝ) * ((k / q : ℕ) : ℝ) + (a : ℝ) := by
      exact_mod_cast hkdecomp
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
    calc
      E ((k : ℝ) * t) = E ((a : ℝ) * t + ((k / q * h : ℕ) : ℝ)) := by
        congr 1
        dsimp [t]
        rw [hk_real]
        push_cast
        field_simp [hqR]
        ring_nf
      _ = E ((a : ℝ) * t) := by
        rw [hE_add_nat]
      _ = E ((h : ℝ) * (a : ℝ) / (q : ℝ)) := by
        congr 1
        dsimp [t]
        ring
  change
    Finset.sum (Finset.range (N + 1)) (fun k => (f k : ℂ) * E ((k : ℝ) * t)) =
      Finset.sum (Finset.range q) (fun a =>
        ((Finset.sum ((Finset.range (N + 1)).filter (fun k => k % q = a)) f : ℝ) : ℂ) *
          E ((h : ℝ) * (a : ℝ) / (q : ℝ)))
  calc
    Finset.sum (Finset.range (N + 1)) (fun k => (f k : ℂ) * E ((k : ℝ) * t))
        = Finset.sum ((Finset.range (N + 1)).filter (fun k => k % q ∈ Finset.range q))
            (fun k => (f k : ℂ) * E ((k : ℝ) * t)) := by
          simp [Nat.mod_lt, hq]
    _ = Finset.sum (Finset.range q) (fun a =>
          Finset.sum ((Finset.range (N + 1)).filter (fun k => k % q = a))
            (fun k => (f k : ℂ) * E ((k : ℝ) * t))) := by
          rw [← Finset.sum_fiberwise_eq_sum_filter]
    _ = Finset.sum (Finset.range q) (fun a =>
        ((Finset.sum ((Finset.range (N + 1)).filter (fun k => k % q = a)) f : ℝ) : ℂ) *
          E ((h : ℝ) * (a : ℝ) / (q : ℝ))) := by
          apply Finset.sum_congr rfl
          intro a ha
          have ha_lt : a < q := Finset.mem_range.mp ha
          calc
            Finset.sum ((Finset.range (N + 1)).filter (fun k => k % q = a))
                (fun k => (f k : ℂ) * E ((k : ℝ) * t))
              = Finset.sum ((Finset.range (N + 1)).filter (fun k => k % q = a))
                  (fun k => (f k : ℂ) * E ((h : ℝ) * (a : ℝ) / (q : ℝ))) := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  rw [hphase (Finset.mem_filter.mp hk).2]
            _ = (Finset.sum ((Finset.range (N + 1)).filter (fun k => k % q = a))
                  (fun k => (f k : ℂ))) * E ((h : ℝ) * (a : ℝ) / (q : ℝ)) := by
                  rw [Finset.sum_mul]
            _ = ((Finset.sum ((Finset.range (N + 1)).filter (fun k => k % q = a)) f : ℝ) : ℂ) *
                  E ((h : ℝ) * (a : ℝ) / (q : ℝ)) := by
                  simp

end PEqualNP.Outside
