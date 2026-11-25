import Mathlib

/-!
# L-goldbach-reflect-unit-mass

The diagonal correction to the unit-restricted prime mass: in the reflected
window `k ↦ n - k` with `n` even and at least `4`, a prime-prime pair whose
first entry fails to be coprime to `n` must have `k = n / 2` (a prime divisor
of `n` dividing the prime `n - k` equals it). So the coprime filter drops
exactly the central diagonal term.
-/

theorem PEqualNP.Outside.L_goldbach_reflect_unit_mass :
    let w := fun k : ℕ => if k.Prime then Real.log (k : ℝ) else 0; ∀ n : ℕ, 4 ≤ n → Even n → (∑ k ∈ Finset.range (n+1), w k*w (n-k)) = (∑ k ∈ (Finset.range (n+1)).filter (fun k => Nat.Coprime k n), w k*w (n-k)) + (w (n/2))^2 := by
  intro w n hn he
  have hm2 : 2 * (n/2) = n := by
    obtain ⟨m, hm⟩ := he
    omega
  have hcomp : ∑ k ∈ (Finset.range (n+1)).filter (fun k => ¬ Nat.Coprime k n), w k*w (n-k) = (w (n/2))^2 := by
    have hterm : ∀ k ∈ (Finset.range (n+1)).filter (fun k => ¬ Nat.Coprime k n), w k*w (n-k) = if k = n/2 then (w (n/2))^2 else 0 := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨hk1, hk2⟩ := hk
      by_cases hkh : k = n/2
      · rw [if_pos hkh]
        have hhalf : n - k = k := by omega
        rw [hhalf, ← hkh]
        ring
      · rw [if_neg hkh]
        by_cases hp1 : k.Prime
        · by_cases hp2 : (n-k).Prime
          · exfalso
            obtain ⟨p, hp, hpb, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hk2
            have hpek : p = k := by
              rcases (Nat.dvd_prime hp1).mp hpb with h1 | h1
              · exact absurd h1 hp.ne_one
              · exact h1
            have hkn : k ∣ n := by rw [← hpek]; exact hpn
            have hsub : k ∣ (n - k) := by
              obtain ⟨m, hm⟩ := hkn
              refine ⟨m - 1, ?_⟩
              rw [hm, Nat.mul_sub, mul_one]
            rcases (Nat.dvd_prime hp2).mp hsub with h1 | h2
            · exact absurd h1 hp1.ne_one
            · exact hkh (by omega)
          · simp [w, hp2]
        · simp [w, hp1]
    have hmem : n/2 ∈ (Finset.range (n+1)).filter (fun k => ¬ Nat.Coprime k n) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      by_contra hcop
      have hd : n/2 ∣ n := ⟨2, by omega⟩
      have h1 : n/2 = 1 := Nat.Coprime.eq_one_of_dvd hcop hd
      omega
    rw [Finset.sum_congr rfl hterm]
    simp only [Finset.sum_ite_eq' ]
    rw [if_pos hmem]
  have hsplit : (∑ k ∈ (Finset.range (n+1)).filter (fun k => Nat.Coprime k n), w k*w (n-k)) + (∑ k ∈ (Finset.range (n+1)).filter (fun k => ¬ Nat.Coprime k n), w k*w (n-k)) = ∑ k ∈ Finset.range (n+1), w k*w (n-k) :=
    Finset.sum_filter_add_sum_filter_not (Finset.range (n+1)) (fun k => Nat.Coprime k n) (fun k => w k*w (n-k))
  rw [← hsplit, hcomp]
