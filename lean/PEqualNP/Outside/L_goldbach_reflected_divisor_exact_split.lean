import Mathlib

/-!
# Exact reflected-divisor split for designated even targets (D01)

This file formalizes `L-goldbach-reflected-divisor-exact-split` under the
`representations` track feeding `L-goldbach-dyadic-correlation-floor`.

Expanding `Λ(N - p) = -∑_{d ∣ N - p} μ(d) log d` for primes `p < N` coprime to `N`,
any divisor `d ≤ D` of `N - p` is automatically coprime to `N` and restricts `p` to
the single unit residue class `p ≡ N (mod d)`, giving an exact split into short
progression sums (`d ≤ D`) and the long-divisor tail (`D < d`).
-/

namespace ReflectedDivisorExactSplit

open Finset Real

noncomputable section

def muR (d : ℕ) : ℝ := ((ArithmeticFunction.moebius d : ℤ) : ℝ)

private lemma coprime_and_mod_of_dvd_sub {N p d : ℕ} (hpN : p < N) (hp : Nat.Coprime p N)
    (hd : d ∣ N - p) : Nat.Coprime d N ∧ p % d = N % d := by
  have hsub : p + (N - p) = N := Nat.add_sub_of_le hpN.le
  refine ⟨?_, ?_⟩
  · refine Nat.coprime_of_dvd fun k hk hkd hkN => ?_
    have hksub : k ∣ N - p := hkd.trans hd
    have hkp : k ∣ p := (Nat.dvd_add_left hksub).mp (by rwa [hsub])
    exact hk.ne_one (Nat.dvd_one.mp (hp ▸ Nat.dvd_gcd hkp hkN))
  · have hme : p ≡ N [MOD d] := (Nat.modEq_iff_dvd' hpN.le).2 hd
    exact hme

private lemma filter_divisors_eq {N D p : ℕ} (hpN : p < N) (hp : Nat.Coprime p N) :
    (Nat.divisors (N - p)).filter (fun d => d ≤ D) =
      ((Finset.Icc 1 D).filter (fun d => Nat.Coprime d N)).filter (fun d => p % d = N % d) := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hd_dvd, hne⟩, hdD⟩
    have hd_pos : 1 ≤ d := Nat.pos_of_ne_zero fun h0 => by
      subst h0
      exact hne (zero_dvd_iff.mp hd_dvd)
    obtain ⟨hcop, hmod⟩ := coprime_and_mod_of_dvd_sub hpN hp hd_dvd
    exact ⟨⟨⟨hd_pos, hdD⟩, hcop⟩, hmod⟩
  · rintro ⟨⟨⟨_, hdD⟩, _⟩, hmod⟩
    refine ⟨⟨?_, by omega⟩, hdD⟩
    have hmod' : p ≡ N [MOD d] := hmod
    exact (Nat.modEq_iff_dvd' hpN.le).1 hmod'

theorem main :
    ∀ (N D : ℕ) (η : ℕ → ℝ),
      let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ);
      let Λ := ArithmeticFunction.vonMangoldt;
      let P := (Finset.range N).filter (fun p => Nat.Prime p ∧ Nat.Coprime p N);
      (∑ p ∈ P, η p * Λ (N - p)) =
        (-(∑ d ∈ (Finset.Icc 1 D).filter (fun d => Nat.Coprime d N),
            μ d * Real.log (d : ℝ) * ∑ p ∈ P.filter (fun p => p % d = N % d), η p)) +
        (-(∑ p ∈ P, η p *
            ∑ d ∈ (Nat.divisors (N - p)).filter (fun d => D < d), μ d * Real.log (d : ℝ))) := by
  intro N D η
  dsimp only
  let P := (Finset.range N).filter (fun p => Nat.Prime p ∧ Nat.Coprime p N)
  let shortD := (Finset.Icc 1 D).filter (fun d => Nat.Coprime d N)
  change (∑ p ∈ P, η p * ArithmeticFunction.vonMangoldt (N - p)) =
    (-(∑ d ∈ shortD, muR d * Real.log (d : ℝ) * ∑ p ∈ P.filter (fun p => p % d = N % d), η p)) +
    (-(∑ p ∈ P, η p *
      ∑ d ∈ (Nat.divisors (N - p)).filter (fun d => D < d), muR d * Real.log (d : ℝ)))
  have hsplit : ∀ p ∈ P,
      η p * ArithmeticFunction.vonMangoldt (N - p) =
        -(η p * ∑ d ∈ (Nat.divisors (N - p)).filter (fun d => d ≤ D), muR d * Real.log (d : ℝ)) +
        -(η p * ∑ d ∈ (Nat.divisors (N - p)).filter (fun d => D < d), muR d * Real.log (d : ℝ)) := by
    intro p _
    have hlam : ArithmeticFunction.vonMangoldt (N - p) =
        -(∑ d ∈ (Nat.divisors (N - p)), muR d * Real.log (d : ℝ)) := by
      have h := ArithmeticFunction.sum_moebius_mul_log_eq (n := N - p)
      change (∑ d ∈ Nat.divisors (N - p), muR d * Real.log (d : ℝ)) =
        -ArithmeticFunction.vonMangoldt (N - p) at h
      linarith
    have hdiv := Finset.sum_filter_add_sum_filter_not (Nat.divisors (N - p)) (fun d => d ≤ D)
      (fun d => muR d * Real.log (d : ℝ))
    have hnot : (Nat.divisors (N - p)).filter (fun d => ¬ d ≤ D) =
        (Nat.divisors (N - p)).filter (fun d => D < d) := by
      ext d
      simp [not_le]
    rw [hnot] at hdiv
    rw [hlam, ← hdiv]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    Finset.sum_neg_distrib]
  congr 1
  congr 1
  have hlhs : (∑ p ∈ P, η p *
      ∑ d ∈ (Nat.divisors (N - p)).filter (fun d => d ≤ D), muR d * Real.log (d : ℝ)) =
      ∑ p ∈ P, ∑ d ∈ shortD, if p % d = N % d then η p * (muR d * Real.log (d : ℝ)) else 0 := by
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hp_range, _, hp_cop⟩ := Finset.mem_filter.mp hp
    have hpN : p < N := Finset.mem_range.mp hp_range
    rw [filter_divisors_eq hpN hp_cop, Finset.mul_sum, Finset.sum_filter]
  have hrhs : (∑ d ∈ shortD,
      muR d * Real.log (d : ℝ) * ∑ p ∈ P.filter (fun p => p % d = N % d), η p) =
      ∑ d ∈ shortD, ∑ p ∈ P, if p % d = N % d then η p * (muR d * Real.log (d : ℝ)) else 0 := by
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> ring
  rw [hlhs, hrhs, Finset.sum_comm]

end

end ReflectedDivisorExactSplit

theorem PEqualNP.Outside.L_goldbach_reflected_divisor_exact_split :
    ∀ (N D : ℕ) (η : ℕ → ℝ),
      let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ);
      let Λ := ArithmeticFunction.vonMangoldt;
      let P := (Finset.range N).filter (fun p => Nat.Prime p ∧ Nat.Coprime p N);
      (∑ p ∈ P, η p * Λ (N - p)) =
        (-(∑ d ∈ (Finset.Icc 1 D).filter (fun d => Nat.Coprime d N),
            μ d * Real.log (d : ℝ) * ∑ p ∈ P.filter (fun p => p % d = N % d), η p)) +
        (-(∑ p ∈ P, η p *
            ∑ d ∈ (Nat.divisors (N - p)).filter (fun d => D < d), μ d * Real.log (d : ℝ))) := by
  exact ReflectedDivisorExactSplit.main
