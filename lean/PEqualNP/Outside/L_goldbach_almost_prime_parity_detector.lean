import Mathlib

/-!
# Parity detector and semiprime branching for the weighted sieve (W14)

This file formalizes `L-goldbach-almost-prime-parity-detector` under the
`representations` track feeding `L-goldbach-binary-pointwise-positivity` via
the Li–Liu 1+1.9 weighted sieve.

For admissible primes `p < N` with `M < N - p` and either `N - p` prime or
`N - p = r * q` (`r, q ∈ Icc 2 N` prime, `r^10 ≤ q^9`), we have:
1. `D - J = 2 * R`, where `J = ∑_{p ∈ Adm} (-1)^Ω(N - p)` and `R` counts prime `N - p`.
2. `J + R` equals the disjoint partition over primes `r ∈ Icc 2 N` of the semiprime
   branch `N - p = r * q` with `r < q` and `r^10 ≤ q^9`.
-/

namespace AlmostPrimeParityDetector

open Finset

private lemma lt_of_pow_ten_le_pow_nine {r q : ℕ} (hq : 2 ≤ q) (h : r ^ 10 ≤ q ^ 9) : r < q := by
  by_contra! hqr
  have h1 : q ^ 10 ≤ r ^ 10 := Nat.pow_le_pow_left hqr 10
  have h2 : q ^ 9 < q ^ 10 := Nat.pow_lt_pow_right (by omega) (by decide)
  omega

private lemma unique_semiprime_pair {r₁ q₁ r₂ q₂ : ℕ}
    (hr₁ : Nat.Prime r₁) (hq₁ : Nat.Prime q₁) (h₁ : r₁ < q₁)
    (hr₂ : Nat.Prime r₂) (hq₂ : Nat.Prime q₂) (h₂ : r₂ < q₂)
    (heq : r₁ * q₁ = r₂ * q₂) : r₁ = r₂ := by
  have hdvd : r₁ ∣ r₂ * q₂ := ⟨q₁, heq.symm⟩
  rcases hr₁.dvd_mul.mp hdvd with h_r | h_q
  · exact (hr₂.eq_one_or_self_of_dvd r₁ h_r).resolve_left hr₁.ne_one
  · have h1q2 : r₁ = q₂ := (hq₂.eq_one_or_self_of_dvd r₁ h_q).resolve_left hr₁.ne_one
    have hdvd2 : r₂ ∣ r₁ * q₁ := ⟨q₂, heq⟩
    rcases hr₂.dvd_mul.mp hdvd2 with h2_r | h2_q
    · exact ((hr₁.eq_one_or_self_of_dvd r₂ h2_r).resolve_left hr₂.ne_one).symm
    · have h2q1 : r₂ = q₁ := (hq₁.eq_one_or_self_of_dvd r₂ h2_q).resolve_left hr₂.ne_one
      omega

private lemma omega_semiprime {r q : ℕ} (hr : Nat.Prime r) (hq : Nat.Prime q) :
    (r * q).primeFactorsList.length = 2 := by
  rw [(Nat.perm_primeFactorsList_mul hr.ne_zero hq.ne_zero).length_eq,
    List.length_append, Nat.primeFactorsList_prime hr, Nat.primeFactorsList_prime hq]
  simp

theorem main :
    ∀ (N M : ℕ),
      let Adm := (Finset.range N).filter (fun p => Nat.Prime p ∧ M < N - p ∧
        (Nat.Prime (N - p) ∨ ∃ r ∈ Finset.Icc 2 N, ∃ q ∈ Finset.Icc 2 N,
          Nat.Prime r ∧ Nat.Prime q ∧ r ^ 10 ≤ q ^ 9 ∧ N - p = r * q));
      let D : ℤ := (Adm.card : ℤ);
      let J : ℤ := ∑ p ∈ Adm, (-1 : ℤ) ^ (N - p).primeFactorsList.length;
      let R : ℤ := ((Adm.filter (fun p => Nat.Prime (N - p))).card : ℤ);
      let Semi := (Finset.Icc 2 N).filter (fun r => Nat.Prime r);
      D - J = 2 * R ∧
        J + R = ∑ r ∈ Semi, ((Adm.filter (fun p => ∃ q ∈ Finset.Icc 2 N,
          Nat.Prime q ∧ r < q ∧ r ^ 10 ≤ q ^ 9 ∧ N - p = r * q)).card : ℤ) := by
  intro N M
  dsimp only
  let Adm := (Finset.range N).filter (fun p => Nat.Prime p ∧ M < N - p ∧
    (Nat.Prime (N - p) ∨ ∃ r ∈ Finset.Icc 2 N, ∃ q ∈ Finset.Icc 2 N,
      Nat.Prime r ∧ Nat.Prime q ∧ r ^ 10 ≤ q ^ 9 ∧ N - p = r * q))
  let Rfin := Adm.filter (fun p => Nat.Prime (N - p))
  let Sfin := Adm.filter (fun p => ¬ Nat.Prime (N - p))
  let Semi := (Finset.Icc 2 N).filter (fun r => Nat.Prime r)
  have hsplit_sum : ∑ p ∈ Adm, (-1 : ℤ) ^ (N - p).primeFactorsList.length =
      (∑ p ∈ Rfin, (-1 : ℤ) ^ (N - p).primeFactorsList.length) +
        (∑ p ∈ Sfin, (-1 : ℤ) ^ (N - p).primeFactorsList.length) :=
    (Finset.sum_filter_add_sum_filter_not Adm (fun p => Nat.Prime (N - p)) _).symm
  have hR_sum : ∑ p ∈ Rfin, (-1 : ℤ) ^ (N - p).primeFactorsList.length = -(Rfin.card : ℤ) := by
    have hterm : ∀ p ∈ Rfin, (-1 : ℤ) ^ (N - p).primeFactorsList.length = -1 := by
      intro p hp
      have hp_pr : Nat.Prime (N - p) := (Finset.mem_filter.mp hp).2
      simp [Nat.primeFactorsList_prime hp_pr]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    ring
  have hS_sum : ∑ p ∈ Sfin, (-1 : ℤ) ^ (N - p).primeFactorsList.length = (Sfin.card : ℤ) := by
    have hterm : ∀ p ∈ Sfin, (-1 : ℤ) ^ (N - p).primeFactorsList.length = 1 := by
      intro p hp
      obtain ⟨hp_adm, hp_np⟩ := Finset.mem_filter.mp hp
      obtain ⟨_, _, _, hcases⟩ := Finset.mem_filter.mp hp_adm
      rcases hcases with hpr | ⟨r, _, q, _, hr, hq, _, heq⟩
      · exact False.elim (hp_np hpr)
      · rw [heq, omega_semiprime hr hq]
        norm_num
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    ring
  have hcard_split : Adm.card = Rfin.card + Sfin.card := by
    have h := Finset.card_filter_add_card_filter_not (s := Adm) (p := fun p => Nat.Prime (N - p))
    exact h.symm
  have hDJ : (Adm.card : ℤ) - ∑ p ∈ Adm, (-1 : ℤ) ^ (N - p).primeFactorsList.length =
      2 * (Rfin.card : ℤ) := by
    rw [hsplit_sum, hR_sum, hS_sum, hcard_split]
    push_cast
    ring
  have hJR : (∑ p ∈ Adm, (-1 : ℤ) ^ (N - p).primeFactorsList.length) + (Rfin.card : ℤ) =
      (Sfin.card : ℤ) := by
    rw [hsplit_sum, hR_sum, hS_sum]
    ring
  refine ⟨hDJ, hJR.trans ?_⟩
  have hS_eq : Sfin = Semi.biUnion (fun r => Adm.filter (fun p => ∃ q ∈ Finset.Icc 2 N,
      Nat.Prime q ∧ r < q ∧ r ^ 10 ≤ q ^ 9 ∧ N - p = r * q)) := by
    ext p
    simp only [Sfin, Finset.mem_filter, Finset.mem_biUnion, Semi, Finset.mem_Icc]
    constructor
    · rintro ⟨hp_adm, hp_np⟩
      obtain ⟨_, _, _, hcases⟩ := Finset.mem_filter.mp hp_adm
      rcases hcases with hpr | ⟨r, hrI, q, hqI, hr, hq, hpow, heq⟩
      · exact False.elim (hp_np hpr)
      · have hrq : r < q := lt_of_pow_ten_le_pow_nine hq.two_le hpow
        exact ⟨r, ⟨Finset.mem_Icc.mp hrI, hr⟩, hp_adm, q, Finset.mem_Icc.mp hqI, hq, hrq, hpow, heq⟩
    · rintro ⟨r, ⟨_, hr⟩, hp_adm, q, _, hq, _, _, heq⟩
      refine ⟨hp_adm, fun hpr => ?_⟩
      have hlen : (r * q).primeFactorsList.length = [N - p].length := by
        rw [← heq, Nat.primeFactorsList_prime hpr]
      rw [omega_semiprime hr hq] at hlen
      simp at hlen
  have hdisj : (Semi : Set ℕ).PairwiseDisjoint (fun r => Adm.filter (fun p => ∃ q ∈ Finset.Icc 2 N,
      Nat.Prime q ∧ r < q ∧ r ^ 10 ≤ q ^ 9 ∧ N - p = r * q)) := by
    intro r₁ hr₁ r₂ hr₂ hne
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    have hr₁' := (Finset.mem_filter.mp (Finset.mem_coe.mp hr₁)).2
    have hr₂' := (Finset.mem_filter.mp (Finset.mem_coe.mp hr₂)).2
    simp only [Finset.mem_filter] at hp₁ hp₂
    obtain ⟨_, q₁, _, hq₁, hlt₁, _, heq₁⟩ := hp₁
    obtain ⟨_, q₂, _, hq₂, hlt₂, _, heq₂⟩ := hp₂
    exact hne (unique_semiprime_pair hr₁' hq₁ hlt₁ hr₂' hq₂ hlt₂ (heq₁.symm.trans heq₂))
  rw [hS_eq, Finset.card_biUnion hdisj]
  push_cast
  rfl

end AlmostPrimeParityDetector

theorem PEqualNP.Outside.L_goldbach_almost_prime_parity_detector :
    ∀ (N M : ℕ),
      let Adm := (Finset.range N).filter (fun p => Nat.Prime p ∧ M < N - p ∧
        (Nat.Prime (N - p) ∨ ∃ r ∈ Finset.Icc 2 N, ∃ q ∈ Finset.Icc 2 N,
          Nat.Prime r ∧ Nat.Prime q ∧ r ^ 10 ≤ q ^ 9 ∧ N - p = r * q));
      let D : ℤ := (Adm.card : ℤ);
      let J : ℤ := ∑ p ∈ Adm, (-1 : ℤ) ^ (N - p).primeFactorsList.length;
      let R : ℤ := ((Adm.filter (fun p => Nat.Prime (N - p))).card : ℤ);
      let Semi := (Finset.Icc 2 N).filter (fun r => Nat.Prime r);
      D - J = 2 * R ∧
        J + R = ∑ r ∈ Semi, ((Adm.filter (fun p => ∃ q ∈ Finset.Icc 2 N,
          Nat.Prime q ∧ r < q ∧ r ^ 10 ≤ q ^ 9 ∧ N - p = r * q)).card : ℤ) := by
  exact AlmostPrimeParityDetector.main
