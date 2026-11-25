import Mathlib

/-!
# TH-0073: polylogarithmic energy of the exact unit-class model

For the exact unit-class density `μ q r = q / φ q` on the reduced residues, the energy

`U n q = ∑_{r < q} #(F n q r) * (μ q r)²`

grows at most like `(n + 1) * (log (q + 2))²`, with a constant independent of `q`.
The proof uses the total fibre mass `∑_r #(F n q r) = n + 1` and the elementary
bound `q / φ q ≤ ω(q) + 1 ≤ log₂ q + 1 ≤ 4 log (q + 2)`.
-/

namespace GoldbachCosetUnitEnergy

/-- The residue-class fibre `F n q r = {k ≤ n : k % q = r}`. -/
private def cF (n q r : ℕ) : Finset ℕ := (Finset.range (n + 1)).filter (fun k => k % q = r)

/-- The exact unit-class density: `q / φ q` on the reduced residues, `0` elsewhere. -/
private def cMu (q r : ℕ) : ℝ := if r.Coprime q then (q : ℝ) / (q.totient : ℝ) else 0

/-- The energy of the unit-class model. -/
private def cU (n q : ℕ) : ℝ := ∑ r ∈ Finset.range q, ((cF n q r).card : ℝ) * (cMu q r) ^ 2

/-- The fibres over the residue classes partition `{0, …, n}`. -/
private theorem mass_eq (n q : ℕ) (hq : 0 < q) :
    ∑ r ∈ Finset.range q, ((cF n q r).card : ℝ) = ((n + 1 : ℕ) : ℝ) := by
  have hcard := Finset.card_eq_sum_card_fiberwise (f := fun k : ℕ => k % q)
    (s := Finset.range (n + 1)) (t := Finset.range q)
    (fun k hk => Finset.mem_range.mpr (Nat.mod_lt k hq))
  have hreal : ((Finset.range (n + 1)).card : ℝ)
      = ∑ r ∈ Finset.range q,
          (((Finset.range (n + 1)).filter (fun k => k % q = r)).card : ℝ) := by
    rw [hcard]
    push_cast
  simpa [cF] using hreal

/-- For a finite set of integers at least two, `∏ p ≤ (#s + 1) ∏ (p - 1)`. -/
private theorem prod_le_succ_mul_prod_pred (s : Finset ℕ) (h2 : ∀ p ∈ s, 2 ≤ p) :
    (∏ p ∈ s, (p : ℝ)) ≤ ((s.card : ℝ) + 1) * ∏ p ∈ s, ((p : ℝ) - 1) := by
  classical
  have key : ∀ M : ℕ, ∀ s : Finset ℕ, (∀ p ∈ s, 2 ≤ p) → (∀ p ∈ s, p ≤ M) →
      (∏ p ∈ s, (p : ℝ)) ≤ ((s.card : ℝ) + 1) * ∏ p ∈ s, ((p : ℝ) - 1) := by
    intro M
    refine Nat.strong_induction_on M ?_
    intro N ih s h2s hMs
    rcases Nat.lt_or_ge N 2 with hN | hN
    · have hs : s = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        have h1 := h2s p hp
        have h2' := hMs p hp
        omega
      rw [hs]
      simp
    · by_cases hNs : N ∈ s
      · set t := s.erase N with ht
        have hNt : N ∉ t := Finset.not_mem_erase N s
        have hst : s = insert N t := (Finset.insert_erase hNs).symm
        have ht2 : ∀ p ∈ t, 2 ≤ p := by
          intro p hp
          exact h2s p (Finset.mem_of_mem_erase hp)
        have htN : ∀ p ∈ t, p ≤ N - 1 := by
          intro p hp
          have hp' := Finset.mem_erase.mp hp
          have hle := hMs p hp'.2
          omega
        have hcard : t.card + 2 ≤ N := by
          have hsub : t ⊆ Finset.Icc 2 (N - 1) := by
            intro p hp
            exact Finset.mem_Icc.mpr ⟨ht2 p hp, htN p hp⟩
          have hle := Finset.card_le_card hsub
          rw [Finset.card_Icc] at hle
          omega
        have hnR : ((t.card : ℝ) + 2) ≤ (N : ℝ) := by exact_mod_cast hcard
        have hQ : 0 ≤ ∏ p ∈ t, ((p : ℝ) - 1) := by
          apply Finset.prod_nonneg
          intro p hp
          have := ht2 p hp
          linarith
        have ih_t := ih (N - 1) (by omega) t ht2 htN
        have hstep : (N : ℝ) * (∏ p ∈ t, (p : ℝ))
            ≤ (N : ℝ) * (((t.card : ℝ) + 1) * ∏ p ∈ t, ((p : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_left ih_t (by positivity)
        have hineq : ((t.card : ℝ) + 1) * (N : ℝ)
            ≤ ((t.card : ℝ) + 2) * ((N : ℝ) - 1) := by
          nlinarith [hnR]
        have hstep2 : (N : ℝ) * (((t.card : ℝ) + 1) * ∏ p ∈ t, ((p : ℝ) - 1))
            ≤ ((t.card : ℝ) + 2) * (((N : ℝ) - 1) * ∏ p ∈ t, ((p : ℝ) - 1)) := by
          calc (N : ℝ) * (((t.card : ℝ) + 1) * ∏ p ∈ t, ((p : ℝ) - 1))
              = (((t.card : ℝ) + 1) * (N : ℝ)) * ∏ p ∈ t, ((p : ℝ) - 1) := by ring
            _ ≤ (((t.card : ℝ) + 2) * ((N : ℝ) - 1)) * ∏ p ∈ t, ((p : ℝ) - 1) :=
                mul_le_mul_of_nonneg_right hineq hQ
            _ = ((t.card : ℝ) + 2) * (((N : ℝ) - 1) * ∏ p ∈ t, ((p : ℝ) - 1)) := by ring
        rw [hst]
        rw [Finset.prod_insert hNt, Finset.prod_insert hNt]
        calc (N : ℝ) * ∏ p ∈ t, (p : ℝ)
            ≤ (N : ℝ) * (((t.card : ℝ) + 1) * ∏ p ∈ t, ((p : ℝ) - 1)) := hstep
          _ ≤ ((t.card : ℝ) + 2) * (((N : ℝ) - 1) * ∏ p ∈ t, ((p : ℝ) - 1)) := hstep2
          _ = (((insert N t).card : ℝ) + 1) * (((N : ℝ) - 1) * ∏ p ∈ t, ((p : ℝ) - 1)) := by
              rw [Finset.card_insert_of_notMem hNt]
              push_cast
              ring
      · have hs_le : ∀ p ∈ s, p ≤ N - 1 := by
          intro p hp
          have hne : p ≠ N := fun h => hNs (h ▸ hp)
          have hle := hMs p hp
          omega
        exact ih (N - 1) (by omega) s h2s hs_le
  exact key (s.sum id) s h2 (fun p hp => Finset.single_le_sum (fun i _ => Nat.zero_le i) hp)

/-- The totient ratio grows at most logarithmically. -/
private theorem ratio_bounded (q : ℕ) (hq : 0 < q) :
    (q : ℝ) / (q.totient : ℝ) ≤ 4 * Real.log ((q + 2 : ℕ) : ℝ) := by
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by
    have h : 0 < q.totient := Nat.totient_pos.mpr hq
    exact_mod_cast h
  have h2p : ∀ p ∈ q.primeFactors, 2 ≤ p := by
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).two_le
  have htot := Nat.totient_mul_prod_primeFactors q
  have hreal : (q.totient : ℝ) * (∏ p ∈ q.primeFactors, (p : ℝ))
      = (q : ℝ) * (∏ p ∈ q.primeFactors, ((p : ℝ) - 1)) := by
    have h := congrArg (fun m : ℕ => (m : ℝ)) htot
    push_cast at h
    have hsub : ∀ p ∈ q.primeFactors, ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      intro p hp
      have hp1 : 1 ≤ p := by
        have h := (Nat.prime_of_mem_primeFactors hp).pos
        omega
      rw [Nat.cast_sub hp1]
      norm_num
    rw [Finset.prod_congr rfl hsub] at h
    exact h
  have hBpos : (0 : ℝ) < ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    apply Finset.prod_pos
    intro p hp
    have := h2p p hp
    linarith
  have hratio : (q : ℝ) / (q.totient : ℝ)
      = (∏ p ∈ q.primeFactors, (p : ℝ)) / (∏ p ∈ q.primeFactors, ((p : ℝ) - 1)) := by
    rw [eq_div_iff (ne_of_gt hBpos)]
    rw [div_mul_eq_mul_div, div_eq_iff (ne_of_gt hφpos)]
    rw [mul_comm (∏ p ∈ q.primeFactors, (p : ℝ)) (q.totient : ℝ)]
    exact hreal.symm
  have hprod := prod_le_succ_mul_prod_pred q.primeFactors h2p
  have hratio_le : (q : ℝ) / (q.totient : ℝ) ≤ (q.primeFactors.card : ℝ) + 1 := by
    rw [hratio, div_le_iff₀ hBpos]
    exact hprod
  have h2card : 2 ^ q.primeFactors.card ≤ q := by
    have hdvd : (∏ p ∈ q.primeFactors, p) ∣ q := Nat.prod_primeFactors_dvd q
    have hle : (∏ p ∈ q.primeFactors, p) ≤ q := Nat.le_of_dvd hq hdvd
    have h2le : 2 ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p := by
      have hprod' := Finset.prod_le_prod (s := q.primeFactors) (f := fun _ => (2 : ℕ))
        (g := fun p => p) (fun p hp => h2p p hp)
      simpa [Finset.prod_const] using hprod'
    exact le_trans h2le hle
  have h2cardR : (2 : ℝ) ^ q.primeFactors.card ≤ (q : ℝ) := by exact_mod_cast h2card
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ q.primeFactors.card) h2cardR
  rw [Real.log_pow] at hlog
  by_cases hq1 : q = 1
  · subst q
    have hle0 : ((1 : ℕ).primeFactors.card : ℝ) ≤ 0 := by
      have h' : ((1 : ℕ).primeFactors.card : ℝ) * Real.log 2 ≤ (0 : ℝ) * Real.log 2 := by
        simpa using hlog
      exact le_of_mul_le_mul_right h' (Real.log_pos (by norm_num))
    have h3 : ((1 + 2 : ℕ) : ℝ) = 3 := by norm_num
    rw [h3]
    have h23 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
    nlinarith [hle0, Real.log_two_gt_d9, h23]
  · have hq2 : 2 ≤ q := by omega
    have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
    have hL2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hL2half : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hLq_ge : Real.log 2 ≤ Real.log (q : ℝ) := Real.log_le_log (by norm_num) hq2R
    have hLq_half : (1 / 2 : ℝ) ≤ Real.log (q : ℝ) := le_trans hL2half hLq_ge
    have hcard_le : (q.primeFactors.card : ℝ) ≤ 2 * Real.log (q : ℝ) := by
      have hc_nonneg : (0 : ℝ) ≤ (q.primeFactors.card : ℝ) := by positivity
      have h1 : (q.primeFactors.card : ℝ) * (1 / 2)
          ≤ (q.primeFactors.card : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_left hL2half hc_nonneg
      linarith [hlog, h1]
    have hone : (1 : ℝ) ≤ 2 * Real.log (q : ℝ) := by linarith
    have hlog_mono : Real.log (q : ℝ) ≤ Real.log ((q + 2 : ℕ) : ℝ) := by
      apply Real.log_le_log (by positivity)
      push_cast
      linarith
    have hfinal : (q.primeFactors.card : ℝ) + 1 ≤ 4 * Real.log ((q + 2 : ℕ) : ℝ) := by
      nlinarith [hcard_le, hone, hlog_mono]
    exact le_trans hratio_le hfinal

end GoldbachCosetUnitEnergy

open GoldbachCosetUnitEnergy in
theorem PEqualNP.Outside.L_goldbach_coset_unit_energy_upper :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q = r)
    let μ := fun q r : ℕ => if r.Coprime q then (q:ℝ)/(q.totient:ℝ) else 0
    let U := fun n q => ∑ r ∈ Finset.range q, ((F n q r).card:ℝ)*(μ q r)^2
    ∃ C : ℝ, 0<C ∧ ∀ n q : ℕ, 0<q → U n q ≤ C*((n+1:ℕ):ℝ)*(Real.log ((q+2:ℕ):ℝ))^2 := by
  classical
  dsimp only
  refine ⟨16, by norm_num, ?_⟩
  intro n q hq
  change cU n q ≤ 16 * ((n + 1 : ℕ) : ℝ) * (Real.log ((q + 2 : ℕ) : ℝ)) ^ 2
  have hMnonneg : 0 ≤ (q : ℝ) / (q.totient : ℝ) := by
    have hφpos : (0 : ℝ) < (q.totient : ℝ) := by
      have h : 0 < q.totient := Nat.totient_pos.mpr hq
      exact_mod_cast h
    positivity
  have hMu_nonneg : ∀ r : ℕ, 0 ≤ cMu q r := by
    intro r
    by_cases h : r.Coprime q
    · simp only [cMu, h, if_true]
      positivity
    · simp only [cMu, h, if_false]
      norm_num
  have hMu_le : ∀ r : ℕ, cMu q r ≤ (q : ℝ) / (q.totient : ℝ) := by
    intro r
    by_cases h : r.Coprime q
    · simp only [cMu, h, if_true]
    · simp only [cMu, h, if_false]
      exact hMnonneg
  have hratio := ratio_bounded q hq
  have hMsq : ((q : ℝ) / (q.totient : ℝ)) ^ 2
      ≤ (4 * Real.log ((q + 2 : ℕ) : ℝ)) ^ 2 := by
    have hCnonneg : 0 ≤ 4 * Real.log ((q + 2 : ℕ) : ℝ) := by
      have hLpos : 0 < Real.log ((q + 2 : ℕ) : ℝ) := by
        apply Real.log_pos
        push_cast
        have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
        linarith
      positivity
    calc ((q : ℝ) / (q.totient : ℝ)) ^ 2 = (q : ℝ) / (q.totient : ℝ) * ((q : ℝ) / (q.totient : ℝ)) := by
          ring
      _ ≤ (4 * Real.log ((q + 2 : ℕ) : ℝ)) * (4 * Real.log ((q + 2 : ℕ) : ℝ)) :=
          mul_le_mul hratio hratio hMnonneg hCnonneg
      _ = (4 * Real.log ((q + 2 : ℕ) : ℝ)) ^ 2 := by ring
  have hsum : ∑ r ∈ Finset.range q, ((cF n q r).card : ℝ) * (cMu q r) ^ 2
      ≤ ((n + 1 : ℕ) : ℝ) * (4 * Real.log ((q + 2 : ℕ) : ℝ)) ^ 2 := by
    calc ∑ r ∈ Finset.range q, ((cF n q r).card : ℝ) * (cMu q r) ^ 2
        ≤ ∑ r ∈ Finset.range q, ((cF n q r).card : ℝ) * ((q : ℝ) / (q.totient : ℝ)) ^ 2 := by
          apply Finset.sum_le_sum
          intro r hr
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc (cMu q r) ^ 2 = cMu q r * cMu q r := by ring
            _ ≤ ((q : ℝ) / (q.totient : ℝ)) * ((q : ℝ) / (q.totient : ℝ)) :=
                mul_le_mul (hMu_le r) (hMu_le r) (hMu_nonneg r)
                  (le_trans (hMu_nonneg r) (hMu_le r))
            _ = ((q : ℝ) / (q.totient : ℝ)) ^ 2 := by ring
      _ = (∑ r ∈ Finset.range q, ((cF n q r).card : ℝ)) * ((q : ℝ) / (q.totient : ℝ)) ^ 2 := by
          rw [Finset.sum_mul]
      _ = ((n + 1 : ℕ) : ℝ) * ((q : ℝ) / (q.totient : ℝ)) ^ 2 := by rw [mass_eq n q hq]
      _ ≤ ((n + 1 : ℕ) : ℝ) * (4 * Real.log ((q + 2 : ℕ) : ℝ)) ^ 2 := by
          refine mul_le_mul_of_nonneg_left hMsq ?_
          positivity
  calc cU n q = ∑ r ∈ Finset.range q, ((cF n q r).card : ℝ) * (cMu q r) ^ 2 := rfl
    _ ≤ ((n + 1 : ℕ) : ℝ) * (4 * Real.log ((q + 2 : ℕ) : ℝ)) ^ 2 := hsum
    _ = 16 * ((n + 1 : ℕ) : ℝ) * (Real.log ((q + 2 : ℕ) : ℝ)) ^ 2 := by ring
