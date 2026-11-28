import Mathlib
import Conjectures.Goldbach.PolynomialFourierTransference
import Conjectures.Goldbach.VinogradovPolylogMinorSaving

/-! Almost-all binary Goldbach for two prime subsets with target-dependent compatible local
densities. Adapts Alsetri and Shao (arXiv:2405.18576v1, Section 4) together with the
enveloping sieve and L^p restriction estimate of Green and Tao (arXiv:math/0405581,
Sections 3, 4 and 7) using a discrete Fejer kernel, the verified binary transference
theorem from PR 4281 (Conjectures.Goldbach.PolynomialFourierTransference), and the
verified Siegel-Walfisz and Vinogradov minor-arc bounds from PR 3526
(Conjectures.Goldbach.VinogradovPolylogMinorSaving). -/

namespace PrimeLocalCompatibleColors
open Finset Real
open scoped ComplexConjugate BigOperators
noncomputable section

/-! ### Section 1: Elementary arithmetic, prime-cutoff bounds, and Ruzsa LCM moment -/

lemma harmonic_le (B : ℕ) (hB : 1 ≤ B) :
    ∑ k ∈ Icc 1 B, (1 : ℝ) / (k : ℝ) ≤ 1 + Real.log (B : ℝ) := by
  induction B with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp
    | succ m =>
      have hm1 : 1 ≤ m + 1 := by omega
      have hih := ih hm1
      have hsplit : Icc 1 (m + 2) = insert (m + 2) (Icc 1 (m + 1)) := by
        ext x; simp only [mem_Icc, mem_insert]; omega
      rw [hsplit, sum_insert (by simp)]
      have hpos1 : (0 : ℝ) < (m + 1 : ℕ) := by positivity
      have hpos2 : (0 : ℝ) < (m + 2 : ℕ) := by positivity
      have hlog : (1 : ℝ) / ((m + 2 : ℕ) : ℝ) ≤
          Real.log ((m + 2 : ℕ) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ) := by
        rw [← Real.log_div hpos2.ne' hpos1.ne']
        have hstep := Real.one_sub_inv_le_log_of_pos (div_pos hpos2 hpos1)
        have hcalc : 1 - (((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ))⁻¹ =
            1 / ((m + 2 : ℕ) : ℝ) := by
          field_simp; push_cast; ring
        linarith
      linarith

lemma log_le_harmonic (K : ℕ) :
    Real.log ((K + 1 : ℕ) : ℝ) ≤ ∑ j ∈ range K, (1 : ℝ) / ((j + 1 : ℕ) : ℝ) := by
  induction K with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hpos1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hpos2 : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
    have hstep : Real.log ((k + 2 : ℕ) : ℝ) - Real.log ((k + 1 : ℕ) : ℝ) ≤
        (1 : ℝ) / ((k + 1 : ℕ) : ℝ) := by
      rw [← Real.log_div hpos2.ne' hpos1.ne']
      have h1 := Real.log_le_sub_one_of_pos (div_pos hpos2 hpos1)
      have h2 : ((k + 2 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) - 1 = 1 / ((k + 1 : ℕ) : ℝ) := by
        field_simp; push_cast; ring
      linarith
    linarith

lemma one_add_log_le_rpow (c : ℝ) (hc : 0 < c) {x : ℝ} (hx : 1 ≤ x) :
    1 + Real.log x ≤ (1 + 1 / c) * x ^ c := by
  have hxpos : 0 < x := by linarith
  have h1 : Real.log (x ^ c) ≤ x ^ c - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hxpos c)
  rw [Real.log_rpow hxpos] at h1
  have h2 : Real.log x ≤ (x ^ c - 1) / c := (le_div_iff₀ hc).mpr (by linarith)
  have h3 : (1 : ℝ) ≤ x ^ c := Real.one_le_rpow hx hc.le
  have h4 : (x ^ c - 1) / c ≤ (1 / c) * x ^ c := by
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right (by linarith) hc.le
  nlinarith

lemma dvd_prod_decomp : ∀ {n : ℕ} (u : Fin n → ℕ) (g : ℕ),
    g ∣ ∏ i, u i → ∃ v : Fin n → ℕ, (∀ i, v i ∣ u i) ∧ ∏ i, v i = g
  | 0, _, g, hg => by
    have h1 : g ∣ 1 := by simpa using hg
    exact ⟨Fin.elim0, fun i => i.elim0, (Nat.dvd_one.mp h1).symm⟩
  | n + 1, u, g, hg => by
    rw [Fin.prod_univ_succ] at hg
    let g0 := Nat.gcd g (u 0)
    by_cases hg0 : g0 = 0
    · have hgzero : g = 0 := (Nat.gcd_eq_zero_iff.mp hg0).1
      have hu0 : u 0 = 0 := (Nat.gcd_eq_zero_iff.mp hg0).2
      refine ⟨Fin.cons 0 (fun j : Fin n => u j.succ), ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ ?_ i
        · simp [hu0]
        · intro j; exact dvd_refl _
      · rw [Fin.prod_univ_succ, Fin.cons_zero, zero_mul, hgzero]
    · have hpos : 0 < g0 := Nat.pos_of_ne_zero hg0
      have hg0_dvd_g : g0 ∣ g := Nat.gcd_dvd_left g (u 0)
      have hg0_dvd_u0 : g0 ∣ u 0 := Nat.gcd_dvd_right g (u 0)
      let g' := g / g0
      have hmul : g0 * g' = g := Nat.mul_div_cancel' hg0_dvd_g
      have hcop : Nat.Coprime g' (u 0 / g0) := Nat.coprime_div_gcd_div_gcd hpos
      have hg'_dvd : g' ∣ ∏ i : Fin n, u i.succ := by
        have h1 : g0 * g' ∣ g0 * ((u 0 / g0) * ∏ i : Fin n, u i.succ) := by
          rw [hmul, ← mul_assoc, Nat.mul_div_cancel' hg0_dvd_u0]
          exact hg
        have h2 : g' ∣ (u 0 / g0) * ∏ i : Fin n, u i.succ :=
          (Nat.mul_dvd_mul_iff_left hpos).mp h1
        exact hcop.dvd_of_dvd_mul_left h2
      obtain ⟨v', hv'd, hv'p⟩ := dvd_prod_decomp (fun i : Fin n => u i.succ) g' hg'_dvd
      refine ⟨Fin.cons g0 v', ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ ?_ i
        · exact hg0_dvd_u0
        · intro j; exact hv'd j
      · rw [Fin.prod_univ_succ, Fin.cons_zero]
        simp only [Fin.cons_succ]
        rw [hv'p, hmul]

/-- Ruzsa's LCM moment injection: encodes m-tuples in [1, B] into (2^m - 1)-tuples
in [1, B] whose product equals the LCM of the original tuple. -/
lemma ruzsa_lcm_exists_inj (m B : ℕ) :
    ∃ φ : (Fin m → ℕ) → (Fin (2 ^ m - 1) → ℕ),
      (∀ q, (∀ i, q i ∈ Icc 1 B) →
        (∀ j, φ q j ∈ Icc 1 B) ∧ ∏ j, φ q j = Finset.univ.lcm q) ∧
      Set.InjOn φ {q | ∀ i, q i ∈ Icc 1 B} := by
  induction m with
  | zero =>
    refine ⟨fun _ => Fin.elim0, ?_, ?_⟩
    · intro q _; exact ⟨fun j => j.elim0, by simp⟩
    · intro q₁ _ q₂ _ _; funext i; exact i.elim0
  | succ m ih =>
    obtain ⟨φ, hφ_prop, hφ_inj⟩ := ih
    let K := 2 ^ m - 1
    have hK_pos : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
    have hcard : K + K + 1 = 2 ^ (m + 1) - 1 := by
      dsimp [K]; rw [pow_succ]; omega
    let step : (Fin m → ℕ) × ℕ → (Fin K → ℕ) × (Fin K → ℕ) × ℕ := fun ⟨q, r⟩ =>
      let u : Fin K → ℕ := φ q
      let g := Nat.gcd (∏ j, u j) r
      let v := Classical.choose (dvd_prod_decomp u g (Nat.gcd_dvd_left _ _))
      (fun j => u j / v j, v, r / g)
    let enc : (Fin K → ℕ) × (Fin K → ℕ) × ℕ → (Fin (2 ^ (m + 1) - 1) → ℕ) :=
      fun ⟨a, b, c⟩ idx =>
        if h1 : idx.val < K then a ⟨idx.val, h1⟩
        else if h2 : idx.val < K + K then b ⟨idx.val - K, by omega⟩
        else c
    let ψ : (Fin (m + 1) → ℕ) → (Fin (2 ^ (m + 1) - 1) → ℕ) := fun q =>
      enc (step (fun i => q i.castSucc, q (Fin.last m)))
    have henc_prod : ∀ (a b : Fin K → ℕ) (c : ℕ),
        ∏ idx : Fin (2 ^ (m + 1) - 1), enc (a, b, c) idx = (∏ j, a j) * (∏ j, b j) * c := by
      intro a b c
      let e : Fin (K + K + 1) ≃ Fin (2 ^ (m + 1) - 1) := finCongr hcard
      rw [← Equiv.prod_comp e]
      rw [Fin.prod_univ_castSucc]
      have hlast : enc (a, b, c) (e (Fin.last (K + K))) = c := by
        dsimp [enc, e]
        have h1 : ¬ K + K < K := by omega
        have h2 : ¬ K + K < K + K := by omega
        simp [h1]
      rw [hlast]
      congr 1
      rw [Fin.prod_univ_add]
      congr 1
      · apply prod_congr rfl; intro j _
        dsimp [enc, e]; simp [j.isLt]
      · apply prod_congr rfl; intro j _
        dsimp [enc, e]
        have h1 : ¬ K + j.val < K := by omega
        have h2 : K + j.val < K + K := by omega
        simp [h1, h2]
    refine ⟨ψ, ?_, ?_⟩
    · intro q hq
      have hq' : ∀ i : Fin m, q i.castSucc ∈ Icc 1 B := fun i => hq i.castSucc
      have hr : q (Fin.last m) ∈ Icc 1 B := hq (Fin.last m)
      obtain ⟨huB, huprod⟩ := hφ_prop (fun i => q i.castSucc) hq'
      let u : Fin K → ℕ := φ (fun i => q i.castSucc)
      let r := q (Fin.last m)
      let g := Nat.gcd (∏ j, u j) r
      let hspec := Classical.choose_spec (dvd_prod_decomp u g (Nat.gcd_dvd_left _ _))
      let v : Fin K → ℕ := Classical.choose (dvd_prod_decomp u g (Nat.gcd_dvd_left _ _))
      have hv_dvd : ∀ j, v j ∣ u j := hspec.1
      have hv_prod : ∏ j, v j = g := hspec.2
      have hstep : step (fun i => q i.castSucc, r) = (fun j => u j / v j, v, r / g) := rfl
      constructor
      · intro idx
        dsimp [ψ, enc]
        rw [hstep]
        split_ifs with h1 h2
        · have hu1 : 1 ≤ u ⟨idx.val, h1⟩ := (mem_Icc.mp (huB ⟨idx.val, h1⟩)).1
          have hu2 : u ⟨idx.val, h1⟩ ≤ B := (mem_Icc.mp (huB ⟨idx.val, h1⟩)).2
          have hvpos : 0 < v ⟨idx.val, h1⟩ :=
            Nat.pos_of_ne_zero fun h => by
              have hdv := hv_dvd ⟨idx.val, h1⟩; rw [h, zero_dvd_iff] at hdv; omega
          have hqpos : 1 ≤ u ⟨idx.val, h1⟩ / v ⟨idx.val, h1⟩ := by
            have hle : v ⟨idx.val, h1⟩ ≤ u ⟨idx.val, h1⟩ :=
              Nat.le_of_dvd (by omega) (hv_dvd ⟨idx.val, h1⟩)
            exact (Nat.le_div_iff_mul_le hvpos).mpr (by omega)
          exact mem_Icc.mpr ⟨hqpos, (Nat.div_le_self _ _).trans hu2⟩
        · have hu1 : 1 ≤ u ⟨idx.val - K, by omega⟩ := (mem_Icc.mp (huB ⟨idx.val - K, by omega⟩)).1
          have hu2 : u ⟨idx.val - K, by omega⟩ ≤ B := (mem_Icc.mp (huB ⟨idx.val - K, by omega⟩)).2
          have hvpos : 1 ≤ v ⟨idx.val - K, by omega⟩ :=
            Nat.pos_of_ne_zero fun h => by
              have hdv := hv_dvd ⟨idx.val - K, by omega⟩; rw [h, zero_dvd_iff] at hdv; omega
          have hvle : v ⟨idx.val - K, by omega⟩ ≤ u ⟨idx.val - K, by omega⟩ :=
            Nat.le_of_dvd (by omega) (hv_dvd ⟨idx.val - K, by omega⟩)
          exact mem_Icc.mpr ⟨hvpos, hvle.trans hu2⟩
        · have hr1 : 1 ≤ r := (mem_Icc.mp hr).1
          have hr2 : r ≤ B := (mem_Icc.mp hr).2
          have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ (by omega)
          have hgle : g ≤ r := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)
          exact mem_Icc.mpr ⟨(Nat.le_div_iff_mul_le hgpos).mpr (by omega),
            (Nat.div_le_self _ _).trans hr2⟩
      · dsimp [ψ]
        rw [hstep, henc_prod (fun j => u j / v j) v (r / g)]
        have hprod_uv : (∏ j : Fin K, u j / v j) * (∏ j : Fin K, v j) = ∏ j : Fin K, u j := by
          rw [← prod_mul_distrib]
          exact prod_congr rfl fun j _ => Nat.div_mul_cancel (hv_dvd j)
        rw [hprod_uv]
        have hlcm_eq : (∏ j : Fin K, u j) * (r / g) = Nat.lcm (∏ j : Fin K, u j) r := by
          have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ (by have := (mem_Icc.mp hr).1; omega)
          apply Nat.eq_of_mul_eq_mul_right hgpos
          rw [mul_assoc, Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)]
          exact (Nat.gcd_mul_lcm _ _).symm.trans (by rw [mul_comm])
        rw [hlcm_eq, huprod]
        have huniv : (Finset.univ : Finset (Fin (m + 1))) =
            insert (Fin.last m) (Finset.univ.image Fin.castSucc) := by
          ext i
          simp only [mem_univ, mem_insert, mem_image, true_and, true_iff]
          exact Fin.lastCases (Or.inl rfl) (fun j => Or.inr ⟨j, rfl⟩) i
        rw [huniv, Finset.lcm_insert, Finset.lcm_image, Nat.lcm_comm]
        rfl
    · intro q₁ hq₁ q₂ hq₂ heq
      have hu_eq : φ (fun i => q₁ i.castSucc) = φ (fun i => q₂ i.castSucc) := by
        funext j
        have h1 := congrFun heq ⟨j.val, by omega⟩
        have h2 := congrFun heq ⟨K + j.val, by omega⟩
        dsimp [ψ, enc, step] at h1 h2
        have hj1 : j.val < K := j.isLt
        have hj2 : ¬ K + j.val < K := by omega
        have hj3 : K + j.val < K + K := by omega
        simp only [hj1, ↓reduceDIte, hj2, hj3, Nat.add_sub_cancel_left] at h1 h2
        let v₁ := Classical.choose (dvd_prod_decomp (φ fun i => q₁ i.castSucc)
          (Nat.gcd (∏ k, φ (fun i => q₁ i.castSucc) k) (q₁ (Fin.last m)))
          (Nat.gcd_dvd_left _ _))
        let v₂ := Classical.choose (dvd_prod_decomp (φ fun i => q₂ i.castSucc)
          (Nat.gcd (∏ k, φ (fun i => q₂ i.castSucc) k) (q₂ (Fin.last m)))
          (Nat.gcd_dvd_left _ _))
        have hd1 : v₁ j ∣ φ (fun i => q₁ i.castSucc) j :=
          (Classical.choose_spec (dvd_prod_decomp (φ fun i => q₁ i.castSucc)
            (Nat.gcd (∏ k, φ (fun i => q₁ i.castSucc) k) (q₁ (Fin.last m)))
            (Nat.gcd_dvd_left _ _))).1 j
        have hd2 : v₂ j ∣ φ (fun i => q₂ i.castSucc) j :=
          (Classical.choose_spec (dvd_prod_decomp (φ fun i => q₂ i.castSucc)
            (Nat.gcd (∏ k, φ (fun i => q₂ i.castSucc) k) (q₂ (Fin.last m)))
            (Nat.gcd_dvd_left _ _))).1 j
        have h1' : φ (fun i => q₁ i.castSucc) j / v₁ j = φ (fun i => q₂ i.castSucc) j / v₂ j := h1
        have h2' : v₁ j = v₂ j := h2
        calc
          φ (fun i => q₁ i.castSucc) j = (φ (fun i => q₁ i.castSucc) j / v₁ j) * v₁ j :=
            (Nat.div_mul_cancel hd1).symm
          _ = (φ (fun i => q₂ i.castSucc) j / v₂ j) * v₂ j := by rw [h1', h2']
          _ = φ (fun i => q₂ i.castSucc) j := Nat.div_mul_cancel hd2
      have hcast : (fun i : Fin m => q₁ i.castSucc) = (fun i : Fin m => q₂ i.castSucc) :=
        hφ_inj (fun i => hq₁ i.castSucc) (fun i => hq₂ i.castSucc) hu_eq
      have hr_eq : q₁ (Fin.last m) = q₂ (Fin.last m) := by
        have hlast := congrFun heq ⟨K + K, by omega⟩
        dsimp [ψ, enc, step] at hlast
        have h1 : ¬ K + K < K := by omega
        have h2 : ¬ K + K < K + K := by omega
        simp only [h1, h2, ↓reduceDIte] at hlast
        have hv_eq : ∀ j : Fin K,
            Classical.choose (dvd_prod_decomp (φ fun i => q₁ i.castSucc)
              (Nat.gcd (∏ k, φ (fun i => q₁ i.castSucc) k) (q₁ (Fin.last m)))
              (Nat.gcd_dvd_left _ _)) j =
            Classical.choose (dvd_prod_decomp (φ fun i => q₂ i.castSucc)
              (Nat.gcd (∏ k, φ (fun i => q₂ i.castSucc) k) (q₂ (Fin.last m)))
              (Nat.gcd_dvd_left _ _)) j := by
          intro j
          have h2j := congrFun heq ⟨K + j.val, by omega⟩
          dsimp [ψ, enc, step] at h2j
          have hj2 : ¬ K + j.val < K := by omega
          have hj3 : K + j.val < K + K := by omega
          simpa only [hj2, hj3, ↓reduceDIte, Nat.add_sub_cancel_left] using h2j
        have hg1 := (Classical.choose_spec (dvd_prod_decomp (φ fun i => q₁ i.castSucc)
          (Nat.gcd (∏ k, φ (fun i => q₁ i.castSucc) k) (q₁ (Fin.last m)))
          (Nat.gcd_dvd_left _ _))).2
        have hg2 := (Classical.choose_spec (dvd_prod_decomp (φ fun i => q₂ i.castSucc)
          (Nat.gcd (∏ k, φ (fun i => q₂ i.castSucc) k) (q₂ (Fin.last m)))
          (Nat.gcd_dvd_left _ _))).2
        have hg_eq : Nat.gcd (∏ k, φ (fun i => q₁ i.castSucc) k) (q₁ (Fin.last m)) =
            Nat.gcd (∏ k, φ (fun i => q₂ i.castSucc) k) (q₂ (Fin.last m)) := by
          rw [← hg1, ← hg2]; exact prod_congr rfl fun j _ => hv_eq j
        calc
          q₁ (Fin.last m) = (q₁ (Fin.last m) / Nat.gcd (∏ k, φ (fun i => q₁ i.castSucc) k) (q₁ (Fin.last m))) *
              Nat.gcd (∏ k, φ (fun i => q₁ i.castSucc) k) (q₁ (Fin.last m)) :=
            (Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)).symm
          _ = (q₂ (Fin.last m) / Nat.gcd (∏ k, φ (fun i => q₂ i.castSucc) k) (q₂ (Fin.last m))) *
              Nat.gcd (∏ k, φ (fun i => q₂ i.castSucc) k) (q₂ (Fin.last m)) := by
            rw [hlast, hg_eq]
          _ = q₂ (Fin.last m) := Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
      funext i
      exact Fin.lastCases hr_eq (fun j => congrFun hcast j) i

lemma ruzsa_lcm_sum (m B : ℕ) (hB : 1 ≤ B) :
    ∑ q ∈ Fintype.piFinset (fun _ : Fin m => Icc 1 B),
      (1 : ℝ) / ((Finset.univ.lcm q : ℕ) : ℝ) ≤ (1 + Real.log (B : ℝ)) ^ (2 ^ m - 1) := by
  classical
  obtain ⟨φ, hφ_prop, hφ_inj⟩ := ruzsa_lcm_exists_inj m B
  let S := Fintype.piFinset (fun _ : Fin m => Icc 1 B)
  let T := Fintype.piFinset (fun _ : Fin (2 ^ m - 1) => Icc 1 B)
  have h1 : ∑ q ∈ S, (1 : ℝ) / ((Finset.univ.lcm q : ℕ) : ℝ) ≤
      ∑ u ∈ T, (1 : ℝ) / ((∏ j, u j : ℕ) : ℝ) := by
    have hmap : ∑ q ∈ S, (1 : ℝ) / ((Finset.univ.lcm q : ℕ) : ℝ) =
        ∑ q ∈ S, (1 : ℝ) / ((∏ j, φ q j : ℕ) : ℝ) := by
      refine sum_congr rfl fun q hq => ?_
      rw [(hφ_prop q (fun i => Fintype.mem_piFinset.mp hq i)).2]
    have himg : ∑ u ∈ S.image φ, (1 : ℝ) / ((∏ j, u j : ℕ) : ℝ) =
        ∑ q ∈ S, (1 : ℝ) / ((∏ j, φ q j : ℕ) : ℝ) := by
      apply sum_image
      intro q₁ hq₁ q₂ hq₂ h
      exact hφ_inj (fun i => Fintype.mem_piFinset.mp hq₁ i)
        (fun i => Fintype.mem_piFinset.mp hq₂ i) h
    rw [hmap, ← himg]
    apply sum_le_sum_of_subset_of_nonneg
    · intro u hu
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hu
      exact Fintype.mem_piFinset.mpr (hφ_prop q (fun i => Fintype.mem_piFinset.mp hq i)).1
    · intro u _ _; positivity
  have h2 : ∑ u ∈ T, (1 : ℝ) / ((∏ j, u j : ℕ) : ℝ) =
      (∑ k ∈ Icc 1 B, (1 : ℝ) / (k : ℝ)) ^ (2 ^ m - 1) := by
    have hfactor : ∀ u : Fin (2 ^ m - 1) → ℕ,
        (1 : ℝ) / ((∏ j, u j : ℕ) : ℝ) = ∏ j, ((1 : ℝ) / (u j : ℝ)) := by
      intro u; push_cast; simp [one_div, prod_inv_distrib]
    simp_rw [hfactor]
    have hpi := (Finset.prod_univ_sum (t := fun _ : Fin (2 ^ m - 1) => Icc 1 B)
      (f := fun _ k => (1 : ℝ) / (k : ℝ))).symm
    simpa [T, prod_const, card_univ] using hpi
  have h3 : (∑ k ∈ Icc 1 B, (1 : ℝ) / (k : ℝ)) ^ (2 ^ m - 1) ≤
      (1 + Real.log (B : ℝ)) ^ (2 ^ m - 1) := by
    apply pow_le_pow_left₀
    · exact sum_nonneg fun k _ => by positivity
    · exact harmonic_le B hB
  exact (h1.trans_eq h2).trans h3

lemma prod_le_prod_nonneg {ι : Type*} {s : Finset ι} {f g : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [prod_insert has, prod_insert has]
    have hfa := hf a (mem_insert_self a s)
    have hga := hfg a (mem_insert_self a s)
    have hfs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (mem_insert_of_mem hi)
    have hfgs : ∀ i ∈ s, f i ≤ g i := fun i hi => hfg i (mem_insert_of_mem hi)
    exact mul_le_mul hga (ih hfs hfgs) (prod_nonneg hfs) (hfa.trans hga)

lemma finset_prod_rpow {ι : Type*} (s : Finset ι) (f : ι → ℝ) (c : ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∏ i ∈ s, f i) ^ c = ∏ i ∈ s, (f i) ^ c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [prod_insert has, prod_insert has]
    have hfa := hf a (mem_insert_self a s)
    have hfs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (mem_insert_of_mem hi)
    rw [Real.mul_rpow hfa (prod_nonneg hfs), ih hfs]

lemma sum_divisors_mul_coprime {β : Type*} [AddCommMonoid β] {u v : ℕ}
    (hu : 1 ≤ u) (hv : 1 ≤ v) (huv : u.Coprime v) (F : ℕ → β) :
    ∑ r ∈ (u * v).divisors, F r = ∑ r₁ ∈ u.divisors, ∑ r₂ ∈ v.divisors, F (r₁ * r₂) := by
  rw [← sum_product']
  symm
  refine Finset.sum_bij (fun x _ => x.1 * x.2) ?_ ?_ ?_ ?_
  · intro ⟨x, y⟩ hxy
    have hx := Nat.dvd_of_mem_divisors (mem_product.mp hxy).1
    have hy := Nat.dvd_of_mem_divisors (mem_product.mp hxy).2
    exact Nat.mem_divisors.mpr ⟨mul_dvd_mul hx hy, by nlinarith⟩
  · intro ⟨x₁, y₁⟩ h1 ⟨x₂, y₂⟩ h2 heq
    have hx1 := Nat.dvd_of_mem_divisors (mem_product.mp h1).1
    have hy1 := Nat.dvd_of_mem_divisors (mem_product.mp h1).2
    have hx2 := Nat.dvd_of_mem_divisors (mem_product.mp h2).1
    have hy2 := Nat.dvd_of_mem_divisors (mem_product.mp h2).2
    have hx : x₁ = x₂ := Nat.dvd_antisymm
      ((huv.coprime_dvd_left hx1 |>.coprime_dvd_right hy2).dvd_of_dvd_mul_right (heq ▸ dvd_mul_right _ _))
      ((huv.coprime_dvd_left hx2 |>.coprime_dvd_right hy1).dvd_of_dvd_mul_right (heq.symm ▸ dvd_mul_right _ _))
    have hy : y₁ = y₂ := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_dvd_of_pos hx1 (by omega)) (hx ▸ heq)
    exact Prod.ext hx hy
  · intro r hr
    have hrd := Nat.dvd_of_mem_divisors hr
    let x := Nat.gcd r u
    let y := Nat.gcd r v
    have hxm : x ∈ u.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right r u, by omega⟩
    have hym : y ∈ v.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right r v, by omega⟩
    refine ⟨(x, y), mem_product.mpr ⟨hxm, hym⟩, ?_⟩
    dsimp [x, y]
    rw [← huv.gcd_mul r, Nat.gcd_eq_left hrd]
  · intro _ _; rfl

lemma prod_primeFactors_pow_eq_self {m : ℕ} (hm : m ≠ 0) :
    ∏ p ∈ m.primeFactors, p ^ (m.factorization p) = m := by
  simpa [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hm

lemma card_divisors_eq_prod_primeFactors {m : ℕ} (hm : 1 ≤ m) :
    m.divisors.card = ∏ p ∈ m.primeFactors, (m.factorization p + 1) := by
  have hm0 : m ≠ 0 := by omega
  have hgen : ∀ (s : Finset ℕ) (e : ℕ → ℕ), (∀ p ∈ s, p.Prime) →
      (∏ p ∈ s, p ^ e p).divisors.card = ∏ p ∈ s, (e p + 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro e _; simp
    | @insert p s hps ih =>
      intro e hs
      have hpp : p.Prime := hs p (mem_insert_self p s)
      have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (mem_insert_of_mem hr)
      have hcop : (p ^ e p).Coprime (∏ r ∈ s, r ^ e r) := by
        apply Nat.Coprime.prod_right
        intro r hr
        exact ((Nat.coprime_primes hpp (hs' r hr)).mpr (fun h => hps (h ▸ hr))).pow _ _
      have hpos1 : 1 ≤ p ^ e p := pow_pos hpp.pos _
      have hpos2 : 1 ≤ ∏ r ∈ s, r ^ e r := prod_pos fun r hr => pow_pos (hs' r hr).pos _
      rw [prod_insert hps, prod_insert hps]
      have hcard : (p ^ e p * ∏ r ∈ s, r ^ e r).divisors.card =
          (p ^ e p).divisors.card * (∏ r ∈ s, r ^ e r).divisors.card := by
        simpa [sum_const, smul_eq_mul] using sum_divisors_mul_coprime hpos1 hpos2 hcop (fun _ => (1 : ℕ))
      rw [hcard, Nat.divisors_prime_pow hpp, card_map, card_range, ih e hs']
  conv_lhs => rw [← prod_primeFactors_pow_eq_self hm0]
  exact hgen m.primeFactors (fun p => m.factorization p) (fun p hp => Nat.prime_of_mem_primeFactors hp)

lemma divisor_bound_eps (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → (m.divisors.card : ℝ) ≤ C * (m : ℝ) ^ c := by
  let α : ℝ := (2 : ℝ) ^ c - 1
  have hα : 0 < α := by
    dsimp [α]
    have h := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hc
    linarith
  let K : ℕ := ⌈(2 : ℝ) ^ (1 / c)⌉₊ + 2
  have hK_pow : (2 : ℝ) ≤ (K : ℝ) ^ c := by
    have hKge : (2 : ℝ) ^ (1 / c) ≤ (K : ℝ) := by
      have h1 : (2 : ℝ) ^ (1 / c) ≤ (⌈(2 : ℝ) ^ (1 / c)⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈(2 : ℝ) ^ (1 / c)⌉₊ : ℝ) ≤ (K : ℝ) := by dsimp [K]; push_cast; linarith
      exact h1.trans h2
    calc
      (2 : ℝ) = ((2 : ℝ) ^ (1 / c)) ^ c := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), one_div_mul_cancel hc.ne', Real.rpow_one]
      _ ≤ (K : ℝ) ^ c := Real.rpow_le_rpow (by positivity) hKge hc.le
  let B : ℝ := 1 + 1 / α
  have hB1 : 1 ≤ B := by dsimp [B]; linarith [div_pos one_pos hα]
  refine ⟨B ^ K, by positivity, ?_⟩
  intro m hm
  have hm0 : m ≠ 0 := by omega
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [← div_le_iff₀ (Real.rpow_pos_of_pos hmpos c)]
  have hfac : m = ∏ p ∈ m.primeFactors, p ^ (m.factorization p) :=
    (prod_primeFactors_pow_eq_self hm0).symm
  have hdiv : (m.divisors.card : ℝ) / (m : ℝ) ^ c =
      ∏ p ∈ m.primeFactors, ((m.factorization p + 1 : ℝ) / ((p ^ (m.factorization p) : ℕ) : ℝ) ^ c) := by
    rw [card_divisors_eq_prod_primeFactors hm, Nat.cast_prod]
    conv_lhs => arg 2; rw [hfac]
    rw [Nat.cast_prod, finset_prod_rpow _ _ c (fun p _ => by positivity), ← prod_div_distrib]
    exact prod_congr rfl fun p _ => by push_cast; rfl
  rw [hdiv]
  have hsplit := (Finset.prod_filter_mul_prod_filter_not m.primeFactors (fun p => p < K)
    (fun p => (m.factorization p + 1 : ℝ) / ((p ^ (m.factorization p) : ℕ) : ℝ) ^ c)).symm
  rw [hsplit]
  have hge_le : ∏ p ∈ m.primeFactors.filter (fun p => ¬ p < K),
      ((m.factorization p + 1 : ℝ) / ((p ^ (m.factorization p) : ℕ) : ℝ) ^ c) ≤ 1 := by
    conv_rhs => rw [← prod_const_one (s := m.primeFactors.filter (fun p => ¬ p < K))]
    apply prod_le_prod_nonneg
    · intro p _; positivity
    · intro p hp
      have hpK : K ≤ p := by have := (mem_filter.mp hp).2; omega
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
      have hpc : (2 : ℝ) ≤ (p : ℝ) ^ c :=
        hK_pow.trans (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hpK) hc.le)
      let k := m.factorization p
      have hpow : ((p ^ k : ℕ) : ℝ) ^ c = ((p : ℝ) ^ c) ^ k := by
        rw [Nat.cast_pow, ← Real.rpow_natCast ((p : ℝ) ^ c), ← Real.rpow_natCast (p : ℝ),
          ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity), mul_comm]
      rw [hpow, div_le_one (by positivity)]
      have h2k : (k + 1 : ℝ) ≤ (2 : ℝ) ^ k := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := k))
      exact h2k.trans (pow_le_pow_left₀ (by norm_num) hpc k)
  have hlt_le : ∏ p ∈ m.primeFactors.filter (fun p => p < K),
      ((m.factorization p + 1 : ℝ) / ((p ^ (m.factorization p) : ℕ) : ℝ) ^ c) ≤ B ^ K := by
    have hterm : ∀ p ∈ m.primeFactors.filter (fun p => p < K),
        (m.factorization p + 1 : ℝ) / ((p ^ (m.factorization p) : ℕ) : ℝ) ^ c ≤ B := by
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have hpc : 1 + α ≤ (p : ℝ) ^ c := by
        dsimp [α]; linarith [Real.rpow_le_rpow (by norm_num) hp2 hc.le]
      let k := m.factorization p
      have hpow : ((p ^ k : ℕ) : ℝ) ^ c = ((p : ℝ) ^ c) ^ k := by
        rw [Nat.cast_pow, ← Real.rpow_natCast ((p : ℝ) ^ c), ← Real.rpow_natCast (p : ℝ),
          ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity), mul_comm]
      rw [hpow, div_le_iff₀ (by positivity)]
      have hbern : 1 + (k : ℝ) * α ≤ ((p : ℝ) ^ c) ^ k := by
        calc
          1 + (k : ℝ) * α ≤ (1 + α) ^ k := one_add_mul_le_pow (by linarith) k
          _ ≤ ((p : ℝ) ^ c) ^ k := pow_le_pow_left₀ (by linarith) hpc k
      have hBmul : (k : ℝ) + 1 ≤ B * (1 + (k : ℝ) * α) := by
        dsimp [B]
        have hka : 0 ≤ (k : ℝ) * α := by positivity
        have hinv : 0 ≤ 1 / α := by positivity
        have heq : (1 + 1 / α) * (1 + (k : ℝ) * α) = ((k : ℝ) + 1) + (k : ℝ) * α + 1 / α := by
          field_simp; ring
        linarith
      exact hBmul.trans (mul_le_mul_of_nonneg_left hbern (by linarith))
    have hcard : (m.primeFactors.filter (fun p => p < K)).card ≤ K := by
      calc
        (m.primeFactors.filter (fun p => p < K)).card ≤ (range K).card := by
          apply card_le_card; intro p hp; exact mem_range.mpr (mem_filter.mp hp).2
        _ = K := card_range K
    calc
      ∏ p ∈ m.primeFactors.filter (fun p => p < K),
          ((m.factorization p + 1 : ℝ) / ((p ^ (m.factorization p) : ℕ) : ℝ) ^ c)
          ≤ ∏ _p ∈ m.primeFactors.filter (fun p => p < K), B :=
        prod_le_prod_nonneg (fun _ _ => by positivity) hterm
      _ = B ^ (m.primeFactors.filter (fun p => p < K)).card := prod_const B
      _ ≤ B ^ K := pow_le_pow_right₀ hB1 hcard
  calc
    (∏ p ∈ m.primeFactors.filter (fun p => p < K), _) *
        (∏ p ∈ m.primeFactors.filter (fun p => ¬ p < K), _)
        ≤ B ^ K * 1 := mul_le_mul hlt_le hge_le (prod_nonneg fun _ _ => by positivity) (by positivity)
    _ = B ^ K := mul_one _

lemma squarefree_eq_prod_primeFactors {q : ℕ} (hq : Squarefree q) :
    q = ∏ p ∈ q.primeFactors, p := by
  have hq0 : q ≠ 0 := hq.ne_zero
  conv_lhs => rw [← prod_primeFactors_pow_eq_self hq0]
  refine prod_congr rfl fun p hp => ?_
  have hle1 : q.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one hq0).mp hq p
  have hpos : 1 ≤ q.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  have heq1 : q.factorization p = 1 := by omega
  rw [heq1, pow_one]

lemma squarefree_totient_eq_prod {q : ℕ} (hq : Squarefree q) :
    q.totient = ∏ p ∈ q.primeFactors, (p - 1) := by
  have hq0 : q ≠ 0 := hq.ne_zero
  have hmul : ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) →
      (∏ p ∈ s, p).totient = ∏ p ∈ s, (p - 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | @insert p s hps ih =>
      intro hs
      have hpp : p.Prime := hs p (mem_insert_self p s)
      have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (mem_insert_of_mem hr)
      have hcop : p.Coprime (∏ r ∈ s, r) := by
        apply Nat.Coprime.prod_right
        intro r hr
        have hrp := hs' r hr
        exact (Nat.coprime_primes hpp hrp).mpr (fun heq => hps (heq ▸ hr))
      rw [prod_insert hps, Nat.totient_mul hcop, Nat.totient_prime hpp, ih hs', prod_insert hps]
  conv_lhs => rw [squarefree_eq_prod_primeFactors hq]
  exact hmul q.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)

lemma three_omega_div_totient_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 1 ≤ q → Squarefree q →
      (3 : ℝ) ^ q.primeFactors.card / (q.totient : ℝ) ≤ C * (q : ℝ) ^ (-(4 / 5 : ℝ)) := by
  let B : ℝ := 3072
  refine ⟨B ^ 1024, by positivity, ?_⟩
  intro q hq hsq
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [Real.rpow_neg hqpos.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hqpos _)]
  have hprod : ((3 : ℝ) ^ q.primeFactors.card / (q.totient : ℝ)) * (q : ℝ) ^ (4 / 5 : ℝ) =
      ∏ p ∈ q.primeFactors, ((3 : ℝ) * (p : ℝ) ^ (4 / 5 : ℝ) / ((p : ℝ) - 1)) := by
    have hqeq : (q : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ) := by
      rw [← Nat.cast_prod]; exact_mod_cast squarefree_eq_prod_primeFactors hsq
    have hphieq : (q.totient : ℝ) = ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
      rw [squarefree_totient_eq_prod hsq, Nat.cast_prod]
      refine prod_congr rfl fun p hp => ?_
      have h1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_le
      exact Nat.cast_sub h1
    rw [hqeq, hphieq, finset_prod_rpow _ _ (4 / 5 : ℝ) (fun _ _ => by positivity)]
    have h3 : (3 : ℝ) ^ q.primeFactors.card = ∏ _p ∈ q.primeFactors, (3 : ℝ) := (prod_const 3).symm
    rw [h3, div_mul_eq_mul_div, ← prod_mul_distrib, ← prod_div_distrib]
  rw [hprod]
  rw [← Finset.prod_filter_mul_prod_filter_not q.primeFactors (fun p => p < 1024)]
  have hge_le : ∏ p ∈ q.primeFactors.filter (fun p => ¬ p < 1024),
      ((3 : ℝ) * (p : ℝ) ^ (4 / 5 : ℝ) / ((p : ℝ) - 1)) ≤ 1 := by
    conv_rhs => rw [← prod_const_one (s := q.primeFactors.filter (fun p => ¬ p < 1024))]
    apply prod_le_prod_nonneg
    · intro p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).two_le
      have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity
    · intro p hp
      have hp1024 : 1024 ≤ p := by have := (mem_filter.mp hp).2; omega
      have hpr : (1024 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1024
      have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      rw [div_le_one hpm1]
      have hpow5 : ((3 : ℝ) * (p : ℝ) ^ (4 / 5 : ℝ)) ^ 5 ≤ ((p : ℝ) - 1) ^ 5 := by
        have h1 : ((3 : ℝ) * (p : ℝ) ^ (4 / 5 : ℝ)) ^ 5 = 243 * (p : ℝ) ^ 4 := by
          rw [mul_pow, ← Real.rpow_natCast ((p : ℝ) ^ (4 / 5 : ℝ)),
            ← Real.rpow_mul (by positivity)]
          norm_num
        have h2 : (3 / 4 : ℝ) * (p : ℝ) ≤ (p : ℝ) - 1 := by linarith
        have h3 : ((3 / 4 : ℝ) * (p : ℝ)) ^ 5 ≤ ((p : ℝ) - 1) ^ 5 :=
          pow_le_pow_left₀ (by positivity) h2 5
        have h4 : 243 * (p : ℝ) ^ 4 ≤ ((3 / 4 : ℝ) * (p : ℝ)) ^ 5 := by
          have : ((3 / 4 : ℝ) * (p : ℝ)) ^ 5 = (243 / 1024 : ℝ) * (p : ℝ) ^ 4 * (p : ℝ) := by ring
          rw [this]
          have hp4 : 0 ≤ (p : ℝ) ^ 4 := by positivity
          nlinarith
        linarith
      exact le_of_pow_le_pow_left₀ (by decide) hpm1.le hpow5
  have hlt_le : ∏ p ∈ q.primeFactors.filter (fun p => p < 1024),
      ((3 : ℝ) * (p : ℝ) ^ (4 / 5 : ℝ) / ((p : ℝ) - 1)) ≤ B ^ 1024 := by
    have hterm : ∀ p ∈ q.primeFactors.filter (fun p => p < 1024),
        (3 : ℝ) * (p : ℝ) ^ (4 / 5 : ℝ) / ((p : ℝ) - 1) ≤ B := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have hp1024 : (p : ℝ) ≤ 1024 := by exact_mod_cast (mem_filter.mp hp).2.le
      have hpm1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
      have hp45 : (p : ℝ) ^ (4 / 5 : ℝ) ≤ (p : ℝ) := by
        conv_rhs => rw [← Real.rpow_one (p : ℝ)]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      calc
        (3 : ℝ) * (p : ℝ) ^ (4 / 5 : ℝ) / ((p : ℝ) - 1)
            ≤ (3 : ℝ) * (p : ℝ) / 1 :=
          div_le_div₀ (by positivity) (by linarith) one_pos hpm1
        _ ≤ B := by dsimp [B]; linarith
    have hcard : (q.primeFactors.filter (fun p => p < 1024)).card ≤ 1024 := by
      calc
        (q.primeFactors.filter (fun p => p < 1024)).card ≤ (range 1024).card := by
          apply card_le_card; intro p hp; exact mem_range.mpr (mem_filter.mp hp).2
        _ = 1024 := card_range 1024
    calc
      ∏ p ∈ q.primeFactors.filter (fun p => p < 1024),
          ((3 : ℝ) * (p : ℝ) ^ (4 / 5 : ℝ) / ((p : ℝ) - 1))
          ≤ ∏ _p ∈ q.primeFactors.filter (fun p => p < 1024), B := by
        apply prod_le_prod_nonneg _ hterm
        intro p hp
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).two_le
        have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
        positivity
      _ = B ^ (q.primeFactors.filter (fun p => p < 1024)).card := prod_const B
      _ ≤ B ^ 1024 := pow_le_pow_right₀ (by dsimp [B]; norm_num) hcard
  have hnonneg : 0 ≤ ∏ p ∈ q.primeFactors.filter (fun p => ¬ p < 1024),
      ((3 : ℝ) * (p : ℝ) ^ (4 / 5 : ℝ) / ((p : ℝ) - 1)) := by
    apply prod_nonneg
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).two_le
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  calc
    (∏ p ∈ q.primeFactors.filter (fun p => p < 1024), _) *
        (∏ p ∈ q.primeFactors.filter (fun p => ¬ p < 1024), _)
        ≤ B ^ 1024 * 1 := mul_le_mul hlt_le hge_le hnonneg (by positivity)
    _ = B ^ 1024 := mul_one _

lemma squarefree_inv_totient_le_divisors {q : ℕ} (hq : 1 ≤ q) (hsq : Squarefree q) :
    (1 : ℝ) / (q.totient : ℝ) ≤ (q.divisors.card : ℝ) / (q : ℝ) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hphipos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  rw [div_le_div_iff₀ hphipos hqpos, one_mul]
  have hqeq : (q : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod]; exact_mod_cast squarefree_eq_prod_primeFactors hsq
  have hphieq : (q.totient : ℝ) = ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    rw [squarefree_totient_eq_prod hsq, Nat.cast_prod]
    refine prod_congr rfl fun p hp => Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le
  have hdiv : (2 : ℝ) ^ q.primeFactors.card ≤ (q.divisors.card : ℝ) := by
    rw [card_divisors_eq_prod_primeFactors hq, Nat.cast_prod]
    have h2 : (2 : ℝ) ^ q.primeFactors.card = ∏ _p ∈ q.primeFactors, (2 : ℝ) := (prod_const 2).symm
    rw [h2]
    apply prod_le_prod_nonneg (fun _ _ => by norm_num)
    intro p hp
    have hpos : 1 ≤ q.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    exact_mod_cast (by omega : 2 ≤ q.factorization p + 1)
  calc
    (q : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ) := hqeq
    _ ≤ ∏ p ∈ q.primeFactors, (2 * ((p : ℝ) - 1)) := by
      apply prod_le_prod_nonneg (fun _ _ => by positivity)
      intro p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      linarith
    _ = (2 : ℝ) ^ q.primeFactors.card * (q.totient : ℝ) := by
      rw [prod_mul_distrib, prod_const, hphieq]
    _ ≤ (q.divisors.card : ℝ) * (q.totient : ℝ) :=
      mul_le_mul_of_nonneg_right hdiv hphipos.le

lemma sum_inv_smooth_le_euler_prod (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (R : ℕ) :
    ∑ k ∈ (Icc 1 R).filter (fun k => k.primeFactors ⊆ s), (1 : ℝ) / (k : ℝ) ≤
      ∏ p ∈ s, ((p : ℝ) / ((p : ℝ) - 1)) := by
  induction s using Finset.induction_on with
  | empty =>
    have hsub : (Icc 1 R).filter (fun k => k.primeFactors ⊆ ∅) ⊆ {1} := by
      intro k hk
      have hk1 : 1 ≤ k := (mem_Icc.mp (mem_filter.mp hk).1).1
      have hpf : k.primeFactors = ∅ := subset_empty.mp (mem_filter.mp hk).2
      rw [mem_singleton]
      by_contra hne
      obtain ⟨p, hpp, hpd⟩ := Nat.exists_prime_and_dvd hne
      have hmem : p ∈ k.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpd, by omega⟩
      rw [hpf] at hmem
      exact notMem_empty p hmem
    calc
      ∑ k ∈ (Icc 1 R).filter (fun k => k.primeFactors ⊆ ∅), (1 : ℝ) / (k : ℝ)
          ≤ ∑ k ∈ ({1} : Finset ℕ), (1 : ℝ) / (k : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = 1 := by simp
      _ = ∏ p ∈ (∅ : Finset ℕ), ((p : ℝ) / ((p : ℝ) - 1)) := by simp
  | @insert p s hps ih =>
    have hpp : p.Prime := hs p (mem_insert_self p s)
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (mem_insert_of_mem hr)
    let T := (Icc 1 R).filter (fun k => k.primeFactors ⊆ insert p s)
    let T' := (Icc 1 R).filter (fun k => k.primeFactors ⊆ s)
    let f : ℕ → ℕ × ℕ := fun k => (k.factorization p, k / p ^ (k.factorization p))
    have hf_maps : ∀ k ∈ T, f k ∈ range (R + 1) ×ˢ T' := by
      intro k hk
      have hk1 : 1 ≤ k := (mem_Icc.mp (mem_filter.mp hk).1).1
      have hkR : k ≤ R := (mem_Icc.mp (mem_filter.mp hk).1).2
      have hkpf : k.primeFactors ⊆ insert p s := (mem_filter.mp hk).2
      let j := k.factorization p
      let k' := k / p ^ j
      have hdvd : p ^ j ∣ k := Nat.ordProj_dvd k p
      have hj_le : j ≤ R := by
        have h1 : j < 2 ^ j := Nat.lt_two_pow_self
        have h2 : 2 ^ j ≤ p ^ j := Nat.pow_le_pow_left hpp.two_le j
        have h3 : p ^ j ≤ k := Nat.le_of_dvd (by omega) hdvd
        omega
      have hk'pos : 1 ≤ k' := by
        have hle : p ^ j ≤ k := Nat.le_of_dvd (by omega) hdvd
        exact (Nat.le_div_iff_mul_le (pow_pos hpp.pos j)).mpr (by omega)
      have hk'R : k' ≤ R := (Nat.div_le_self k _).trans hkR
      have hk'pf : k'.primeFactors ⊆ s := by
        intro r hr
        have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
        have hrd : r ∣ k' := Nat.dvd_of_mem_primeFactors hr
        have hrk : r ∣ k := hrd.trans (Nat.div_dvd_of_dvd hdvd)
        have hrmem : r ∈ insert p s := hkpf (Nat.mem_primeFactors.mpr ⟨hrp, hrk, by omega⟩)
        rcases mem_insert.mp hrmem with hrp_eq | hrs
        · exfalso
          rw [hrp_eq] at hrd
          have hmul : p ^ (j + 1) ∣ k := by
            rw [pow_succ, ← Nat.mul_div_cancel' hdvd]
            exact Nat.mul_dvd_mul_left (p ^ j) hrd
          have hle := (Nat.Prime.pow_dvd_iff_le_factorization hpp (by omega : k ≠ 0)).mp hmul
          omega
        · exact hrs
      exact mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hj_le), mem_filter.mpr ⟨mem_Icc.mpr ⟨hk'pos, hk'R⟩, hk'pf⟩⟩
    have hf_inj : ∀ k₁ ∈ T, ∀ k₂ ∈ T, f k₁ = f k₂ → k₁ = k₂ := by
      intro k₁ hk₁ k₂ hk₂ heq
      have hd1 : p ^ (k₁.factorization p) ∣ k₁ := Nat.ordProj_dvd k₁ p
      have hd2 : p ^ (k₂.factorization p) ∣ k₂ := Nat.ordProj_dvd k₂ p
      have h1 : k₁.factorization p = k₂.factorization p := congrArg Prod.fst heq
      have h2 : k₁ / p ^ (k₁.factorization p) = k₂ / p ^ (k₂.factorization p) := congrArg Prod.snd heq
      calc
        k₁ = p ^ (k₁.factorization p) * (k₁ / p ^ (k₁.factorization p)) := (Nat.mul_div_cancel' hd1).symm
        _ = p ^ (k₂.factorization p) * (k₂ / p ^ (k₂.factorization p)) := by rw [h2, h1]
        _ = k₂ := Nat.mul_div_cancel' hd2
    have hsum_eq : ∑ k ∈ T, (1 : ℝ) / (k : ℝ) =
        ∑ x ∈ T.image f, ((1 : ℝ) / (p : ℝ)) ^ x.1 * ((1 : ℝ) / (x.2 : ℝ)) := by
      rw [sum_image hf_inj]
      refine sum_congr rfl fun k hk => ?_
      have hdvd : p ^ (k.factorization p) ∣ k := Nat.ordProj_dvd k p
      have hkmul : (k : ℝ) = (p : ℝ) ^ (k.factorization p) * ((k / p ^ (k.factorization p) : ℕ) : ℝ) := by
        exact_mod_cast (Nat.mul_div_cancel' hdvd).symm
      dsimp [f]
      rw [hkmul, one_div_pow]
      ring
    have hgeom : ∑ j ∈ range (R + 1), ((1 : ℝ) / (p : ℝ)) ^ j ≤ (p : ℝ) / ((p : ℝ) - 1) := by
      have hp1 : (1 : ℝ) / (p : ℝ) ≠ 1 := by
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
        intro h; rw [div_eq_one_iff_eq (by linarith)] at h; linarith
      rw [geom_sum_eq hp1]
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have hden : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
        have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
        linarith
      have hden' : (1 : ℝ) / (p : ℝ) - 1 ≠ 0 := by linarith
      have heq : (((1 : ℝ) / (p : ℝ)) ^ (R + 1) - 1) / (1 / (p : ℝ) - 1) =
          (1 - ((1 : ℝ) / (p : ℝ)) ^ (R + 1)) / (1 - 1 / (p : ℝ)) := by
        rw [div_eq_div_iff hden' hden.ne']; ring
      rw [heq]
      have hnum : 1 - ((1 : ℝ) / (p : ℝ)) ^ (R + 1) ≤ 1 := by
        have : 0 ≤ ((1 : ℝ) / (p : ℝ)) ^ (R + 1) := by positivity
        linarith
      have hfrac : (1 : ℝ) / (1 - 1 / (p : ℝ)) = (p : ℝ) / ((p : ℝ) - 1) := by
        have hp0 : (p : ℝ) ≠ 0 := by linarith
        have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp
      rw [← hfrac]
      exact div_le_div_of_nonneg_right hnum hden.le
    calc
      ∑ k ∈ T, (1 : ℝ) / (k : ℝ)
          = ∑ x ∈ T.image f, ((1 : ℝ) / (p : ℝ)) ^ x.1 * ((1 : ℝ) / (x.2 : ℝ)) := hsum_eq
      _ ≤ ∑ x ∈ range (R + 1) ×ˢ T', ((1 : ℝ) / (p : ℝ)) ^ x.1 * ((1 : ℝ) / (x.2 : ℝ)) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro x hx; obtain ⟨k, hk, rfl⟩ := mem_image.mp hx; exact hf_maps k hk
        · intro x _ _; positivity
      _ = (∑ j ∈ range (R + 1), ((1 : ℝ) / (p : ℝ)) ^ j) * (∑ k' ∈ T', (1 : ℝ) / (k' : ℝ)) := by
        rw [sum_product, sum_mul_sum]
      _ ≤ ((p : ℝ) / ((p : ℝ) - 1)) * ∏ r ∈ s, ((r : ℝ) / ((r : ℝ) - 1)) := by
        exact mul_le_mul hgeom (ih hs') (sum_nonneg fun _ _ => by positivity) (by
          have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
          have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
          positivity)
      _ = ∏ r ∈ insert p s, ((r : ℝ) / ((r : ℝ) - 1)) := (prod_insert hps).symm

/-! ### Section 2: Green-Tao enveloping sieve and Ramare-Ruzsa Fourier expansion -/

def phase (x : ℝ) : ℂ := GoldbachMajorArc.phase x

lemma phase_zero : phase 0 = 1 := by simp [phase, GoldbachMajorArc.phase]

lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase GoldbachMajorArc.phase
  rw [← Complex.exp_add]; push_cast; congr 1; ring

lemma phase_neg (x : ℝ) : phase (-x) = conj (phase x) := by
  unfold phase GoldbachMajorArc.phase
  rw [← Complex.exp_conj]
  simp [Complex.conj_ofReal, Complex.conj_I, map_mul, map_ofNat]

lemma norm_phase (x : ℝ) : ‖phase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

lemma phase_int (k : ℤ) : phase (k : ℝ) = 1 := by
  unfold phase GoldbachMajorArc.phase
  convert Complex.exp_int_mul_two_pi_mul_I k using 2
  push_cast; ring

lemma phase_sub (x y : ℝ) : phase (x - y) = phase x * conj (phase y) := by
  rw [sub_eq_add_neg, phase_add, phase_neg]

lemma phase_eq_of_int_sub {x y : ℝ} {k : ℤ} (h : x - y = (k : ℝ)) : phase x = phase y := by
  have hx : x = y + (k : ℝ) := by linarith
  rw [hx, phase_add, phase_int, mul_one]

def SF (d R : ℕ) : Finset ℕ :=
  (Icc 1 R).filter (fun q => Squarefree q ∧ q.Coprime d)

def G (d R : ℕ) : ℝ :=
  ∑ q ∈ SF d R, (1 : ℝ) / (q.totient : ℝ)

lemma one_mem_SF {d R : ℕ} (hR : 1 ≤ R) : 1 ∈ SF d R :=
  mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, hR⟩, squarefree_one, Nat.coprime_one_left d⟩

lemma one_le_G {d R : ℕ} (hR : 1 ≤ R) : 1 ≤ G d R := by
  have h1 : (1 : ℝ) / ((1 : ℕ).totient : ℝ) ≤ G d R :=
    single_le_sum (f := fun q => (1 : ℝ) / (q.totient : ℝ))
      (fun _ _ => by positivity) (one_mem_SF hR)
  simpa using h1

lemma G_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ d R : ℕ, 1 ≤ R → G d R ≤ C * (R : ℝ) ^ (1 / 50 : ℝ) := by
  obtain ⟨C₁, hC₁, hdiv⟩ := divisor_bound_eps (1 / 100 : ℝ) (by norm_num)
  refine ⟨101 * C₁, by positivity, ?_⟩
  intro d R hR
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have h1 : G d R ≤ ∑ q ∈ Icc 1 R, C₁ * (R : ℝ) ^ (1 / 100 : ℝ) * ((1 : ℝ) / (q : ℝ)) := by
    calc
      G d R ≤ ∑ q ∈ SF d R, C₁ * (R : ℝ) ^ (1 / 100 : ℝ) * ((1 : ℝ) / (q : ℝ)) := by
        apply sum_le_sum
        intro q hq
        have hq1 : 1 ≤ q := (mem_Icc.mp (mem_filter.mp hq).1).1
        have hqR : q ≤ R := (mem_Icc.mp (mem_filter.mp hq).1).2
        have hsq : Squarefree q := (mem_filter.mp hq).2.1
        have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
        calc
          (1 : ℝ) / (q.totient : ℝ) ≤ (q.divisors.card : ℝ) / (q : ℝ) :=
            squarefree_inv_totient_le_divisors hq1 hsq
          _ ≤ (C₁ * (q : ℝ) ^ (1 / 100 : ℝ)) / (q : ℝ) :=
            div_le_div_of_nonneg_right (hdiv q hq1) hqpos.le
          _ ≤ (C₁ * (R : ℝ) ^ (1 / 100 : ℝ)) / (q : ℝ) := by
            apply div_le_div_of_nonneg_right _ hqpos.le
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hqR) (by norm_num)) hC₁.le
          _ = C₁ * (R : ℝ) ^ (1 / 100 : ℝ) * ((1 : ℝ) / (q : ℝ)) := by ring
      _ ≤ ∑ q ∈ Icc 1 R, C₁ * (R : ℝ) ^ (1 / 100 : ℝ) * ((1 : ℝ) / (q : ℝ)) := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro _ _ _; positivity
  have h2 : ∑ q ∈ Icc 1 R, C₁ * (R : ℝ) ^ (1 / 100 : ℝ) * ((1 : ℝ) / (q : ℝ)) ≤
      C₁ * (R : ℝ) ^ (1 / 100 : ℝ) * (1 + Real.log (R : ℝ)) := by
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (harmonic_le R hR) (by positivity)
  have h3 : 1 + Real.log (R : ℝ) ≤ 101 * (R : ℝ) ^ (1 / 100 : ℝ) := by
    have h3' := one_add_log_le_rpow (1 / 100 : ℝ) (by norm_num) hR1
    norm_num at h3'
    exact h3'
  have h4 : (R : ℝ) ^ (1 / 100 : ℝ) * (R : ℝ) ^ (1 / 100 : ℝ) = (R : ℝ) ^ (1 / 50 : ℝ) := by
    rw [← Real.rpow_add (by positivity)]; norm_num
  calc
    G d R ≤ C₁ * (R : ℝ) ^ (1 / 100 : ℝ) * (1 + Real.log (R : ℝ)) := h1.trans h2
    _ ≤ C₁ * (R : ℝ) ^ (1 / 100 : ℝ) * (101 * (R : ℝ) ^ (1 / 100 : ℝ)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 101 * C₁ * ((R : ℝ) ^ (1 / 100 : ℝ) * (R : ℝ) ^ (1 / 100 : ℝ)) := by ring
    _ = 101 * C₁ * (R : ℝ) ^ (1 / 50 : ℝ) := by rw [h4]

lemma G_lower_bound (d R : ℕ) (hd : 1 ≤ d) (hR : d ^ 2 ≤ R) :
    ((d.totient : ℝ) / (2 * (d : ℝ))) * Real.log (R : ℝ) ≤ G d R := by
  have hR1 : 1 ≤ R := by nlinarith
  -- Step 1: ∑_{m ≤ R, (m, d) = 1} 1/m ≤ G d R via radical fiberwise grouping
  let rad : ℕ → ℕ := fun m => ∏ p ∈ m.primeFactors, p
  have hrad_maps : ∀ m ∈ (Icc 1 R).filter (fun m => m.Coprime d), rad m ∈ SF d R := by
    intro m hm
    have hm1 : 1 ≤ m := (mem_Icc.mp (mem_filter.mp hm).1).1
    have hmR : m ≤ R := (mem_Icc.mp (mem_filter.mp hm).1).2
    have hmcop : m.Coprime d := (mem_filter.mp hm).2
    have hrad_dvd : rad m ∣ m := Nat.prod_primeFactors_dvd m
    have hrad_pos : 1 ≤ rad m := Nat.pos_of_dvd_of_pos hrad_dvd (by omega)
    have hrad_le : rad m ≤ R := (Nat.le_of_dvd (by omega) hrad_dvd).trans hmR
    have hrad_sq : Squarefree (rad m) := by
      rw [Nat.squarefree_iff_prime_squarefree]
      intro p hpp hp2
      have hpd : p ∣ rad m := (dvd_mul_left p p).trans hp2
      have hp_mem : p ∈ m.primeFactors := by
        obtain ⟨r, hr, hpr⟩ := hpp.prime.exists_mem_finset_dvd hpd
        have hrp := Nat.prime_of_mem_primeFactors hr
        have heq := (Nat.prime_dvd_prime_iff_eq hpp hrp).mp hpr
        exact heq ▸ hr
      have hsplit : rad m = p * ∏ r ∈ m.primeFactors.erase p, r :=
        (Finset.mul_prod_erase m.primeFactors id hp_mem).symm
      rw [hsplit] at hp2
      have hp_rest : p ∣ ∏ r ∈ m.primeFactors.erase p, r :=
        (mul_dvd_mul_iff_left hpp.ne_zero).mp hp2
      obtain ⟨r, hr, hpr⟩ := hpp.prime.exists_mem_finset_dvd hp_rest
      have hrp := Nat.prime_of_mem_primeFactors (mem_of_mem_erase hr)
      have heq := (Nat.prime_dvd_prime_iff_eq hpp hrp).mp hpr
      exact (mem_erase.mp hr).1 heq.symm
    have hrad_cop : (rad m).Coprime d := hmcop.coprime_dvd_left hrad_dvd
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hrad_pos, hrad_le⟩, hrad_sq, hrad_cop⟩
  have hstep1 : ∑ m ∈ (Icc 1 R).filter (fun m => m.Coprime d), (1 : ℝ) / (m : ℝ) ≤ G d R := by
    rw [← sum_fiberwise_of_maps_to hrad_maps]
    unfold G
    apply sum_le_sum
    intro q hq
    have hq1 : 1 ≤ q := (mem_Icc.mp (mem_filter.mp hq).1).1
    have hsq : Squarefree q := (mem_filter.mp hq).2.1
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
    let fib := ((Icc 1 R).filter (fun m => m.Coprime d)).filter (fun m => rad m = q)
    let smooth := (Icc 1 R).filter (fun k => k.primeFactors ⊆ q.primeFactors)
    have hdiv_maps : ∀ m ∈ fib, m / q ∈ smooth := by
      intro m hm
      have hm_in := (mem_filter.mp hm).1
      have hrad_eq : rad m = q := (mem_filter.mp hm).2
      have hm1 : 1 ≤ m := (mem_Icc.mp (mem_filter.mp hm_in).1).1
      have hmR : m ≤ R := (mem_Icc.mp (mem_filter.mp hm_in).1).2
      have hqdvd : q ∣ m := hrad_eq ▸ Nat.prod_primeFactors_dvd m
      have hkpos : 1 ≤ m / q :=
        (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using Nat.le_of_dvd (by omega) hqdvd)
      have hkR : m / q ≤ R := (Nat.div_le_self m q).trans hmR
      have hkpf : (m / q).primeFactors ⊆ q.primeFactors := by
        intro p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hpd : p ∣ m := (Nat.dvd_of_mem_primeFactors hp).trans (Nat.div_dvd_of_dvd hqdvd)
        have hpm : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpd, by omega⟩
        have hpq : p ∣ q := hrad_eq ▸ dvd_prod_of_mem _ hpm
        exact Nat.mem_primeFactors.mpr ⟨hpp, hpq, by omega⟩
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hkpos, hkR⟩, hkpf⟩
    have hdiv_inj : ∀ m₁ ∈ fib, ∀ m₂ ∈ fib, m₁ / q = m₂ / q → m₁ = m₂ := by
      intro m₁ hm₁ m₂ hm₂ heq
      have hd1 : q ∣ m₁ := (mem_filter.mp hm₁).2 ▸ Nat.prod_primeFactors_dvd m₁
      have hd2 : q ∣ m₂ := (mem_filter.mp hm₂).2 ▸ Nat.prod_primeFactors_dvd m₂
      calc
        m₁ = q * (m₁ / q) := (Nat.mul_div_cancel' hd1).symm
        _ = q * (m₂ / q) := by rw [heq]
        _ = m₂ := Nat.mul_div_cancel' hd2
    have hfib_sum : ∑ m ∈ fib, (1 : ℝ) / (m : ℝ) =
        (1 / (q : ℝ)) * ∑ k ∈ fib.image (fun m => m / q), (1 : ℝ) / (k : ℝ) := by
      rw [sum_image hdiv_inj, mul_sum]
      refine sum_congr rfl fun m hm => ?_
      have hqdvd : q ∣ m := (mem_filter.mp hm).2 ▸ Nat.prod_primeFactors_dvd m
      have hmeq : (m : ℝ) = (q : ℝ) * ((m / q : ℕ) : ℝ) := by
        exact_mod_cast (Nat.mul_div_cancel' hqdvd).symm
      rw [hmeq]; ring
    have heuler : ∏ p ∈ q.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) = (q : ℝ) / (q.totient : ℝ) := by
      rw [prod_div_distrib]
      have hqeq : (q : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ) := by
        rw [← Nat.cast_prod]; exact_mod_cast squarefree_eq_prod_primeFactors hsq
      have hphieq : (q.totient : ℝ) = ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
        rw [squarefree_totient_eq_prod hsq, Nat.cast_prod]
        exact prod_congr rfl fun p hp => Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le
      rw [hqeq, hphieq]
    calc
      ∑ m ∈ fib, (1 : ℝ) / (m : ℝ)
          = (1 / (q : ℝ)) * ∑ k ∈ fib.image (fun m => m / q), (1 : ℝ) / (k : ℝ) := hfib_sum
      _ ≤ (1 / (q : ℝ)) * ∑ k ∈ smooth, (1 : ℝ) / (k : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply sum_le_sum_of_subset_of_nonneg
        · intro k hk; obtain ⟨m, hm, rfl⟩ := mem_image.mp hk; exact hdiv_maps m hm
        · intro _ _ _; positivity
      _ ≤ (1 / (q : ℝ)) * ∏ p ∈ q.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left
          (sum_inv_smooth_le_euler_prod q.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp) R)
          (by positivity)
      _ = (1 / (q : ℝ)) * ((q : ℝ) / (q.totient : ℝ)) := by rw [heuler]
      _ = (1 : ℝ) / (q.totient : ℝ) := by field_simp
  -- Step 2: lower bound ∑_{m ≤ R, (m, d) = 1} 1/m using blocks of length d
  let K := R / d
  let U := (Icc 1 d).filter (fun r => r.Coprime d)
  have hU_card : U.card = d.totient := by
    by_cases hd1 : d = 1
    · subst hd1; decide
    · have hd2 : 2 ≤ d := by omega
      have hU_eq : U = (range d).filter (fun r => r.Coprime d) := by
        ext r
        simp only [U, mem_filter, mem_Icc, mem_range]
        constructor
        · rintro ⟨⟨hr1, hrd⟩, hcop⟩
          refine ⟨?_, hcop⟩
          rcases lt_or_eq_of_le hrd with hlt | rfl
          · exact hlt
          · exfalso; rw [Nat.coprime_self] at hcop; omega
        · rintro ⟨hrd, hcop⟩
          refine ⟨⟨?_, hrd.le⟩, hcop⟩
          by_contra h0
          have hr0 : r = 0 := by omega
          subst hr0; rw [Nat.coprime_zero_left] at hcop; omega
      rw [hU_eq, Nat.totient_eq_card_coprime]
      congr 1; ext r; simp [Nat.coprime_comm]
  let φ : ℕ × ℕ → ℕ := fun p => p.1 * d + p.2
  have hφ_maps : ∀ x ∈ range K ×ˢ U, φ x ∈ (Icc 1 R).filter (fun m => m.Coprime d) := by
    intro ⟨j, r⟩ hx
    have hj : j < K := mem_range.mp (mem_product.mp hx).1
    have hr1 : 1 ≤ r := (mem_Icc.mp (mem_filter.mp (mem_product.mp hx).2).1).1
    have hrd : r ≤ d := (mem_Icc.mp (mem_filter.mp (mem_product.mp hx).2).1).2
    have hrcop : r.Coprime d := (mem_filter.mp (mem_product.mp hx).2).2
    have hm1 : 1 ≤ j * d + r := by omega
    have hmR : j * d + r ≤ R := by
      have h1 : (j + 1) * d ≤ K * d := Nat.mul_le_mul_right d hj
      have h2 : K * d ≤ R := Nat.div_mul_le_self R d
      nlinarith
    have hmcop : (j * d + r).Coprime d := by
      rw [add_comm]; exact (Nat.coprime_add_mul_right_left r d j).mpr hrcop
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hm1, hmR⟩, hmcop⟩
  have hφ_inj : ∀ x₁ ∈ range K ×ˢ U, ∀ x₂ ∈ range K ×ˢ U, φ x₁ = φ x₂ → x₁ = x₂ := by
    intro ⟨j₁, r₁⟩ h₁ ⟨j₂, r₂⟩ h₂ heq
    have hr1a : 1 ≤ r₁ := (mem_Icc.mp (mem_filter.mp (mem_product.mp h₁).2).1).1
    have hr1b : r₁ ≤ d := (mem_Icc.mp (mem_filter.mp (mem_product.mp h₁).2).1).2
    have hr2a : 1 ≤ r₂ := (mem_Icc.mp (mem_filter.mp (mem_product.mp h₂).2).1).1
    have hr2b : r₂ ≤ d := (mem_Icc.mp (mem_filter.mp (mem_product.mp h₂).2).1).2
    dsimp [φ] at heq
    have hsub : j₁ * d + (r₁ - 1) = j₂ * d + (r₂ - 1) := by omega
    have hr_sub : r₁ - 1 = r₂ - 1 := by
      have h1 : (j₁ * d + (r₁ - 1)) % d = r₁ - 1 := by
        rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      have h2 : (j₂ * d + (r₂ - 1)) % d = r₂ - 1 := by
        rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      rw [← h1, hsub, h2]
    have hr_eq : r₁ = r₂ := by omega
    have hj_eq : j₁ = j₂ := by
      have : j₁ * d = j₂ * d := by omega
      exact Nat.eq_of_mul_eq_mul_right (by omega) this
    exact Prod.ext hj_eq hr_eq
  have hstep2 : ((d.totient : ℝ) / (d : ℝ)) * Real.log ((K + 1 : ℕ) : ℝ) ≤
      ∑ m ∈ (Icc 1 R).filter (fun m => m.Coprime d), (1 : ℝ) / (m : ℝ) := by
    have hblock : ((d.totient : ℝ) / (d : ℝ)) * (∑ j ∈ range K, (1 : ℝ) / ((j + 1 : ℕ) : ℝ)) ≤
        ∑ x ∈ range K ×ˢ U, (1 : ℝ) / (φ x : ℝ) := by
      have h1 : ((d.totient : ℝ) / (d : ℝ)) * (∑ j ∈ range K, (1 : ℝ) / ((j + 1 : ℕ) : ℝ)) =
          ∑ x ∈ range K ×ˢ U, (1 : ℝ) / (((x.1 + 1) * d : ℕ) : ℝ) := by
        rw [sum_product]
        simp only [sum_const, nsmul_eq_mul, hU_card, Nat.cast_mul]
        rw [mul_sum]
        refine sum_congr rfl fun j _ => ?_
        ring
      rw [h1]
      apply sum_le_sum
      intro ⟨j, r⟩ hx
      have hr1 : 1 ≤ r := (mem_Icc.mp (mem_filter.mp (mem_product.mp hx).2).1).1
      have hrd : r ≤ d := (mem_Icc.mp (mem_filter.mp (mem_product.mp hx).2).1).2
      apply one_div_le_one_div_of_le (by dsimp [φ]; positivity)
      exact_mod_cast (show j * d + r ≤ (j + 1) * d by nlinarith)
    have hsub : ∑ x ∈ range K ×ˢ U, (1 : ℝ) / (φ x : ℝ) ≤
        ∑ m ∈ (Icc 1 R).filter (fun m => m.Coprime d), (1 : ℝ) / (m : ℝ) := by
      rw [← sum_image (f := fun m : ℕ => (1 : ℝ) / (m : ℝ)) hφ_inj]
      apply sum_le_sum_of_subset_of_nonneg
      · intro m hm; obtain ⟨x, hx, rfl⟩ := mem_image.mp hm; exact hφ_maps x hx
      · intro _ _ _; positivity
    exact (mul_le_mul_of_nonneg_left (log_le_harmonic K) (by positivity)).trans (hblock.trans hsub)
  -- Step 3: (1/2) log R ≤ log (K + 1) since d^2 ≤ R < (K + 1) * d
  have hlog : (1 / 2 : ℝ) * Real.log (R : ℝ) ≤ Real.log ((K + 1 : ℕ) : ℝ) := by
    have hRlt : R < (K + 1) * d := by
      dsimp [K]
      rw [add_mul, one_mul]
      have := Nat.lt_div_mul_add (a := R) (b := d) (by omega)
      omega
    have hsq : (R : ℝ) ≤ (((K + 1 : ℕ) : ℝ)) ^ 2 := by
      have h1 : (R : ℝ) ^ 2 ≤ (((K + 1 : ℕ) : ℝ) * (d : ℝ)) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity) _ 2
        exact_mod_cast hRlt.le
      have h2 : (d : ℝ) ^ 2 ≤ (R : ℝ) := by exact_mod_cast hR
      have h3 : (((K + 1 : ℕ) : ℝ) * (d : ℝ)) ^ 2 ≤ (((K + 1 : ℕ) : ℝ)) ^ 2 * (R : ℝ) := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
      have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR1
      nlinarith
    have hlog2 := Real.log_le_log (by exact_mod_cast hR1) hsq
    rw [Real.log_pow] at hlog2
    have hlog2' : Real.log (R : ℝ) ≤ 2 * Real.log ((K + 1 : ℕ) : ℝ) := by
      simpa using hlog2
    linarith
  calc
    ((d.totient : ℝ) / (2 * (d : ℝ))) * Real.log (R : ℝ)
        = ((d.totient : ℝ) / (d : ℝ)) * ((1 / 2 : ℝ) * Real.log (R : ℝ)) := by ring
    _ ≤ ((d.totient : ℝ) / (d : ℝ)) * Real.log ((K + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ G d R := hstep2.trans hstep1

def reducedRes (q : ℕ) : Finset ℕ := (range q).filter (fun b => b.Coprime q)

def sqMu (q : ℕ) : ℝ := (-1 : ℝ) ^ q.primeFactors.card

def rootMod (d a q : ℕ) : ℕ := (-(a : ZMod q) * (d : ZMod q)⁻¹).val

def sCoeff (d a q b : ℕ) : ℂ :=
  ((sqMu q / (q.totient : ℝ) : ℝ) : ℂ) * phase ((b : ℝ) * (rootMod d a q : ℝ) / (q : ℝ))

def sieveAlpha (d a R : ℕ) (n : ℤ) : ℂ :=
  ∑ q ∈ SF d R, ∑ b ∈ reducedRes q, sCoeff d a q b * phase (-(b : ℝ) * (n : ℝ) / (q : ℝ))

def sieveBeta (d a R : ℕ) (n : ℤ) : ℝ :=
  ‖sieveAlpha d a R n‖ ^ 2 / G d R

lemma rootMod_dvd {d a q : ℕ} (hq : 1 ≤ q) (hcop : q.Coprime d) :
    (q : ℤ) ∣ (d : ℤ) * (rootMod d a q : ℤ) + (a : ℤ) := by
  let : NeZero q := ⟨by omega⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  have hval : ((rootMod d a q : ℕ) : ZMod q) = -(a : ZMod q) * (d : ZMod q)⁻¹ := by
    unfold rootMod; exact ZMod.natCast_zmod_val _
  rw [hval]
  have hmul : (d : ZMod q) * (d : ZMod q)⁻¹ = 1 := by
    exact ZMod.coe_mul_inv_eq_one d hcop.symm
  calc
    (d : ZMod q) * (-(a : ZMod q) * (d : ZMod q)⁻¹) + (a : ZMod q)
        = -(a : ZMod q) * ((d : ZMod q) * (d : ZMod q)⁻¹) + (a : ZMod q) := by ring
    _ = 0 := by rw [hmul]; ring

lemma ram_squarefree {q : ℕ} (hq : Squarefree q) (h : ℕ) :
    GoldbachMajorArc.ram q h = ∏ p ∈ q.primeFactors, ((if p ∣ h then (p : ℂ) else 0) - 1) := by
  have hmul : ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) →
      GoldbachMajorArc.ram (∏ p ∈ s, p) h = ∏ p ∈ s, ((if p ∣ h then (p : ℂ) else 0) - 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp [GoldbachMajorArc.ram_one]
    | @insert p s hps ih =>
      intro hs
      have hpp : p.Prime := hs p (mem_insert_self p s)
      have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (mem_insert_of_mem hr)
      have hcop : p.Coprime (∏ r ∈ s, r) := by
        apply Nat.Coprime.prod_right
        intro r hr
        exact (Nat.coprime_primes hpp (hs' r hr)).mpr (fun heq => hps (heq ▸ hr))
      have hprod_pos : 0 < ∏ r ∈ s, r := prod_pos fun r hr => (hs' r hr).pos
      rw [prod_insert hps, GoldbachMajorArc.ram_mul hpp.pos hprod_pos hcop,
        GoldbachMajorArc.ram_prime hpp, ih hs', prod_insert hps]
  conv_lhs => rw [squarefree_eq_prod_primeFactors hq]
  exact hmul q.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)

lemma sCoeff_sum_eq_real {d a q : ℕ} (hq : 1 ≤ q) (hsq : Squarefree q) (hcop : q.Coprime d)
    (n : ℤ) :
    ∑ b ∈ reducedRes q, sCoeff d a q b * phase (-(b : ℝ) * (n : ℝ) / (q : ℝ)) =
      ((∏ p ∈ q.primeFactors,
        (if (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) then (-1 : ℝ) else 1 / ((p : ℝ) - 1)) : ℝ) : ℂ) := by
  let n0 : ℕ := rootMod d a q
  let diff : ℤ := (n0 : ℤ) - n
  let h : ℕ := (diff % (q : ℤ)).toNat
  have hq0 : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hmod_nonneg : 0 ≤ diff % (q : ℤ) := Int.emod_nonneg diff hq0.ne'
  have hh_eq : (h : ℤ) = diff % (q : ℤ) := Int.toNat_of_nonneg hmod_nonneg
  have hdiff_sub : ∃ k : ℤ, diff - (h : ℤ) = k * (q : ℤ) := by
    refine ⟨diff / (q : ℤ), ?_⟩
    rw [hh_eq]
    have := Int.mul_ediv_add_emod diff (q : ℤ)
    linarith
  have hsum_ram : ∑ b ∈ reducedRes q,
      phase ((b : ℝ) * (n0 : ℝ) / (q : ℝ)) * phase (-(b : ℝ) * (n : ℝ) / (q : ℝ)) =
      GoldbachMajorArc.ram q h := by
    unfold GoldbachMajorArc.ram reducedRes
    refine sum_congr rfl fun b _ => ?_
    rw [← phase_add]
    obtain ⟨k, hk⟩ := hdiff_sub
    have harg : (b : ℝ) * (n0 : ℝ) / (q : ℝ) + -(b : ℝ) * (n : ℝ) / (q : ℝ) -
        (h : ℝ) * (b : ℝ) / (q : ℝ) = ((k * (b : ℤ) : ℤ) : ℝ) := by
      have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
      have hkr : (n0 : ℝ) - (n : ℝ) - (h : ℝ) = (k : ℝ) * (q : ℝ) := by
        exact_mod_cast hk
      push_cast
      field_simp
      nlinarith
    exact phase_eq_of_int_sub harg
  have hlhs : ∑ b ∈ reducedRes q, sCoeff d a q b * phase (-(b : ℝ) * (n : ℝ) / (q : ℝ)) =
      ((sqMu q / (q.totient : ℝ) : ℝ) : ℂ) * GoldbachMajorArc.ram q h := by
    rw [← hsum_ram, mul_sum]
    refine sum_congr rfl fun b _ => ?_
    unfold sCoeff; ring
  rw [hlhs, ram_squarefree hsq h]
  have hfactor : ((sqMu q / (q.totient : ℝ) : ℝ) : ℂ) =
      ∏ p ∈ q.primeFactors, (((-1 : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod]
    congr 1
    rw [sqMu, squarefree_totient_eq_prod hsq, Nat.cast_prod]
    have h1 : (-1 : ℝ) ^ q.primeFactors.card = ∏ _p ∈ q.primeFactors, (-1 : ℝ) := (prod_const _).symm
    rw [h1, ← prod_div_distrib]
    refine prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]; simp
  rw [hfactor, ← prod_mul_distrib, Complex.ofReal_prod]
  refine prod_congr rfl fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdq : p ∣ q := Nat.dvd_of_mem_primeFactors hp
  have hp_cop : p.Coprime d := hcop.coprime_dvd_left hpdq
  have hp_iff : p ∣ h ↔ (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) := by
    have h1 : p ∣ h ↔ (p : ℤ) ∣ (h : ℤ) := Int.ofNat_dvd.symm
    obtain ⟨k, hk⟩ := hdiff_sub
    have h2 : (p : ℤ) ∣ (h : ℤ) ↔ (p : ℤ) ∣ diff := by
      have hpq : (p : ℤ) ∣ k * (q : ℤ) := dvd_mul_of_dvd_right (Int.ofNat_dvd.mpr hpdq) k
      have heq : (h : ℤ) = diff - k * (q : ℤ) := by linarith
      rw [heq]
      exact ⟨fun hd => by
        have := dvd_add hd hpq; simpa using this,
        fun hd => dvd_sub hd hpq⟩
    have hroot : (p : ℤ) ∣ (d : ℤ) * (n0 : ℤ) + (a : ℤ) :=
      (Int.ofNat_dvd.mpr hpdq).trans (rootMod_dvd hq hcop)
    have h3 : (p : ℤ) ∣ diff ↔ (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) := by
      have hid : (d : ℤ) * n + (a : ℤ) = ((d : ℤ) * (n0 : ℤ) + (a : ℤ)) - (d : ℤ) * diff := by
        dsimp [diff]; ring
      rw [hid]
      constructor
      · intro hpd
        exact dvd_sub hroot (dvd_mul_of_dvd_right hpd (d : ℤ))
      · intro hpd
        have hdmul : (p : ℤ) ∣ (d : ℤ) * diff := by
          have := dvd_sub hroot hpd
          simpa using this
        have hcp : IsCoprime (p : ℤ) (d : ℤ) := Nat.isCoprime_iff_coprime.mpr hp_cop
        exact hcp.dvd_of_dvd_mul_left hdmul
    exact h1.trans (h2.trans h3)
  have hpm1 : ((p : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    linarith
  have hpm1c : ((p : ℂ) - 1) ≠ 0 := by exact_mod_cast hpm1
  by_cases hdiv : p ∣ h
  · rw [ite_eq_left hdiv, ite_eq_left (hp_iff.mp hdiv)]
    push_cast
    field_simp
  · rw [ite_eq_right hdiv, ite_eq_right (fun h' => hdiv (hp_iff.mpr h'))]
    push_cast
    field_simp; ring

lemma sieveAlpha_eq_real (d a R : ℕ) (n : ℤ) :
    sieveAlpha d a R n =
      ((∑ q ∈ SF d R, ∏ p ∈ q.primeFactors,
        (if (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) then (-1 : ℝ) else 1 / ((p : ℝ) - 1)) : ℝ) : ℂ) := by
  unfold sieveAlpha
  rw [Complex.ofReal_sum]
  refine sum_congr rfl fun q hq => ?_
  have hq1 : 1 ≤ q := (mem_Icc.mp (mem_filter.mp hq).1).1
  have hsq : Squarefree q := (mem_filter.mp hq).2.1
  have hcop : q.Coprime d := (mem_filter.mp hq).2.2
  exact sCoeff_sum_eq_real hq1 hsq hcop n

lemma sieveBeta_eq_G_of_prime {d a R : ℕ} (hR : 1 ≤ R) {n : ℤ}
    (hp : ((d : ℤ) * n + (a : ℤ)).natAbs.Prime)
    (hgt : R < ((d : ℤ) * n + (a : ℤ)).natAbs) :
    sieveBeta d a R n = G d R := by
  have hα : sieveAlpha d a R n = (G d R : ℂ) := by
    rw [sieveAlpha_eq_real]
    congr 1
    unfold G
    refine sum_congr rfl fun q hq => ?_
    have hsq : Squarefree q := (mem_filter.mp hq).2.1
    have hqR : q ≤ R := (mem_Icc.mp (mem_filter.mp hq).1).2
    have hprod : ∏ p ∈ q.primeFactors,
        (if (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) then (-1 : ℝ) else 1 / ((p : ℝ) - 1)) =
        ∏ p ∈ q.primeFactors, (1 / ((p : ℝ) - 1)) := by
      refine prod_congr rfl fun p hpm => ?_
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpm
      have hple : p ≤ R := (Nat.le_of_dvd (by have := (mem_Icc.mp (mem_filter.mp hq).1).1; omega)
        (Nat.dvd_of_mem_primeFactors hpm)).trans hqR
      have hndvd : ¬ ((p : ℤ) ∣ (d : ℤ) * n + (a : ℤ)) := by
        intro hd
        have hd' : p ∣ ((d : ℤ) * n + (a : ℤ)).natAbs := Int.ofNat_dvd_left.mp hd
        have heq := (Nat.prime_dvd_prime_iff_eq hpp hp).mp hd'
        omega
      rw [if_neg hndvd]
    rw [hprod, squarefree_totient_eq_prod hsq, Nat.cast_prod, one_div, ← prod_inv_distrib]
    refine prod_congr rfl fun p hpm => ?_
    rw [one_div, Nat.cast_sub (Nat.prime_of_mem_primeFactors hpm).one_le]
    simp
  have hGpos : 0 < G d R := lt_of_lt_of_le zero_lt_one (one_le_G hR)
  unfold sieveBeta
  rw [hα, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hGpos]
  field_simp

lemma sieveBeta_crude_bound_raw {d a R : ℕ} (hR : 1 ≤ R) {n : ℤ}
    (hne : (d : ℤ) * n + (a : ℤ) ≠ 0) :
    sieveBeta d a R n ≤ G d R * ((((d : ℤ) * n + (a : ℤ)).natAbs.divisors.card : ℝ) ^ 2) := by
  let M : ℕ := ((d : ℤ) * n + (a : ℤ)).natAbs
  have hMpos : 1 ≤ M := Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hne)
  have hGpos : 0 < G d R := lt_of_lt_of_le zero_lt_one (one_le_G hR)
  have hα_le : ‖sieveAlpha d a R n‖ ≤ (M.divisors.card : ℝ) * G d R := by
    rw [sieveAlpha_eq_real, Complex.norm_real, Real.norm_eq_abs]
    have htri : |∑ q ∈ SF d R, ∏ p ∈ q.primeFactors,
        (if (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) then (-1 : ℝ) else 1 / ((p : ℝ) - 1))| ≤
        ∑ q ∈ SF d R, (1 : ℝ) / ((q / Nat.gcd q M).totient : ℝ) := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun q hq => ?_)
      have hq1 : 1 ≤ q := (mem_Icc.mp (mem_filter.mp hq).1).1
      have hsq : Squarefree q := (mem_filter.mp hq).2.1
      let q1 := Nat.gcd q M
      let q2 := q / q1
      have hq1_dvd : q1 ∣ q := Nat.gcd_dvd_left q M
      have hmul : q1 * q2 = q := Nat.mul_div_cancel' hq1_dvd
      have hsq2 : Squarefree q2 := hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hq1_dvd)
      have hcop12 : q1.Coprime q2 := by
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hg
        obtain ⟨p, hpp, hpd⟩ := Nat.exists_prime_and_dvd hg
        have hp1 : p ∣ q1 := hpd.trans (Nat.gcd_dvd_left _ _)
        have hp2 : p ∣ q2 := hpd.trans (Nat.gcd_dvd_right _ _)
        have hppq : p * p ∣ q := by rw [← hmul]; exact mul_dvd_mul hp1 hp2
        exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hpp) hppq
      have hpf_eq : q.primeFactors = q1.primeFactors ∪ q2.primeFactors := by
        rw [← hmul, Nat.primeFactors_mul (by
          intro h; rw [h, zero_mul] at hmul; omega) (by
          intro h; rw [h, mul_zero] at hmul; omega)]
      have hdisj : Disjoint q1.primeFactors q2.primeFactors :=
        hcop12.disjoint_primeFactors
      rw [abs_prod, hpf_eq, prod_union hdisj]
      have hp1_eq : ∏ p ∈ q1.primeFactors,
          |(if (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) then (-1 : ℝ) else 1 / ((p : ℝ) - 1))| = 1 := by
        apply prod_eq_one
        intro p hp
        have hpd : p ∣ M := (Nat.dvd_of_mem_primeFactors hp).trans (Nat.gcd_dvd_right q M)
        have hpz : (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) := Int.ofNat_dvd_left.mpr hpd
        simp [hpz]
      have hp2_eq : ∏ p ∈ q2.primeFactors,
          |(if (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) then (-1 : ℝ) else 1 / ((p : ℝ) - 1))| =
          (1 : ℝ) / (q2.totient : ℝ) := by
        rw [squarefree_totient_eq_prod hsq2, Nat.cast_prod, one_div, ← prod_inv_distrib]
        refine prod_congr rfl fun p hp => ?_
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hnd : ¬ ((p : ℤ) ∣ (d : ℤ) * n + (a : ℤ)) := by
          intro hpd
          have hpM : p ∣ M := Int.ofNat_dvd_left.mp hpd
          have hpq : p ∣ q := (Nat.dvd_of_mem_primeFactors hp).trans (Nat.div_dvd_of_dvd hq1_dvd)
          have hpq1 : p ∣ q1 := Nat.dvd_gcd hpq hpM
          have hp12 : p ∣ Nat.gcd q1 q2 := Nat.dvd_gcd hpq1 (Nat.dvd_of_mem_primeFactors hp)
          rw [hcop12.gcd_eq_one] at hp12
          exact hpp.not_dvd_one hp12
        rw [if_neg hnd, abs_of_nonneg (by
          have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
          have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
          positivity), one_div, Nat.cast_sub hpp.one_le]
        simp
      rw [hp1_eq, hp2_eq, one_mul]
    let f : ℕ → ℕ × ℕ := fun q => (Nat.gcd q M, q / Nat.gcd q M)
    have hf_maps : ∀ q ∈ SF d R, f q ∈ M.divisors ×ˢ SF d R := by
      intro q hq
      have hq1 : 1 ≤ q := (mem_Icc.mp (mem_filter.mp hq).1).1
      have hqR : q ≤ R := (mem_Icc.mp (mem_filter.mp hq).1).2
      have hsq : Squarefree q := (mem_filter.mp hq).2.1
      have hcop : q.Coprime d := (mem_filter.mp hq).2.2
      have h1 : Nat.gcd q M ∈ M.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right q M, by omega⟩
      have hdvd : q / Nat.gcd q M ∣ q := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q M)
      have h2pos : 1 ≤ q / Nat.gcd q M := Nat.pos_of_dvd_of_pos hdvd (by omega)
      have h2le : q / Nat.gcd q M ≤ R := (Nat.div_le_self _ _).trans hqR
      have h2sq : Squarefree (q / Nat.gcd q M) := hsq.squarefree_of_dvd hdvd
      have h2cop : (q / Nat.gcd q M).Coprime d := hcop.coprime_dvd_left hdvd
      exact mem_product.mpr ⟨h1, mem_filter.mpr ⟨mem_Icc.mpr ⟨h2pos, h2le⟩, h2sq, h2cop⟩⟩
    have hf_inj : ∀ q₁ ∈ SF d R, ∀ q₂ ∈ SF d R, f q₁ = f q₂ → q₁ = q₂ := by
      intro q₁ _ q₂ _ heq
      have h1 : Nat.gcd q₁ M = Nat.gcd q₂ M := congrArg Prod.fst heq
      have h2 : q₁ / Nat.gcd q₁ M = q₂ / Nat.gcd q₂ M := congrArg Prod.snd heq
      calc
        q₁ = Nat.gcd q₁ M * (q₁ / Nat.gcd q₁ M) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
        _ = Nat.gcd q₂ M * (q₂ / Nat.gcd q₂ M) := by rw [h2, h1]
        _ = q₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    calc
      |∑ q ∈ SF d R, _| ≤ ∑ q ∈ SF d R, (1 : ℝ) / ((q / Nat.gcd q M).totient : ℝ) := htri
      _ = ∑ x ∈ (SF d R).image f, (1 : ℝ) / (x.2.totient : ℝ) :=
        (sum_image (f := fun x : ℕ × ℕ => (1 : ℝ) / (x.2.totient : ℝ)) hf_inj).symm
      _ ≤ ∑ x ∈ M.divisors ×ˢ SF d R, (1 : ℝ) / (x.2.totient : ℝ) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro x hx; obtain ⟨q, hq, rfl⟩ := mem_image.mp hx; exact hf_maps q hq
        · intro _ _ _; positivity
      _ = (M.divisors.card : ℝ) * G d R := by
        rw [sum_product]; dsimp only; rw [sum_const, nsmul_eq_mul]; rfl
  unfold sieveBeta
  have hsq : ‖sieveAlpha d a R n‖ ^ 2 ≤ ((M.divisors.card : ℝ) * G d R) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hα_le 2
  rw [div_le_iff₀ hGpos]
  calc
    ‖sieveAlpha d a R n‖ ^ 2 ≤ ((M.divisors.card : ℝ) * G d R) ^ 2 := hsq
    _ = G d R * (M.divisors.card : ℝ) ^ 2 * G d R := by ring

/-! #### Ramare-Ruzsa Fourier expansion of sieveBeta -/

def gamma (d r : ℕ) : ℝ :=
  ∏ p ∈ r.primeFactors, (if p ∣ d then (1 : ℝ) else ((p : ℝ) - 1) / (p : ℝ))

def indCoprime (d a r : ℕ) (n : ℤ) : ℝ :=
  if ∀ p ∈ r.primeFactors, ¬ ((p : ℤ) ∣ (d : ℤ) * n + (a : ℤ)) then 1 else 0

lemma gamma_pos (d r : ℕ) : 0 < gamma d r := by
  unfold gamma
  apply prod_pos
  intro p hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  split_ifs
  · norm_num
  · have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity

lemma gamma_one (d : ℕ) : gamma d 1 = 1 := by simp [gamma]

lemma gamma_mul_coprime (d : ℕ) {r₁ r₂ : ℕ} (h1 : r₁ ≠ 0) (h2 : r₂ ≠ 0) (hcop : r₁.Coprime r₂) :
    gamma d (r₁ * r₂) = gamma d r₁ * gamma d r₂ := by
  unfold gamma
  rw [Nat.primeFactors_mul h1 h2, prod_union hcop.disjoint_primeFactors]

lemma gamma_prime_pow (d p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    gamma d (p ^ k) = if p ∣ d then (1 : ℝ) else ((p : ℝ) - 1) / (p : ℝ) := by
  unfold gamma
  rw [Nat.primeFactors_pow p (by omega : k ≠ 0), hp.primeFactors, prod_singleton]

lemma indCoprime_one (d a : ℕ) (n : ℤ) : indCoprime d a 1 n = 1 := by simp [indCoprime]

lemma indCoprime_mul (d a : ℕ) {r₁ r₂ : ℕ} (h1 : r₁ ≠ 0) (h2 : r₂ ≠ 0) (n : ℤ) :
    indCoprime d a (r₁ * r₂) n = indCoprime d a r₁ n * indCoprime d a r₂ n := by
  unfold indCoprime
  rw [Nat.primeFactors_mul h1 h2]
  by_cases hA : ∀ p ∈ r₁.primeFactors, ¬ ((p : ℤ) ∣ (d : ℤ) * n + (a : ℤ))
  · by_cases hB : ∀ p ∈ r₂.primeFactors, ¬ ((p : ℤ) ∣ (d : ℤ) * n + (a : ℤ))
    · have hAB : ∀ p ∈ r₁.primeFactors ∪ r₂.primeFactors, ¬ ((p : ℤ) ∣ (d : ℤ) * n + (a : ℤ)) := by
        intro p hp; rcases mem_union.mp hp with hp1 | hp2
        · exact hA p hp1
        · exact hB p hp2
      rw [ite_eq_left hAB, ite_eq_left hA, ite_eq_left hB, mul_one]
    · have hAB : ¬ ∀ p ∈ r₁.primeFactors ∪ r₂.primeFactors, ¬ ((p : ℤ) ∣ (d : ℤ) * n + (a : ℤ)) := by
        intro h; exact hB fun p hp => h p (mem_union_right _ hp)
      rw [ite_eq_right hAB, ite_eq_left hA, ite_eq_right hB, mul_zero]
  · have hAB : ¬ ∀ p ∈ r₁.primeFactors ∪ r₂.primeFactors, ¬ ((p : ℤ) ∣ (d : ℤ) * n + (a : ℤ)) := by
      intro h; exact hA fun p hp => h p (mem_union_left _ hp)
    rw [ite_eq_right hAB, ite_eq_right hA, zero_mul]

lemma indCoprime_lcm (d a : ℕ) {r₁ r₂ : ℕ} (h1 : r₁ ≠ 0) (h2 : r₂ ≠ 0) (n : ℤ) :
    indCoprime d a (Nat.lcm r₁ r₂) n = indCoprime d a r₁ n * indCoprime d a r₂ n := by
  have hlcm_pf : (Nat.lcm r₁ r₂).primeFactors = r₁.primeFactors ∪ r₂.primeFactors := by
    ext p
    simp only [Nat.mem_primeFactors, mem_union, ne_eq, Nat.lcm_eq_zero_iff, not_or]
    constructor
    · rintro ⟨hp, hd, h1', h2'⟩
      rcases hp.prime.dvd_mul.mp (hd.trans (Nat.lcm_dvd_mul r₁ r₂)) with h | h
      · exact Or.inl ⟨hp, h, h1'⟩
      · exact Or.inr ⟨hp, h, h2'⟩
    · rintro (⟨hp, hd, _⟩ | ⟨hp, hd, _⟩)
      · exact ⟨hp, hd.trans (Nat.dvd_lcm_left r₁ r₂), h1, h2⟩
      · exact ⟨hp, hd.trans (Nat.dvd_lcm_right r₁ r₂), h1, h2⟩
  rw [← indCoprime_mul d a h1 h2 n]
  unfold indCoprime
  rw [hlcm_pf, Nat.primeFactors_mul h1 h2]

lemma indCoprime_prime_pow (d a p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (n : ℤ) :
    indCoprime d a (p ^ k) n = if (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) then 0 else 1 := by
  unfold indCoprime
  rw [Nat.primeFactors_pow p (by omega : k ≠ 0), hp.primeFactors]
  simp only [mem_singleton, forall_eq]
  by_cases h : (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) <;> simp [h]

lemma sieve_div_sum_eq {d a q : ℕ} (hq : 1 ≤ q) (had : a.Coprime d) (n : ℤ) :
    ∑ r ∈ q.divisors, (ArithmeticFunction.moebius (q / r) : ℝ) / gamma d r * indCoprime d a r n =
      if Squarefree q ∧ q.Coprime d then
        ∏ p ∈ q.primeFactors,
          (if (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) then (-1 : ℝ) else 1 / ((p : ℝ) - 1))
      else 0 := by
  let f : ℕ → ℝ := fun r => (1 / gamma d r) * indCoprime d a r n
  have hf_eq : ∀ r, (ArithmeticFunction.moebius (q / r) : ℝ) / gamma d r * indCoprime d a r n =
      (ArithmeticFunction.moebius (q / r) : ℝ) * f r := by
    intro r; dsimp [f]; ring
  simp_rw [hf_eq]
  have hconv : ∀ m : ℕ, 1 ≤ m →
      ∑ r ∈ m.divisors, (ArithmeticFunction.moebius (m / r) : ℝ) * f r =
      ∏ p ∈ m.primeFactors,
        (if m.factorization p = 1 ∧ ¬ (p ∣ d) then
          (if (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) then (-1 : ℝ) else 1 / ((p : ℝ) - 1))
        else 0) := by
    intro m hm
    have hmul : ∀ m₁ m₂ : ℕ, 1 ≤ m₁ → 1 ≤ m₂ → m₁.Coprime m₂ →
        (∑ r ∈ (m₁ * m₂).divisors, (ArithmeticFunction.moebius ((m₁ * m₂) / r) : ℝ) * f r) =
        (∑ r₁ ∈ m₁.divisors, (ArithmeticFunction.moebius (m₁ / r₁) : ℝ) * f r₁) *
        (∑ r₂ ∈ m₂.divisors, (ArithmeticFunction.moebius (m₂ / r₂) : ℝ) * f r₂) := by
      intro m₁ m₂ hm1 hm2 hcop
      rw [sum_divisors_mul_coprime hm1 hm2 hcop, sum_mul_sum]
      refine sum_congr rfl fun r₁ hr1 => sum_congr rfl fun r₂ hr2 => ?_
      have hr1d : r₁ ∣ m₁ := Nat.dvd_of_mem_divisors hr1
      have hr2d : r₂ ∣ m₂ := Nat.dvd_of_mem_divisors hr2
      have hr1p : r₁ ≠ 0 := (Nat.pos_of_dvd_of_pos hr1d (by omega)).ne'
      have hr2p : r₂ ≠ 0 := (Nat.pos_of_dvd_of_pos hr2d (by omega)).ne'
      have hrcop : r₁.Coprime r₂ := hcop.coprime_dvd_left hr1d |>.coprime_dvd_right hr2d
      have hdiv_eq : (m₁ * m₂) / (r₁ * r₂) = (m₁ / r₁) * (m₂ / r₂) :=
        Nat.mul_div_mul_comm hr1d hr2d
      have hqcop : (m₁ / r₁).Coprime (m₂ / r₂) :=
        hcop.coprime_dvd_left (Nat.div_dvd_of_dvd hr1d) |>.coprime_dvd_right (Nat.div_dvd_of_dvd hr2d)
      rw [hdiv_eq, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hqcop]
      push_cast
      dsimp [f]
      rw [gamma_mul_coprime d hr1p hr2p hrcop, indCoprime_mul d a hr1p hr2p n]
      ring
    have hpp : ∀ (p k : ℕ), p.Prime → 1 ≤ k →
        ∑ r ∈ (p ^ k).divisors, (ArithmeticFunction.moebius (p ^ k / r) : ℝ) * f r =
        if k = 1 ∧ ¬ (p ∣ d) then
          (if (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) then (-1 : ℝ) else 1 / ((p : ℝ) - 1))
        else 0 := by
      intro p k hp hk
      rw [Nat.divisors_prime_pow hp, sum_map]
      simp only [Function.Embedding.coeFn_mk]
      have hdiv_pow : ∀ j ∈ range (k + 1), p ^ k / p ^ j = p ^ (k - j) := by
        intro j hj
        have hjk : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
        exact Nat.pow_div hjk hp.pos
      have hsplit : ∑ j ∈ range (k + 1), (ArithmeticFunction.moebius (p ^ k / p ^ j) : ℝ) * f (p ^ j) =
          (ArithmeticFunction.moebius 1 : ℝ) * f (p ^ k) +
          (ArithmeticFunction.moebius p : ℝ) * f (p ^ (k - 1)) := by
        have hk1 : k ∈ range (k + 1) := mem_range.mpr (by omega)
        have hk2 : k - 1 ∈ range (k + 1) := mem_range.mpr (by omega)
        have hne : k - 1 ≠ k := by omega
        have hsub : ({k, k - 1} : Finset ℕ) ⊆ range (k + 1) := by
          intro x hx; simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        rw [← Finset.sum_subset hsub]
        · rw [sum_pair hne.symm, hdiv_pow k hk1, hdiv_pow (k - 1) hk2]
          have h0 : k - k = 0 := Nat.sub_self k
          have h1 : k - (k - 1) = 1 := by omega
          rw [h0, h1, pow_zero, pow_one]
        · intro j hj hnot
          rw [hdiv_pow j hj]
          have hjk : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
          have hge2 : 2 ≤ k - j := by
            simp only [mem_insert, mem_singleton, not_or] at hnot
            omega
          have hnsq : ¬ Squarefree (p ^ (k - j)) := by
            intro hsq
            have : p * p ∣ p ^ (k - j) := by
              rw [← sq]; exact pow_dvd_pow p hge2
            exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp) this
          rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]
          simp
      rw [hsplit, ArithmeticFunction.moebius_apply_one, ArithmeticFunction.moebius_apply_prime hp]
      push_cast
      by_cases hk1 : k = 1
      · subst hk1
        simp only [Nat.sub_self, pow_zero, pow_one, true_and]
        dsimp [f]
        have hg1 : gamma d p = if p ∣ d then (1 : ℝ) else ((p : ℝ) - 1) / (p : ℝ) := by
          simpa using gamma_prime_pow d p 1 hp le_rfl
        have hi1 : indCoprime d a p n = if (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) then 0 else 1 := by
          simpa using indCoprime_prime_pow d a p 1 hp le_rfl n
        rw [gamma_one, indCoprime_one, hg1, hi1]
        by_cases hpd : p ∣ d
        · rw [ite_eq_left hpd, ite_eq_right (not_not.mpr hpd)]
          have hnd : ¬ ((p : ℤ) ∣ (d : ℤ) * n + (a : ℤ)) := by
            intro hd
            have hpa : (p : ℤ) ∣ (a : ℤ) := by
              have hpdn : (p : ℤ) ∣ (d : ℤ) * n := dvd_mul_of_dvd_left (Int.ofNat_dvd.mpr hpd) n
              have := dvd_sub hd hpdn; simpa using this
            have hpa' : p ∣ a := Int.ofNat_dvd.mp hpa
            have hpg : p ∣ Nat.gcd a d := Nat.dvd_gcd hpa' hpd
            rw [had.gcd_eq_one] at hpg
            exact hp.not_dvd_one hpg
          simp [hnd]
        · rw [ite_eq_right hpd, ite_eq_left hpd]
          have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
          have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
          by_cases hdiv : (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ)
          · simp [hdiv]
          · simp only [ite_eq_right hdiv, mul_one, one_mul, neg_one_mul, div_one]
            field_simp; ring
      · have hk2 : 1 ≤ k - 1 := by omega
        rw [ite_eq_right (by tauto)]
        dsimp [f]
        rw [gamma_prime_pow d p k hp hk, gamma_prime_pow d p (k - 1) hp hk2,
          indCoprime_prime_pow d a p k hp hk n, indCoprime_prime_pow d a p (k - 1) hp hk2 n]
        ring
    -- induction on m.primeFactors
    have hm0 : m ≠ 0 := by omega
    have hgen : ∀ (s : Finset ℕ) (e : ℕ → ℕ), (∀ p ∈ s, p.Prime ∧ 1 ≤ e p) →
        ∑ r ∈ (∏ p ∈ s, p ^ e p).divisors,
          (ArithmeticFunction.moebius ((∏ p ∈ s, p ^ e p) / r) : ℝ) * f r =
        ∏ p ∈ s,
          (if e p = 1 ∧ ¬ (p ∣ d) then
            (if (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) then (-1 : ℝ) else 1 / ((p : ℝ) - 1))
          else 0) := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro e _; simp [f, gamma_one, indCoprime_one]
      | @insert p s hps ih =>
        intro e he
        have hpe := he p (mem_insert_self p s)
        have hs' : ∀ r ∈ s, r.Prime ∧ 1 ≤ e r := fun r hr => he r (mem_insert_of_mem hr)
        have hcop : (p ^ e p).Coprime (∏ r ∈ s, r ^ e r) := by
          apply Nat.Coprime.prod_right
          intro r hr
          exact ((Nat.coprime_primes hpe.1 (hs' r hr).1).mpr (fun heq => hps (heq ▸ hr))).pow _ _
        have hpos1 : 1 ≤ p ^ e p := pow_pos hpe.1.pos _
        have hpos2 : 1 ≤ ∏ r ∈ s, r ^ e r := prod_pos fun r hr => pow_pos (hs' r hr).1.pos _
        rw [prod_insert hps, hmul _ _ hpos1 hpos2 hcop, hpp p (e p) hpe.1 hpe.2, ih e hs', prod_insert hps]
    conv_lhs => rw [← prod_primeFactors_pow_eq_self hm0]
    exact hgen m.primeFactors (fun p => m.factorization p) fun p hp =>
      ⟨Nat.prime_of_mem_primeFactors hp, Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)⟩
  rw [hconv q hq]
  by_cases hcond : Squarefree q ∧ q.Coprime d
  · rw [ite_eq_left hcond]
    refine prod_congr rfl fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ q := Nat.dvd_of_mem_primeFactors hp
    have hle1 : q.factorization p = 1 := by
      have hpos : 1 ≤ q.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
      have hle : q.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one (by omega)).mp hcond.1 p
      omega
    have hnd : ¬ (p ∣ d) := by
      intro hd
      have hpg : p ∣ Nat.gcd q d := Nat.dvd_gcd hpd hd
      rw [hcond.2.gcd_eq_one] at hpg
      exact hpp.not_dvd_one hpg
    rw [ite_eq_left ⟨hle1, hnd⟩]
  · rw [ite_eq_right hcond]
    apply prod_eq_zero_iff.mpr
    by_contra hno
    push_neg at hno
    apply hcond
    constructor
    · rw [Nat.squarefree_iff_prime_squarefree]
      intro p hpp hp2
      have hpm : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, (dvd_mul_left p p).trans hp2, by omega⟩
      have hne := hno p hpm
      have h1 : q.factorization p = 1 := by
        by_contra h1'; exact hne (ite_eq_right (by tauto))
      have h2 : 2 ≤ q.factorization p := by
        have hp2' : p ^ 2 ∣ q := by rwa [sq]
        exact (Nat.Prime.pow_dvd_iff_le_factorization hpp (by omega)).mp hp2'
      omega
    · rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hg
      obtain ⟨p, hpp, hpd⟩ := Nat.exists_prime_and_dvd hg
      have hpq : p ∣ q := hpd.trans (Nat.gcd_dvd_left q d)
      have hpd' : p ∣ d := hpd.trans (Nat.gcd_dvd_right q d)
      have hpm : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpq, by omega⟩
      exact hno p hpm (ite_eq_right (by tauto))

lemma sieveAlpha_eq_mobius_sum {d a R : ℕ} (had : a.Coprime d) (n : ℤ) :
    sieveAlpha d a R n =
      ((∑ u ∈ Icc 1 R, ∑ r ∈ Icc 1 (R / u),
        (ArithmeticFunction.moebius u : ℝ) / gamma d r * indCoprime d a r n : ℝ) : ℂ) := by
  rw [sieveAlpha_eq_real]
  congr 1
  have h1 : ∑ q ∈ SF d R, ∏ p ∈ q.primeFactors,
        (if (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) then (-1 : ℝ) else 1 / ((p : ℝ) - 1)) =
      ∑ q ∈ Icc 1 R, ∑ r ∈ q.divisors,
        (ArithmeticFunction.moebius (q / r) : ℝ) / gamma d r * indCoprime d a r n := by
    rw [SF, sum_filter]
    refine sum_congr rfl fun q hq => ?_
    exact (sieve_div_sum_eq (mem_Icc.mp hq).1 had n).symm
  rw [h1]
  rw [sum_sigma', sum_sigma']
  refine Finset.sum_bij (fun x _ => ⟨x.1 / x.2, x.2⟩) ?_ ?_ ?_ ?_
  · rintro ⟨q, r⟩ hx
    have hq1 : 1 ≤ q := (mem_Icc.mp (mem_sigma.mp hx).1).1
    have hqR : q ≤ R := (mem_Icc.mp (mem_sigma.mp hx).1).2
    have hrd : r ∣ q := Nat.dvd_of_mem_divisors (mem_sigma.mp hx).2
    have hr1 : 1 ≤ r := Nat.pos_of_dvd_of_pos hrd (by omega)
    have hu1 : 1 ≤ q / r := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using Nat.le_of_dvd (by omega) hrd)
    have huR : q / r ≤ R := (Nat.div_le_self q r).trans hqR
    have hrle : r ≤ R / (q / r) := by
      apply (Nat.le_div_iff_mul_le (by omega)).mpr
      rw [mul_comm, Nat.div_mul_cancel hrd]; exact hqR
    exact mem_sigma.mpr ⟨mem_Icc.mpr ⟨hu1, huR⟩, mem_Icc.mpr ⟨hr1, hrle⟩⟩
  · rintro ⟨q₁, r₁⟩ h₁ ⟨q₂, r₂⟩ h₂ heq
    have hr1d : r₁ ∣ q₁ := Nat.dvd_of_mem_divisors (mem_sigma.mp h₁).2
    have hr2d : r₂ ∣ q₂ := Nat.dvd_of_mem_divisors (mem_sigma.mp h₂).2
    have hr_eq : r₁ = r₂ := by
      have := congrArg Sigma.snd heq; simpa using this
    have hu_eq : q₁ / r₁ = q₂ / r₂ := by
      have := congrArg Sigma.fst heq; simpa using this
    have hq_eq : q₁ = q₂ := by
      calc
        q₁ = (q₁ / r₁) * r₁ := (Nat.div_mul_cancel hr1d).symm
        _ = (q₂ / r₂) * r₂ := by rw [hu_eq, hr_eq]
        _ = q₂ := Nat.div_mul_cancel hr2d
    exact Sigma.ext hq_eq (heq_of_eq hr_eq)
  · rintro ⟨u, r⟩ hx
    have hu1 : 1 ≤ u := (mem_Icc.mp (mem_sigma.mp hx).1).1
    have hr1 : 1 ≤ r := (mem_Icc.mp (mem_sigma.mp hx).2).1
    have hrle : r ≤ R / u := (mem_Icc.mp (mem_sigma.mp hx).2).2
    have hur : u * r ≤ R := by
      have := (Nat.le_div_iff_mul_le (by omega)).mp hrle; linarith
    refine ⟨⟨u * r, r⟩, ?_, ?_⟩
    · exact mem_sigma.mpr ⟨mem_Icc.mpr ⟨by nlinarith, hur⟩,
        Nat.mem_divisors.mpr ⟨dvd_mul_left r u, by nlinarith⟩⟩
    · exact Sigma.ext (Nat.mul_div_cancel u (by omega)) (heq_of_eq rfl)
  · rintro ⟨q, r⟩ _; rfl

lemma indCoprime_fourier_eq {d a M K : ℕ} (hM : 1 ≤ M) (hMK : M ≤ K) (had : a.Coprime d) (n : ℤ) :
    (indCoprime d a M n : ℂ) =
      (gamma d M : ℂ) * ∑ q ∈ SF d K, (if q ∣ M then (1 : ℂ) else 0) *
        ∑ b ∈ reducedRes q, sCoeff d a q b * phase (-(b : ℝ) * (n : ℝ) / (q : ℝ)) := by
  let M' : ℕ := ∏ p ∈ M.primeFactors.filter (fun p => ¬ (p ∣ d)), p
  have hM'_dvd : M' ∣ M := by
    have hsub : M.primeFactors.filter (fun p => ¬ (p ∣ d)) ⊆ M.primeFactors := filter_subset _ _
    have h1 : M' ∣ ∏ p ∈ M.primeFactors, p := prod_dvd_prod_of_subset _ _ _ hsub
    exact h1.trans (Nat.prod_primeFactors_dvd M)
  have hM'_pos : 1 ≤ M' := Nat.pos_of_dvd_of_pos hM'_dvd (by omega)
  have hM'_pf : M'.primeFactors = M.primeFactors.filter (fun p => ¬ (p ∣ d)) := by
    ext p
    simp only [Nat.mem_primeFactors, mem_filter]
    constructor
    · rintro ⟨hpp, hpd, _⟩
      obtain ⟨r, hr, hpr⟩ := hpp.prime.exists_mem_finset_dvd hpd
      have hrp := Nat.prime_of_mem_primeFactors (mem_filter.mp hr).1
      have heq := (Nat.prime_dvd_prime_iff_eq hpp hrp).mp hpr
      exact heq ▸ ⟨(Nat.mem_primeFactors.mp (mem_filter.mp hr).1), (mem_filter.mp hr).2⟩
    · rintro ⟨⟨hpp, hpd, _⟩, hnd⟩
      exact ⟨hpp, dvd_prod_of_mem _ (mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpp, hpd, by omega⟩, hnd⟩), by omega⟩
  have hM'_sq : Squarefree M' := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hpp hp2
    have hpm : p ∈ M.primeFactors.filter (fun p => ¬ (p ∣ d)) := by
      have h1 : p ∈ M'.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, (dvd_mul_left p p).trans hp2, by omega⟩
      rwa [hM'_pf] at h1
    have hsplit : M' = p * ∏ r ∈ (M.primeFactors.filter (fun p => ¬ (p ∣ d))).erase p, r :=
      (Finset.mul_prod_erase _ id hpm).symm
    rw [hsplit] at hp2
    have hp_rest : p ∣ ∏ r ∈ (M.primeFactors.filter (fun p => ¬ (p ∣ d))).erase p, r :=
      (mul_dvd_mul_iff_left hpp.ne_zero).mp hp2
    obtain ⟨r, hr, hpr⟩ := hpp.prime.exists_mem_finset_dvd hp_rest
    have hrp := Nat.prime_of_mem_primeFactors (mem_filter.mp (mem_of_mem_erase hr)).1
    have heq := (Nat.prime_dvd_prime_iff_eq hpp hrp).mp hpr
    exact (mem_erase.mp hr).1 heq.symm
  have hM'_cop : M'.Coprime d := by
    apply Nat.Coprime.prod_left
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
    exact hpp.coprime_iff_not_dvd.mpr (mem_filter.mp hp).2
  have hfilt : (SF d K).filter (fun q => q ∣ M) = M'.divisors := by
    ext q
    simp only [SF, mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨hq1, _⟩, hsq, hcop⟩, hqM⟩
      refine ⟨?_, by omega⟩
      rw [squarefree_eq_prod_primeFactors hsq]
      apply prod_dvd_prod_of_subset _ _ _
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpq := Nat.dvd_of_mem_primeFactors hp
      have hpm : p ∈ M.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpq.trans hqM, by omega⟩
      have hnd : ¬ (p ∣ d) := fun hd =>
        hpp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hpq hd)
      exact mem_filter.mpr ⟨hpm, hnd⟩
    · rintro ⟨hqM', _⟩
      have hqM : q ∣ M := hqM'.trans hM'_dvd
      have hq1 : 1 ≤ q := Nat.pos_of_dvd_of_pos hqM (by omega)
      have hqK : q ≤ K := (Nat.le_of_dvd (by omega) hqM).trans hMK
      exact ⟨⟨⟨hq1, hqK⟩, hM'_sq.squarefree_of_dvd hqM', hM'_cop.coprime_dvd_left hqM'⟩, hqM⟩
  have hsum_eq : ∑ q ∈ SF d K, (if q ∣ M then (1 : ℂ) else 0) *
        ∑ b ∈ reducedRes q, sCoeff d a q b * phase (-(b : ℝ) * (n : ℝ) / (q : ℝ)) =
      ((∑ q ∈ M'.divisors, ∏ p ∈ q.primeFactors,
        (if (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) then (-1 : ℝ) else 1 / ((p : ℝ) - 1)) : ℝ) : ℂ) := by
    have hite : ∑ q ∈ SF d K, (if q ∣ M then (1 : ℂ) else 0) *
          ∑ b ∈ reducedRes q, sCoeff d a q b * phase (-(b : ℝ) * (n : ℝ) / (q : ℝ)) =
        ∑ q ∈ (SF d K).filter (fun q => q ∣ M),
          ∑ b ∈ reducedRes q, sCoeff d a q b * phase (-(b : ℝ) * (n : ℝ) / (q : ℝ)) := by
      rw [sum_filter]; refine sum_congr rfl fun q _ => by split_ifs <;> simp
    rw [hite, hfilt, Complex.ofReal_sum]
    refine sum_congr rfl fun q hq => ?_
    have hqM' : q ∣ M' := Nat.dvd_of_mem_divisors hq
    have hq1 : 1 ≤ q := Nat.pos_of_dvd_of_pos hqM' (by omega)
    exact sCoeff_sum_eq_real hq1 (hM'_sq.squarefree_of_dvd hqM') (hM'_cop.coprime_dvd_left hqM') n
  -- Evaluate the divisor sum over M'.divisors as a product over M'.primeFactors
  have hdiv_prod : ∑ q ∈ M'.divisors, ∏ p ∈ q.primeFactors,
        (if (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) then (-1 : ℝ) else 1 / ((p : ℝ) - 1)) =
      ∏ p ∈ M'.primeFactors,
        (1 + (if (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) then (-1 : ℝ) else 1 / ((p : ℝ) - 1))) := by
    have hgen : ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) →
        ∑ t ∈ s.powerset, ∏ p ∈ t,
          (if (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) then (-1 : ℝ) else 1 / ((p : ℝ) - 1)) =
        ∏ p ∈ s,
          (1 + (if (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) then (-1 : ℝ) else 1 / ((p : ℝ) - 1))) := by
      intro s _
      rw [Finset.prod_one_add]
    rw [← hgen M'.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)]
    refine Finset.sum_bij (fun q _ => q.primeFactors) ?_ ?_ ?_ ?_
    · intro q hq
      exact mem_powerset.mpr (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hq) (by omega))
    · intro q₁ h₁ q₂ h₂ heq
      have hsq1 := hM'_sq.squarefree_of_dvd (Nat.dvd_of_mem_divisors h₁)
      have hsq2 := hM'_sq.squarefree_of_dvd (Nat.dvd_of_mem_divisors h₂)
      rw [squarefree_eq_prod_primeFactors hsq1, squarefree_eq_prod_primeFactors hsq2, heq]
    · intro t ht
      have htsub : t ⊆ M'.primeFactors := mem_powerset.mp ht
      let q := ∏ p ∈ t, p
      have hqdvd : q ∣ M' := by
        rw [squarefree_eq_prod_primeFactors hM'_sq]
        exact prod_dvd_prod_of_subset _ _ _ htsub
      have hqpf : q.primeFactors = t := by
        ext p
        simp only [Nat.mem_primeFactors]
        constructor
        · rintro ⟨hpp, hpd, _⟩
          obtain ⟨r, hr, hpr⟩ := hpp.prime.exists_mem_finset_dvd hpd
          have hrp := Nat.prime_of_mem_primeFactors (htsub hr)
          have heq := (Nat.prime_dvd_prime_iff_eq hpp hrp).mp hpr
          exact heq ▸ hr
        · intro hp
          have hpp := Nat.prime_of_mem_primeFactors (htsub hp)
          have hqpos : 0 < q := prod_pos fun r hr => (Nat.prime_of_mem_primeFactors (htsub hr)).pos
          exact ⟨hpp, dvd_prod_of_mem _ hp, hqpos.ne'⟩
      exact ⟨q, Nat.mem_divisors.mpr ⟨hqdvd, by omega⟩, hqpf⟩
    · intro q _; rfl
  -- Multiply by gamma d M
  have hreal : indCoprime d a M n =
      gamma d M * ∑ q ∈ M'.divisors, ∏ p ∈ q.primeFactors,
        (if (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) then (-1 : ℝ) else 1 / ((p : ℝ) - 1)) := by
    rw [hdiv_prod]
    have hgam : gamma d M = ∏ p ∈ M'.primeFactors, (((p : ℝ) - 1) / (p : ℝ)) := by
      unfold gamma
      rw [hM'_pf, ← Finset.prod_filter_mul_prod_filter_not M.primeFactors (fun p => ¬ (p ∣ d))]
      have h1 : ∏ p ∈ M.primeFactors.filter (fun p => ¬ ¬ (p ∣ d)),
          (if p ∣ d then (1 : ℝ) else ((p : ℝ) - 1) / (p : ℝ)) = 1 :=
        prod_eq_one fun p hp => by simp [not_not.mp (mem_filter.mp hp).2]
      rw [h1, mul_one]
      exact prod_congr rfl fun p hp => if_neg (mem_filter.mp hp).2
    rw [hgam, ← prod_mul_distrib]
    have hprod_ind : ∏ p ∈ M'.primeFactors,
        (((p : ℝ) - 1) / (p : ℝ) *
          (1 + if (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) then (-1 : ℝ) else 1 / ((p : ℝ) - 1))) =
        ∏ p ∈ M'.primeFactors, (if (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ) then (0 : ℝ) else 1) := by
      refine prod_congr rfl fun p hp => ?_
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
      have hp0 : (p : ℝ) ≠ 0 := by linarith
      by_cases hdiv : (p : ℤ) ∣ (d : ℤ) * n + (a : ℤ)
      · simp [hdiv]
      · simp only [if_neg hdiv]
        field_simp; ring
    rw [hprod_ind]
    unfold indCoprime
    by_cases hA : ∀ p ∈ M.primeFactors, ¬ ((p : ℤ) ∣ (d : ℤ) * n + (a : ℤ))
    · rw [if_pos hA]
      symm; apply prod_eq_one
      intro p hp
      rw [hM'_pf] at hp
      rw [if_neg (hA p (mem_filter.mp hp).1)]
    · rw [if_neg hA]
      symm; apply prod_eq_zero_iff.mpr
      push_neg at hA
      obtain ⟨p, hpm, hpd⟩ := hA
      have hnd : ¬ (p ∣ d) := by
        intro hd
        have hpp := Nat.prime_of_mem_primeFactors hpm
        have hpa : (p : ℤ) ∣ (a : ℤ) := by
          have := dvd_sub hpd (dvd_mul_of_dvd_left (Int.ofNat_dvd.mpr hd) n)
          simpa using this
        have hpg : p ∣ Nat.gcd a d := Nat.dvd_gcd (Int.ofNat_dvd.mp hpa) hd
        rw [had.gcd_eq_one] at hpg
        exact hpp.not_dvd_one hpg
      exact ⟨p, hM'_pf ▸ mem_filter.mpr ⟨hpm, hnd⟩, by simp [hpd]⟩
  rw [hsum_eq, ← Complex.ofReal_mul, ← hreal]

lemma gamma_lcm_div_mul {d R r₁ r₂ : ℕ} (hr1 : 1 ≤ r₁) (hr2 : 1 ≤ r₂) (hr1R : r₁ ≤ R) :
    gamma d (Nat.lcm r₁ r₂) / (gamma d r₁ * gamma d r₂) =
      ∑ t ∈ SF d R, (if t ∣ Nat.gcd r₁ r₂ then (1 : ℝ) / (t.totient : ℝ) else 0) := by
  let g := Nat.gcd r₁ r₂
  let g' := ∏ p ∈ g.primeFactors.filter (fun p => ¬ (p ∣ d)), p
  have hgpos : 1 ≤ g := Nat.gcd_pos_of_pos_left r₂ (by omega)
  have hg'_dvd : g' ∣ g :=
    (prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)).trans (Nat.prod_primeFactors_dvd g)
  have hg'_pos : 1 ≤ g' := Nat.pos_of_dvd_of_pos hg'_dvd (by omega)
  have hg'_pf : g'.primeFactors = g.primeFactors.filter (fun p => ¬ (p ∣ d)) := by
    ext p
    simp only [Nat.mem_primeFactors, mem_filter]
    constructor
    · rintro ⟨hpp, hpd, _⟩
      obtain ⟨r, hr, hpr⟩ := hpp.prime.exists_mem_finset_dvd hpd
      have hrp := Nat.prime_of_mem_primeFactors (mem_filter.mp hr).1
      have heq := (Nat.prime_dvd_prime_iff_eq hpp hrp).mp hpr
      exact heq ▸ ⟨Nat.mem_primeFactors.mp (mem_filter.mp hr).1, (mem_filter.mp hr).2⟩
    · rintro ⟨⟨hpp, hpd, _⟩, hnd⟩
      exact ⟨hpp, dvd_prod_of_mem _ (mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpp, hpd, by omega⟩, hnd⟩), by omega⟩
  have hg'_sq : Squarefree g' := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hpp hp2
    have hpm : p ∈ g.primeFactors.filter (fun p => ¬ (p ∣ d)) := by
      have h1 : p ∈ g'.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, (dvd_mul_left p p).trans hp2, by omega⟩
      rwa [hg'_pf] at h1
    have hsplit : g' = p * ∏ r ∈ (g.primeFactors.filter (fun p => ¬ (p ∣ d))).erase p, r :=
      (Finset.mul_prod_erase _ id hpm).symm
    rw [hsplit] at hp2
    have hp_rest : p ∣ ∏ r ∈ (g.primeFactors.filter (fun p => ¬ (p ∣ d))).erase p, r :=
      (mul_dvd_mul_iff_left hpp.ne_zero).mp hp2
    obtain ⟨r, hr, hpr⟩ := hpp.prime.exists_mem_finset_dvd hp_rest
    have hrp := Nat.prime_of_mem_primeFactors (mem_filter.mp (mem_of_mem_erase hr)).1
    have heq := (Nat.prime_dvd_prime_iff_eq hpp hrp).mp hpr
    exact (mem_erase.mp hr).1 heq.symm
  have hg'_cop : g'.Coprime d := by
    apply Nat.Coprime.prod_left
    intro p hp
    exact (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).coprime_iff_not_dvd.mpr (mem_filter.mp hp).2
  have hlhs : gamma d (Nat.lcm r₁ r₂) / (gamma d r₁ * gamma d r₂) = 1 / gamma d g := by
    have hlcm_pf : (Nat.lcm r₁ r₂).primeFactors = r₁.primeFactors ∪ r₂.primeFactors := by
      ext p
      simp only [Nat.mem_primeFactors, mem_union, ne_eq, Nat.lcm_eq_zero_iff, not_or]
      constructor
      · rintro ⟨hp, hd, h1', h2'⟩
        rcases hp.prime.dvd_mul.mp (hd.trans (Nat.lcm_dvd_mul r₁ r₂)) with h | h
        · exact Or.inl ⟨hp, h, h1'⟩
        · exact Or.inr ⟨hp, h, h2'⟩
      · rintro (⟨hp, hd, _⟩ | ⟨hp, hd, _⟩)
        · exact ⟨hp, hd.trans (Nat.dvd_lcm_left r₁ r₂), by omega, by omega⟩
        · exact ⟨hp, hd.trans (Nat.dvd_lcm_right r₁ r₂), by omega, by omega⟩
    have hgcd_pf : g.primeFactors = r₁.primeFactors ∩ r₂.primeFactors := by
      ext p
      simp only [Nat.mem_primeFactors, mem_inter, g]
      constructor
      · rintro ⟨hp, hd, _⟩
        exact ⟨⟨hp, hd.trans (Nat.gcd_dvd_left _ _), by omega⟩,
          ⟨hp, hd.trans (Nat.gcd_dvd_right _ _), by omega⟩⟩
      · rintro ⟨⟨hp, hd1, _⟩, ⟨_, hd2, _⟩⟩
        exact ⟨hp, Nat.dvd_gcd hd1 hd2, by omega⟩
    have hprod_ui := Finset.prod_union_inter (s₁ := r₁.primeFactors) (s₂ := r₂.primeFactors)
      (f := fun p => if p ∣ d then (1 : ℝ) else ((p : ℝ) - 1) / (p : ℝ))
    have hmul_eq : gamma d (Nat.lcm r₁ r₂) * gamma d g = gamma d r₁ * gamma d r₂ := by
      unfold gamma; rw [hlcm_pf, hgcd_pf]; exact hprod_ui
    have hgp := gamma_pos d g
    have h1p := gamma_pos d r₁
    have h2p := gamma_pos d r₂
    rw [div_eq_div_iff (by positivity) hgp.ne', one_mul, hmul_eq]
  rw [hlhs]
  have hrhs_filt : (SF d R).filter (fun t => t ∣ g) = g'.divisors := by
    ext t
    simp only [SF, mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨ht1, _⟩, hsq, hcop⟩, htg⟩
      refine ⟨?_, by omega⟩
      rw [squarefree_eq_prod_primeFactors hsq]
      apply prod_dvd_prod_of_subset _ _ _
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpt := Nat.dvd_of_mem_primeFactors hp
      have hpg : p ∈ g.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpt.trans htg, by omega⟩
      have hnd : ¬ (p ∣ d) := fun hd => hpp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hpt hd)
      exact mem_filter.mpr ⟨hpg, hnd⟩
    · rintro ⟨htg', _⟩
      have htg : t ∣ g := htg'.trans hg'_dvd
      have ht1 : 1 ≤ t := Nat.pos_of_dvd_of_pos htg (by omega)
      have htR : t ≤ R := (Nat.le_of_dvd (by omega) (htg.trans (Nat.gcd_dvd_left r₁ r₂))).trans hr1R
      exact ⟨⟨⟨ht1, htR⟩, hg'_sq.squarefree_of_dvd htg', hg'_cop.coprime_dvd_left htg'⟩, htg⟩
  rw [← sum_filter, hrhs_filt]
  have h1 : ∑ t ∈ g'.divisors, (1 : ℝ) / (t.totient : ℝ) =
      ∏ p ∈ g'.primeFactors, (1 + 1 / ((p : ℝ) - 1)) := by
    rw [Finset.prod_one_add]
    refine Finset.sum_bij (fun t _ => t.primeFactors) ?_ ?_ ?_ ?_
    · intro t ht
      exact mem_powerset.mpr (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors ht) (by omega))
    · intro t₁ h₁ t₂ h₂ heq
      rw [squarefree_eq_prod_primeFactors (hg'_sq.squarefree_of_dvd (Nat.dvd_of_mem_divisors h₁)),
        squarefree_eq_prod_primeFactors (hg'_sq.squarefree_of_dvd (Nat.dvd_of_mem_divisors h₂)), heq]
    · intro s hs
      have hsub := mem_powerset.mp hs
      let t := ∏ p ∈ s, p
      have htd : t ∣ g' := by
        rw [squarefree_eq_prod_primeFactors hg'_sq]
        exact prod_dvd_prod_of_subset _ _ _ hsub
      have htpf : t.primeFactors = s := by
        ext p; simp only [Nat.mem_primeFactors]
        constructor
        · rintro ⟨hpp, hpd, _⟩
          obtain ⟨r, hr, hpr⟩ := hpp.prime.exists_mem_finset_dvd hpd
          exact (Nat.prime_dvd_prime_iff_eq hpp (Nat.prime_of_mem_primeFactors (hsub hr))).mp hpr ▸ hr
        · intro hp
          have hpp := Nat.prime_of_mem_primeFactors (hsub hp)
          have htpos : 0 < t := prod_pos fun r hr => (Nat.prime_of_mem_primeFactors (hsub hr)).pos
          exact ⟨hpp, dvd_prod_of_mem _ hp, htpos.ne'⟩
      exact ⟨t, Nat.mem_divisors.mpr ⟨htd, by omega⟩, htpf⟩
    · intro t ht
      have htsq := hg'_sq.squarefree_of_dvd (Nat.dvd_of_mem_divisors ht)
      rw [squarefree_totient_eq_prod htsq, Nat.cast_prod, one_div, ← prod_inv_distrib]
      refine prod_congr rfl fun p hp => ?_
      rw [one_div, Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]; simp
  rw [h1]
  have hgam : gamma d g = ∏ p ∈ g'.primeFactors, (((p : ℝ) - 1) / (p : ℝ)) := by
    unfold gamma
    rw [hg'_pf, ← Finset.prod_filter_mul_prod_filter_not g.primeFactors (fun p => ¬ (p ∣ d))]
    have htriv : ∏ p ∈ g.primeFactors.filter (fun p => ¬ ¬ (p ∣ d)),
        (if p ∣ d then (1 : ℝ) else ((p : ℝ) - 1) / (p : ℝ)) = 1 :=
      prod_eq_one fun p hp => by simp [not_not.mp (mem_filter.mp hp).2]
    rw [htriv, mul_one]
    exact prod_congr rfl fun p hp => if_neg (mem_filter.mp hp).2
  rw [hgam, one_div, ← prod_inv_distrib]
  refine prod_congr rfl fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  field_simp; ring

/-- The Ramare-Ruzsa bilinear divisor sum A(q', l1, l2). -/
def rrA (q' l₁ l₂ : ℕ) : ℝ :=
  ∑ r₁ ∈ l₁.divisors, ∑ r₂ ∈ l₂.divisors,
    if q' ∣ Nat.lcm r₁ r₂ then
      (ArithmeticFunction.moebius (l₁ / r₁) : ℝ) * (ArithmeticFunction.moebius (l₂ / r₂) : ℝ)
    else 0

lemma sum_moebius_div (l : ℕ) (hl : 1 ≤ l) :
    ∑ r ∈ l.divisors, (ArithmeticFunction.moebius (l / r) : ℝ) = if l = 1 then 1 else 0 := by
  have h1 : ∑ r ∈ l.divisors, (ArithmeticFunction.moebius (l / r) : ℝ) =
      ∑ d ∈ l.divisors, (ArithmeticFunction.moebius d : ℝ) := by
    refine Finset.sum_bij (fun r _ => l / r) ?_ ?_ ?_ ?_
    · intro r hr
      exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hr), by omega⟩
    · intro r₁ h₁ r₂ h₂ heq
      have hd1 := Nat.dvd_of_mem_divisors h₁
      have hd2 := Nat.dvd_of_mem_divisors h₂
      have hq1 : 0 < l / r₁ := Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd hd1) (by omega)
      have hmul : r₁ * (l / r₁) = r₂ * (l / r₁) := by
        rw [Nat.mul_div_cancel' hd1, heq, Nat.mul_div_cancel' hd2]
      exact Nat.eq_of_mul_eq_mul_right hq1 hmul
    · intro d hd
      have hdd := Nat.dvd_of_mem_divisors hd
      refine ⟨l / d, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdd, by omega⟩, ?_⟩
      exact Nat.div_div_self hdd (by omega)
    · intro _ _; rfl
  rw [h1]
  have hint : (∑ d ∈ l.divisors, ArithmeticFunction.moebius d : ℤ) = if l = 1 then 1 else 0 := by
    have h := ArithmeticFunction.moebius_mul_coe_zeta
    have hval := congrFun (congrArg DFunLike.coe h) l
    simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, ArithmeticFunction.one_apply] at hval
    have hsum : ∑ x ∈ Nat.divisorsAntidiagonal l, ArithmeticFunction.moebius x.1 * ((if x.2 = 0 then (0 : ℕ) else 1 : ℕ) : ℤ) =
        ∑ d ∈ l.divisors, ArithmeticFunction.moebius d := by
      rw [Nat.sum_divisorsAntidiagonal (f := fun x y => ArithmeticFunction.moebius x * ((if y = 0 then (0 : ℕ) else 1 : ℕ) : ℤ))]
      refine sum_congr rfl fun d hd => ?_
      have hdpos : l / d ≠ 0 := (Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd)) (by omega)).ne'
      simp [hdpos]
    rw [hsum] at hval
    exact_mod_cast hval
  rw [← Int.cast_sum, hint]
  split_ifs <;> simp

lemma rrA_mul_coprime {q₁ q₂ l₁ a₁ l₂ a₂ : ℕ}
    (hpos : 1 ≤ q₁ ∧ 1 ≤ q₂ ∧ 1 ≤ l₁ ∧ 1 ≤ a₁ ∧ 1 ≤ l₂ ∧ 1 ≤ a₂)
    (hcop : (q₁ * l₁ * l₂).Coprime (q₂ * a₁ * a₂)) :
    rrA (q₁ * q₂) (l₁ * a₁) (l₂ * a₂) = rrA q₁ l₁ l₂ * rrA q₂ a₁ a₂ := by
  have hcl : l₁.Coprime a₁ :=
    (hcop.coprime_dvd_left (dvd_trans (dvd_mul_left l₁ q₁) (dvd_mul_right _ l₂))).coprime_dvd_right
      (dvd_trans (dvd_mul_left a₁ q₂) (dvd_mul_right _ a₂))
  have hcr : l₂.Coprime a₂ :=
    (hcop.coprime_dvd_left (dvd_mul_left l₂ _)).coprime_dvd_right (dvd_mul_left a₂ _)
  have hcq1_a1 : q₁.Coprime a₁ :=
    (hcop.coprime_dvd_left (dvd_trans (dvd_mul_right q₁ l₁) (dvd_mul_right _ l₂))).coprime_dvd_right
      (dvd_trans (dvd_mul_left a₁ q₂) (dvd_mul_right _ a₂))
  have hcq1_a2 : q₁.Coprime a₂ :=
    (hcop.coprime_dvd_left (dvd_trans (dvd_mul_right q₁ l₁) (dvd_mul_right _ l₂))).coprime_dvd_right
      (dvd_mul_left a₂ _)
  have hcq2_l1 : q₂.Coprime l₁ :=
    (hcop.symm.coprime_dvd_left (dvd_trans (dvd_mul_right q₂ a₁) (dvd_mul_right _ a₂))).coprime_dvd_right
      (dvd_trans (dvd_mul_left l₁ q₁) (dvd_mul_right _ l₂))
  have hcq2_l2 : q₂.Coprime l₂ :=
    (hcop.symm.coprime_dvd_left (dvd_trans (dvd_mul_right q₂ a₁) (dvd_mul_right _ a₂))).coprime_dvd_right
      (dvd_mul_left l₂ _)
  have hcq : q₁.Coprime q₂ :=
    (hcop.coprime_dvd_left (dvd_trans (dvd_mul_right q₁ l₁) (dvd_mul_right _ l₂))).coprime_dvd_right
      (dvd_trans (dvd_mul_right q₂ a₁) (dvd_mul_right _ a₂))
  unfold rrA
  rw [sum_divisors_mul_coprime hpos.2.2.1 hpos.2.2.2.1 hcl]
  simp_rw [sum_divisors_mul_coprime hpos.2.2.2.2.1 hpos.2.2.2.2.2 hcr]
  rw [sum_mul_sum]
  simp_rw [sum_mul_sum]
  refine sum_congr rfl fun r₁ hr1 => ?_
  refine sum_congr rfl fun s₁ hs1 => ?_
  refine sum_congr rfl fun r₂ hr2 => ?_
  refine sum_congr rfl fun s₂ hs2 => ?_
  have hr1d := Nat.dvd_of_mem_divisors hr1
  have hr2d := Nat.dvd_of_mem_divisors hr2
  have hs1d := Nat.dvd_of_mem_divisors hs1
  have hs2d := Nat.dvd_of_mem_divisors hs2
  have hlcm_cop : (Nat.lcm r₁ r₂).Coprime (Nat.lcm s₁ s₂) := by
    have hr1_s1 : r₁.Coprime s₁ := hcl.coprime_dvd_left hr1d |>.coprime_dvd_right hs1d
    have hr1_s2 : r₁.Coprime s₂ :=
      (hcop.coprime_dvd_left (hr1d.trans (dvd_trans (dvd_mul_left l₁ q₁) (dvd_mul_right _ l₂)))).coprime_dvd_right
        (hs2d.trans (dvd_mul_left a₂ _))
    have hr2_s1 : r₂.Coprime s₁ :=
      (hcop.coprime_dvd_left (hr2d.trans (dvd_mul_left l₂ _))).coprime_dvd_right
        (hs1d.trans (dvd_trans (dvd_mul_left a₁ q₂) (dvd_mul_right _ a₂)))
    have hr2_s2 : r₂.Coprime s₂ := hcr.coprime_dvd_left hr2d |>.coprime_dvd_right hs2d
    exact (Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd_mul r₁ r₂)
      ((hr1_s1.mul_right hr1_s2).mul_left (hr2_s1.mul_right hr2_s2))).coprime_dvd_right (Nat.lcm_dvd_mul s₁ s₂)
  have hlcm_eq : Nat.lcm (r₁ * s₁) (r₂ * s₂) = Nat.lcm r₁ r₂ * Nat.lcm s₁ s₂ := by
    apply Nat.dvd_antisymm
    · exact Nat.lcm_dvd (mul_dvd_mul (Nat.dvd_lcm_left _ _) (Nat.dvd_lcm_left _ _))
        (mul_dvd_mul (Nat.dvd_lcm_right _ _) (Nat.dvd_lcm_right _ _))
    · exact hlcm_cop.mul_dvd_of_dvd_of_dvd
        (Nat.lcm_dvd ((dvd_mul_right r₁ s₁).trans (Nat.dvd_lcm_left _ _))
          ((dvd_mul_right r₂ s₂).trans (Nat.dvd_lcm_right _ _)))
        (Nat.lcm_dvd ((dvd_mul_left s₁ r₁).trans (Nat.dvd_lcm_left _ _))
          ((dvd_mul_left s₂ r₂).trans (Nat.dvd_lcm_right _ _)))
  have hdvd_iff : q₁ * q₂ ∣ Nat.lcm (r₁ * s₁) (r₂ * s₂) ↔
      (q₁ ∣ Nat.lcm r₁ r₂ ∧ q₂ ∣ Nat.lcm s₁ s₂) := by
    rw [hlcm_eq]
    have h1 : q₁.Coprime (Nat.lcm s₁ s₂) :=
      ((hcq1_a1.coprime_dvd_right hs1d).mul_right (hcq1_a2.coprime_dvd_right hs2d)).coprime_dvd_right
        (Nat.lcm_dvd_mul s₁ s₂)
    have h2 : q₂.Coprime (Nat.lcm r₁ r₂) :=
      ((hcq2_l1.coprime_dvd_right hr1d).mul_right (hcq2_l2.coprime_dvd_right hr2d)).coprime_dvd_right
        (Nat.lcm_dvd_mul r₁ r₂)
    constructor
    · intro h
      exact ⟨h1.dvd_of_dvd_mul_right ((dvd_mul_right q₁ q₂).trans h),
        h2.dvd_of_dvd_mul_left ((dvd_mul_left q₂ q₁).trans h)⟩
    · rintro ⟨hd1, hd2⟩
      exact mul_dvd_mul hd1 hd2
  have hmu1 : (ArithmeticFunction.moebius ((l₁ * a₁) / (r₁ * s₁)) : ℝ) =
      (ArithmeticFunction.moebius (l₁ / r₁) : ℝ) * (ArithmeticFunction.moebius (a₁ / s₁) : ℝ) := by
    rw [Nat.mul_div_mul_comm hr1d hs1d,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        (hcl.coprime_dvd_left (Nat.div_dvd_of_dvd hr1d) |>.coprime_dvd_right (Nat.div_dvd_of_dvd hs1d))]
    push_cast; rfl
  have hmu2 : (ArithmeticFunction.moebius ((l₂ * a₂) / (r₂ * s₂)) : ℝ) =
      (ArithmeticFunction.moebius (l₂ / r₂) : ℝ) * (ArithmeticFunction.moebius (a₂ / s₂) : ℝ) := by
    rw [Nat.mul_div_mul_comm hr2d hs2d,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        (hcr.coprime_dvd_left (Nat.div_dvd_of_dvd hr2d) |>.coprime_dvd_right (Nat.div_dvd_of_dvd hs2d))]
    push_cast; rfl
  by_cases hA : q₁ ∣ Nat.lcm r₁ r₂
  · by_cases hB : q₂ ∣ Nat.lcm s₁ s₂
    · rw [if_pos (hdvd_iff.mpr ⟨hA, hB⟩), if_pos hA, if_pos hB, hmu1, hmu2]; ring
    · rw [if_neg (fun h => hB (hdvd_iff.mp h).2), if_pos hA, if_neg hB, mul_zero]
  · rw [if_neg (fun h => hA (hdvd_iff.mp h).1), if_neg hA, zero_mul]

lemma rrA_eval {q' l₁ l₂ : ℕ} (hq' : Squarefree q') (hl1 : 1 ≤ l₁) (hl2 : 1 ≤ l₂) :
    rrA q' l₁ l₂ =
      if l₁ ∣ q' ∧ l₂ ∣ q' ∧ q' ∣ l₁ * l₂ then
        (-1 : ℝ) ^ (Nat.gcd l₁ l₂).primeFactors.card
      else 0 := by
  have hq'1 : 1 ≤ q' := Nat.pos_of_ne_zero hq'.ne_zero
  -- Prime-power local case
  have hlocal : ∀ (p eq e1 e2 : ℕ), p.Prime → eq ≤ 1 →
      rrA (p ^ eq) (p ^ e1) (p ^ e2) =
        if p ^ e1 ∣ p ^ eq ∧ p ^ e2 ∣ p ^ eq ∧ p ^ eq ∣ p ^ e1 * p ^ e2 then
          (-1 : ℝ) ^ (Nat.gcd (p ^ e1) (p ^ e2)).primeFactors.card
        else 0 := by
    intro p eq e1 e2 hp heq
    have hpow_dvd : ∀ a b : ℕ, p ^ a ∣ p ^ b ↔ a ≤ b := fun a b => Nat.pow_dvd_pow_iff_le_right hp.one_lt
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp heq with rfl | rfl
    · -- eq = 0, q' = 1
      unfold rrA
      simp only [pow_zero, one_dvd, ↓reduceIte, ← sum_mul, ← mul_sum]
      rw [sum_moebius_div (p ^ e1) (pow_pos hp.pos _), sum_moebius_div (p ^ e2) (pow_pos hp.pos _)]
      cases e1 with
      | zero =>
        cases e2 with
        | zero => simp
        | succ k2 =>
          have hne : p ^ (k2 + 1) ≠ 1 := (Nat.one_lt_pow (by omega) hp.one_lt).ne'
          have hnd : ¬ (p ^ (k2 + 1) ∣ 1) := fun hd => hne (Nat.dvd_one.mp hd)
          simp [hp.ne_one, hnd]
      | succ k1 =>
        have hne : p ^ (k1 + 1) ≠ 1 := (Nat.one_lt_pow (by omega) hp.one_lt).ne'
        have hnd : ¬ (p ^ (k1 + 1) ∣ 1) := fun hd => hne (Nat.dvd_one.mp hd)
        simp [hp.ne_one, hnd]
    · -- eq = 1, q' = p
      rw [pow_one]
      have hsum : rrA p (p ^ e1) (p ^ e2) =
          (∑ r₁ ∈ (p ^ e1).divisors, (ArithmeticFunction.moebius (p ^ e1 / r₁) : ℝ)) *
          (∑ r₂ ∈ (p ^ e2).divisors, (ArithmeticFunction.moebius (p ^ e2 / r₂) : ℝ)) -
          (ArithmeticFunction.moebius (p ^ e1) : ℝ) * (ArithmeticFunction.moebius (p ^ e2) : ℝ) := by
        unfold rrA
        rw [sum_mul_sum]
        have h1 : ∑ r₁ ∈ (p ^ e1).divisors, ∑ r₂ ∈ (p ^ e2).divisors,
            (if p ∣ Nat.lcm r₁ r₂ then
              (ArithmeticFunction.moebius (p ^ e1 / r₁) : ℝ) * (ArithmeticFunction.moebius (p ^ e2 / r₂) : ℝ)
            else 0) =
            ∑ r₁ ∈ (p ^ e1).divisors, ∑ r₂ ∈ (p ^ e2).divisors,
              ((ArithmeticFunction.moebius (p ^ e1 / r₁) : ℝ) * (ArithmeticFunction.moebius (p ^ e2 / r₂) : ℝ) -
              if r₁ = 1 ∧ r₂ = 1 then
                (ArithmeticFunction.moebius (p ^ e1 / r₁) : ℝ) * (ArithmeticFunction.moebius (p ^ e2 / r₂) : ℝ)
              else 0) := by
          refine sum_congr rfl fun r₁ hr1 => sum_congr rfl fun r₂ hr2 => ?_
          have hiff : p ∣ Nat.lcm r₁ r₂ ↔ ¬ (r₁ = 1 ∧ r₂ = 1) := by
            obtain ⟨i₁, hi₁, rfl⟩ := (Nat.mem_divisors_prime_pow hp e1).mp hr1
            obtain ⟨i₂, hi₂, rfl⟩ := (Nat.mem_divisors_prime_pow hp e2).mp hr2
            constructor
            · rintro h ⟨h1, h2⟩; rw [h1, h2, Nat.lcm_one_left] at h; exact hp.not_dvd_one h
            · intro h
              by_cases hi1 : i₁ = 0
              · have hi2 : 1 ≤ i₂ := by
                  by_contra h0; apply h; subst hi1; simp [show i₂ = 0 by omega]
                have hpd : p ∣ p ^ i₂ := by simpa using pow_dvd_pow p hi2
                exact hpd.trans (Nat.dvd_lcm_right _ _)
              · have hi1' : 1 ≤ i₁ := by omega
                have hpd : p ∣ p ^ i₁ := by simpa using pow_dvd_pow p hi1'
                exact hpd.trans (Nat.dvd_lcm_left _ _)
          by_cases h12 : r₁ = 1 ∧ r₂ = 1
          · rw [ite_eq_right (fun h => hiff.mp h h12), ite_eq_left h12, sub_self]
          · rw [ite_eq_left (hiff.mpr h12), ite_eq_right h12, sub_zero]
        rw [h1]
        simp_rw [sum_sub_distrib]
        congr 1
        have h1m1 : 1 ∈ (p ^ e1).divisors := Nat.one_mem_divisors.mpr (pow_pos hp.pos _).ne'
        have h1m2 : 1 ∈ (p ^ e2).divisors := Nat.one_mem_divisors.mpr (pow_pos hp.pos _).ne'
        have heval : ∑ r₁ ∈ (p ^ e1).divisors, ∑ r₂ ∈ (p ^ e2).divisors,
            (if r₁ = 1 ∧ r₂ = 1 then
              (ArithmeticFunction.moebius (p ^ e1 / r₁) : ℝ) * (ArithmeticFunction.moebius (p ^ e2 / r₂) : ℝ)
            else 0) =
            (ArithmeticFunction.moebius (p ^ e1) : ℝ) * (ArithmeticFunction.moebius (p ^ e2) : ℝ) := by
          rw [Finset.sum_eq_single 1]
          · rw [Finset.sum_eq_single 1]
            · simp
            · intro r₂ _ hr2; simp [hr2]
            · intro h; exact absurd h1m2 h
          · intro r₁ _ hr1; apply sum_eq_zero; intro r₂ _; simp [hr1]
          · intro h; exact absurd h1m1 h
        exact heval
      rw [hsum, sum_moebius_div (p ^ e1) (pow_pos hp.pos _), sum_moebius_div (p ^ e2) (pow_pos hp.pos _)]
      have hd1 : p ^ e1 ∣ p ↔ e1 ≤ 1 := by simpa using hpow_dvd e1 1
      have hd2 : p ^ e2 ∣ p ↔ e2 ≤ 1 := by simpa using hpow_dvd e2 1
      have hd3 : p ∣ p ^ e1 * p ^ e2 ↔ 1 ≤ e1 + e2 := by
        rw [← pow_add]; simpa using hpow_dvd 1 (e1 + e2)
      simp only [hd1, hd2, hd3]
      match e1, e2 with
      | 0, 0 => simp
      | 1, 0 =>
        have hpne : p ≠ 1 := hp.ne_one
        simp [hpne, ArithmeticFunction.moebius_apply_prime hp]
      | 0, 1 =>
        have hpne : p ≠ 1 := hp.ne_one
        simp [hpne, ArithmeticFunction.moebius_apply_prime hp]
      | 1, 1 =>
        have hpne : p ≠ 1 := hp.ne_one
        simp [hpne, ArithmeticFunction.moebius_apply_prime hp, hp.primeFactors]
      | e1 + 2, e2 =>
        have hnot1 : ¬ (e1 + 2 ≤ 1) := by omega
        have hnsq : ¬ Squarefree (p ^ (e1 + 2)) := fun hsq =>
          (Nat.squarefree_iff_prime_squarefree.mp hsq p hp) (by rw [← sq]; exact pow_dvd_pow p (by omega))
        simp [hp.ne_one, hnot1, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]
      | e1, e2 + 2 =>
        have hnot2 : ¬ (e2 + 2 ≤ 1) := by omega
        have hnsq : ¬ Squarefree (p ^ (e2 + 2)) := fun hsq =>
          (Nat.squarefree_iff_prime_squarefree.mp hsq p hp) (by rw [← sq]; exact pow_dvd_pow p (by omega))
        simp [hp.ne_one, hnot2, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]
  -- Globalize by induction on the set of prime factors of q' * l₁ * l₂
  have hgen : ∀ (s : Finset ℕ) (fq f1 f2 : ℕ → ℕ),
      (∀ p ∈ s, p.Prime ∧ fq p ≤ 1) →
      rrA (∏ p ∈ s, p ^ fq p) (∏ p ∈ s, p ^ f1 p) (∏ p ∈ s, p ^ f2 p) =
        if (∏ p ∈ s, p ^ f1 p) ∣ (∏ p ∈ s, p ^ fq p) ∧
           (∏ p ∈ s, p ^ f2 p) ∣ (∏ p ∈ s, p ^ fq p) ∧
           (∏ p ∈ s, p ^ fq p) ∣ (∏ p ∈ s, p ^ f1 p) * (∏ p ∈ s, p ^ f2 p) then
          (-1 : ℝ) ^ (Nat.gcd (∏ p ∈ s, p ^ f1 p) (∏ p ∈ s, p ^ f2 p)).primeFactors.card
        else 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro fq f1 f2 _
      simp [rrA]
    | @insert p s hps ih =>
      intro fq f1 f2 hs
      have hpp := (hs p (mem_insert_self p s)).1
      have hfq := (hs p (mem_insert_self p s)).2
      have hs' : ∀ r ∈ s, r.Prime ∧ fq r ≤ 1 := fun r hr => hs r (mem_insert_of_mem hr)
      let Q := ∏ r ∈ s, r ^ fq r
      let L₁ := ∏ r ∈ s, r ^ f1 r
      let L₂ := ∏ r ∈ s, r ^ f2 r
      have hQpos : 1 ≤ Q := prod_pos fun r hr => pow_pos (hs' r hr).1.pos _
      have hL1pos : 1 ≤ L₁ := prod_pos fun r hr => pow_pos (hs' r hr).1.pos _
      have hL2pos : 1 ≤ L₂ := prod_pos fun r hr => pow_pos (hs' r hr).1.pos _
      have hcop_r : ∀ k : ℕ, (p ^ k).Coprime (Q * L₁ * L₂) := by
        intro k
        have hc : ∀ (g : ℕ → ℕ), (p ^ k).Coprime (∏ r ∈ s, r ^ g r) := fun g =>
          Nat.Coprime.prod_right fun r hr =>
            ((Nat.coprime_primes hpp (hs' r hr).1).mpr (fun h => hps (h ▸ hr))).pow _ _
        exact ((hc fq).mul_right (hc f1)).mul_right (hc f2)
      have hcop_all : (p ^ fq p * p ^ f1 p * p ^ f2 p).Coprime (Q * L₁ * L₂) :=
        ((hcop_r (fq p)).mul_left (hcop_r (f1 p))).mul_left (hcop_r (f2 p))
      rw [prod_insert hps, prod_insert hps, prod_insert hps]
      rw [rrA_mul_coprime ⟨pow_pos hpp.pos _, hQpos, pow_pos hpp.pos _, hL1pos, pow_pos hpp.pos _, hL2pos⟩
        hcop_all]
      rw [hlocal p (fq p) (f1 p) (f2 p) hpp hfq, ih fq f1 f2 hs']
      -- Compare conditions and gcd prime factors
      have hc1 : ∀ a b : ℕ, (p ^ a).Coprime (∏ r ∈ s, r ^ b) := fun a b =>
        Nat.Coprime.prod_right fun r hr =>
          ((Nat.coprime_primes hpp (hs' r hr).1).mpr (fun h => hps (h ▸ hr))).pow _ _
      have hcop_pQ : (p ^ f1 p).Coprime Q :=
        Nat.Coprime.prod_right fun r hr =>
          ((Nat.coprime_primes hpp (hs' r hr).1).mpr (fun h => hps (h ▸ hr))).pow _ _
      have hcop_p2Q : (p ^ f2 p).Coprime Q :=
        Nat.Coprime.prod_right fun r hr =>
          ((Nat.coprime_primes hpp (hs' r hr).1).mpr (fun h => hps (h ▸ hr))).pow _ _
      have hcop_qL1 : (p ^ fq p).Coprime L₁ :=
        Nat.Coprime.prod_right fun r hr =>
          ((Nat.coprime_primes hpp (hs' r hr).1).mpr (fun h => hps (h ▸ hr))).pow _ _
      have hcop_qL2 : (p ^ fq p).Coprime L₂ :=
        Nat.Coprime.prod_right fun r hr =>
          ((Nat.coprime_primes hpp (hs' r hr).1).mpr (fun h => hps (h ▸ hr))).pow _ _
      have hd1_iff : p ^ f1 p * L₁ ∣ p ^ fq p * Q ↔ (p ^ f1 p ∣ p ^ fq p ∧ L₁ ∣ Q) := by
        constructor
        · intro h
          exact ⟨hcop_pQ.dvd_of_dvd_mul_right ((dvd_mul_right _ _).trans h),
            hcop_qL1.symm.dvd_of_dvd_mul_left ((dvd_mul_left _ _).trans h)⟩
        · rintro ⟨a, b⟩; exact mul_dvd_mul a b
      have hd2_iff : p ^ f2 p * L₂ ∣ p ^ fq p * Q ↔ (p ^ f2 p ∣ p ^ fq p ∧ L₂ ∣ Q) := by
        constructor
        · intro h
          exact ⟨hcop_p2Q.dvd_of_dvd_mul_right ((dvd_mul_right _ _).trans h),
            hcop_qL2.symm.dvd_of_dvd_mul_left ((dvd_mul_left _ _).trans h)⟩
        · rintro ⟨a, b⟩; exact mul_dvd_mul a b
      have hd3_iff : p ^ fq p * Q ∣ (p ^ f1 p * L₁) * (p ^ f2 p * L₂) ↔
          (p ^ fq p ∣ p ^ f1 p * p ^ f2 p ∧ Q ∣ L₁ * L₂) := by
        have hre : (p ^ f1 p * L₁) * (p ^ f2 p * L₂) = (p ^ f1 p * p ^ f2 p) * (L₁ * L₂) := by ring
        rw [hre]
        have hcqL : (p ^ fq p).Coprime (L₁ * L₂) := hcop_qL1.mul_right hcop_qL2
        have hcQp : Q.Coprime (p ^ f1 p * p ^ f2 p) := hcop_pQ.symm.mul_right hcop_p2Q.symm
        constructor
        · intro h
          exact ⟨hcqL.dvd_of_dvd_mul_right ((dvd_mul_right _ _).trans h),
            hcQp.dvd_of_dvd_mul_left ((dvd_mul_left _ _).trans h)⟩
        · rintro ⟨a, b⟩; exact mul_dvd_mul a b
      have hgcd_eq : Nat.gcd (p ^ f1 p * L₁) (p ^ f2 p * L₂) =
          Nat.gcd (p ^ f1 p) (p ^ f2 p) * Nat.gcd L₁ L₂ := by
        have hc12 : (p ^ f1 p).Coprime L₂ :=
          Nat.Coprime.prod_right fun r hr =>
            ((Nat.coprime_primes hpp (hs' r hr).1).mpr (fun h => hps (h ▸ hr))).pow _ _
        have hc21 : L₁.Coprime (p ^ f2 p) :=
          (Nat.Coprime.prod_right fun r hr =>
            ((Nat.coprime_primes hpp (hs' r hr).1).mpr (fun h => hps (h ▸ hr))).pow _ _).symm
        calc
          Nat.gcd (p ^ f1 p * L₁) (p ^ f2 p * L₂)
              = Nat.gcd (p ^ f1 p) (p ^ f2 p * L₂) * Nat.gcd L₁ (p ^ f2 p * L₂) := by
                have hcopL : (p ^ f1 p).Coprime L₁ :=
                  Nat.Coprime.prod_right fun r hr =>
                    ((Nat.coprime_primes hpp (hs' r hr).1).mpr (fun h => hps (h ▸ hr))).pow _ _
                rw [Nat.gcd_comm, hcopL.gcd_mul, Nat.gcd_comm, Nat.gcd_comm (p ^ f2 p * L₂) L₁]
          _ = Nat.gcd (p ^ f1 p) (p ^ f2 p) * Nat.gcd L₁ L₂ := by
                rw [hc12.symm.gcd_mul_right_cancel_right, Nat.gcd_comm L₁, hc21.symm.gcd_mul_left_cancel,
                  Nat.gcd_comm L₂]
      have hgcd_cop : (Nat.gcd (p ^ f1 p) (p ^ f2 p)).Coprime (Nat.gcd L₁ L₂) := by
        have h1 : (p ^ f1 p).Coprime L₁ :=
          Nat.Coprime.prod_right fun r hr =>
            ((Nat.coprime_primes hpp (hs' r hr).1).mpr (fun h => hps (h ▸ hr))).pow _ _
        exact (h1.coprime_dvd_left (Nat.gcd_dvd_left _ _)).coprime_dvd_right (Nat.gcd_dvd_left _ _)
      have hpf_card : (Nat.gcd (p ^ f1 p * L₁) (p ^ f2 p * L₂)).primeFactors.card =
          (Nat.gcd (p ^ f1 p) (p ^ f2 p)).primeFactors.card + (Nat.gcd L₁ L₂).primeFactors.card := by
        rw [hgcd_eq, Nat.primeFactors_mul (Nat.gcd_pos_of_pos_left _ (pow_pos hpp.pos _)).ne'
          (Nat.gcd_pos_of_pos_left _ (by omega)).ne',
          card_union_of_disjoint hgcd_cop.disjoint_primeFactors]
      by_cases hA : p ^ f1 p ∣ p ^ fq p ∧ p ^ f2 p ∣ p ^ fq p ∧ p ^ fq p ∣ p ^ f1 p * p ^ f2 p
      · by_cases hB : L₁ ∣ Q ∧ L₂ ∣ Q ∧ Q ∣ L₁ * L₂
        · rw [ite_eq_left hA, ite_eq_left hB, ite_eq_left ⟨hd1_iff.mpr ⟨hA.1, hB.1⟩, hd2_iff.mpr ⟨hA.2.1, hB.2.1⟩,
            hd3_iff.mpr ⟨hA.2.2, hB.2.2⟩⟩, hpf_card, pow_add]
        · have hnot : ¬ (p ^ f1 p * L₁ ∣ p ^ fq p * Q ∧ p ^ f2 p * L₂ ∣ p ^ fq p * Q ∧
              p ^ fq p * Q ∣ (p ^ f1 p * L₁) * (p ^ f2 p * L₂)) := by
            rintro ⟨c1, c2, c3⟩
            exact hB ⟨(hd1_iff.mp c1).2, (hd2_iff.mp c2).2, (hd3_iff.mp c3).2⟩
          rw [ite_eq_left hA, ite_eq_right hB, ite_eq_right hnot, mul_zero]
      · have hnot : ¬ (p ^ f1 p * L₁ ∣ p ^ fq p * Q ∧ p ^ f2 p * L₂ ∣ p ^ fq p * Q ∧
            p ^ fq p * Q ∣ (p ^ f1 p * L₁) * (p ^ f2 p * L₂)) := by
          rintro ⟨c1, c2, c3⟩
          exact hA ⟨(hd1_iff.mp c1).1, (hd2_iff.mp c2).1, (hd3_iff.mp c3).1⟩
        rw [ite_eq_right hA, ite_eq_right hnot, zero_mul]
  let s := q'.primeFactors ∪ l₁.primeFactors ∪ l₂.primeFactors
  have hprod_eq : ∀ m : ℕ, 1 ≤ m → m.primeFactors ⊆ s →
      ∏ p ∈ s, p ^ (m.factorization p) = m := by
    intro m hm hsub
    rw [← Finset.prod_subset hsub]
    · exact prod_primeFactors_pow_eq_self (by omega)
    · intro p _ hnot
      have : m.factorization p = 0 := Finsupp.notMem_support_iff.mp hnot
      rw [this, pow_zero]
  have hq'_eq : ∏ p ∈ s, p ^ (q'.factorization p) = q' :=
    hprod_eq q' hq'1 (subset_union_left.trans subset_union_left)
  have hl1_eq : ∏ p ∈ s, p ^ (l₁.factorization p) = l₁ :=
    hprod_eq l₁ hl1 (subset_union_right.trans subset_union_left)
  have hl2_eq : ∏ p ∈ s, p ^ (l₂.factorization p) = l₂ :=
    hprod_eq l₂ hl2 subset_union_right
  have hs_prop : ∀ p ∈ s, p.Prime ∧ q'.factorization p ≤ 1 := by
    intro p hp
    have hpp : p.Prime := by
      rcases mem_union.mp hp with hp1 | hp2
      · rcases mem_union.mp hp1 with hpq | hpl
        · exact Nat.prime_of_mem_primeFactors hpq
        · exact Nat.prime_of_mem_primeFactors hpl
      · exact Nat.prime_of_mem_primeFactors hp2
    exact ⟨hpp, (Nat.squarefree_iff_factorization_le_one hq'.ne_zero).mp hq' p⟩
  have hres := hgen s (fun p => q'.factorization p) (fun p => l₁.factorization p)
    (fun p => l₂.factorization p) hs_prop
  rwa [hq'_eq, hl1_eq, hl2_eq] at hres

lemma card_rrA_pairs_le (q' : ℕ) (hq' : Squarefree q') :
    ((q'.divisors ×ˢ q'.divisors).filter (fun x => q' ∣ x.1 * x.2)).card ≤
      3 ^ q'.primeFactors.card := by
  let S := (q'.divisors ×ˢ q'.divisors).filter (fun x => q' ∣ x.1 * x.2)
  let f : ℕ × ℕ → (q'.primeFactors → Fin 3) := fun ⟨l₁, l₂⟩ p =>
    if p.1 ∣ l₁ then (if p.1 ∣ l₂ then 2 else 0) else 1
  have hinj : Set.InjOn f S := by
    intro ⟨a₁, b₁⟩ h1 ⟨a₂, b₂⟩ h2 heq
    have ha1d : a₁ ∣ q' := Nat.dvd_of_mem_divisors (mem_product.mp (mem_filter.mp h1).1).1
    have hb1d : b₁ ∣ q' := Nat.dvd_of_mem_divisors (mem_product.mp (mem_filter.mp h1).1).2
    have hab1 : q' ∣ a₁ * b₁ := (mem_filter.mp h1).2
    have ha2d : a₂ ∣ q' := Nat.dvd_of_mem_divisors (mem_product.mp (mem_filter.mp h2).1).1
    have hb2d : b₂ ∣ q' := Nat.dvd_of_mem_divisors (mem_product.mp (mem_filter.mp h2).1).2
    have hab2 : q' ∣ a₂ * b₂ := (mem_filter.mp h2).2
    have hpf_a : a₁.primeFactors = a₂.primeFactors := by
      ext p; simp only [Nat.mem_primeFactors]
      have hq'0 := hq'.ne_zero
      constructor
      · rintro ⟨hpp, hpa, _⟩
        have hpq : p ∈ q'.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpa.trans ha1d, hq'0⟩
        have hval := congrFun heq ⟨p, hpq⟩
        dsimp [f] at hval
        rw [if_pos hpa] at hval
        by_contra hnot
        have hnd2 : ¬ (p ∣ a₂) := fun h => hnot ⟨hpp, h, (Nat.pos_of_dvd_of_pos ha2d (Nat.pos_of_ne_zero hq'0)).ne'⟩
        rw [if_neg hnd2] at hval
        split_ifs at hval <;> omega
      · rintro ⟨hpp, hpa, _⟩
        have hpq : p ∈ q'.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpa.trans ha2d, hq'0⟩
        have hval := congrFun heq ⟨p, hpq⟩
        dsimp [f] at hval
        rw [if_pos hpa] at hval
        by_contra hnot
        have hnd1 : ¬ (p ∣ a₁) := fun h => hnot ⟨hpp, h, (Nat.pos_of_dvd_of_pos ha1d (Nat.pos_of_ne_zero hq'0)).ne'⟩
        rw [if_neg hnd1] at hval
        split_ifs at hval <;> omega
    have hpf_b : b₁.primeFactors = b₂.primeFactors := by
      ext p; simp only [Nat.mem_primeFactors]
      have hq'0 := hq'.ne_zero
      constructor
      · rintro ⟨hpp, hpb, _⟩
        have hpq : p ∈ q'.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpb.trans hb1d, hq'0⟩
        have hval := congrFun heq ⟨p, hpq⟩
        dsimp [f] at hval
        by_contra hnot
        have hnd2 : ¬ (p ∣ b₂) := fun h => hnot ⟨hpp, h, (Nat.pos_of_dvd_of_pos hb2d (Nat.pos_of_ne_zero hq'0)).ne'⟩
        have hpa2 : p ∣ a₂ := by
          rcases hpp.prime.dvd_mul.mp ((Nat.dvd_of_mem_primeFactors hpq).trans hab2) with h | h
          · exact h
          · exact absurd h hnd2
        rw [if_pos hpa2, if_neg hnd2] at hval
        rw [if_pos hpb] at hval
        split_ifs at hval <;> omega
      · rintro ⟨hpp, hpb, _⟩
        have hpq : p ∈ q'.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpb.trans hb2d, hq'0⟩
        have hval := congrFun heq ⟨p, hpq⟩
        dsimp [f] at hval
        by_contra hnot
        have hnd1 : ¬ (p ∣ b₁) := fun h => hnot ⟨hpp, h, (Nat.pos_of_dvd_of_pos hb1d (Nat.pos_of_ne_zero hq'0)).ne'⟩
        have hpa1 : p ∣ a₁ := by
          rcases hpp.prime.dvd_mul.mp ((Nat.dvd_of_mem_primeFactors hpq).trans hab1) with h | h
          · exact h
          · exact absurd h hnd1
        rw [if_pos hpa1, if_neg hnd1] at hval
        rw [if_pos hpb] at hval
        split_ifs at hval <;> omega
    have ha : a₁ = a₂ := by
      rw [squarefree_eq_prod_primeFactors (hq'.squarefree_of_dvd ha1d),
        squarefree_eq_prod_primeFactors (hq'.squarefree_of_dvd ha2d), hpf_a]
    have hb : b₁ = b₂ := by
      rw [squarefree_eq_prod_primeFactors (hq'.squarefree_of_dvd hb1d),
        squarefree_eq_prod_primeFactors (hq'.squarefree_of_dvd hb2d), hpf_b]
    exact Prod.ext ha hb
  calc
    S.card = (S.image f).card := (card_image_of_injOn hinj).symm
    _ ≤ Fintype.card (q'.primeFactors → Fin 3) := card_le_univ _
    _ = 3 ^ q'.primeFactors.card := by simp

/-- Fourier expansion of sieveBeta with explicit weight decay and w(1, 0) = 1. -/
theorem sieveBeta_fourier_expansion {d a R : ℕ} (hR : 1 ≤ R) (had : a.Coprime d) :
    ∃ w : ℕ → ℕ → ℂ,
      w 1 0 = 1 ∧
      (∀ q ∈ SF d (R ^ 2), ∀ b ∈ reducedRes q,
        ‖w q b‖ ≤ (3 : ℝ) ^ q.primeFactors.card / (q.totient : ℝ)) ∧
      (∀ n : ℤ, (sieveBeta d a R n : ℂ) =
        ∑ q ∈ SF d (R ^ 2), ∑ b ∈ reducedRes q, w q b * phase (-(b : ℝ) * (n : ℝ) / (q : ℝ))) := by
  let P := (Icc 1 R).sigma (fun u => Icc 1 (R / u))
  let Sqt : ℕ → ℕ → ℝ := fun q t =>
    ∑ l₁ ∈ Icc 1 (R / t), ∑ l₂ ∈ Icc 1 (R / t), rrA (q / Nat.gcd q t) l₁ l₂
  let w : ℕ → ℕ → ℂ := fun q b =>
    sCoeff d a q b * (((1 / G d R) * ∑ t ∈ SF d R, (1 / (t.totient : ℝ)) * Sqt q t : ℝ) : ℂ)
  have hGpos : 0 < G d R := lt_of_lt_of_le zero_lt_one (one_le_G hR)
  refine ⟨w, ?_, ?_, ?_⟩
  · -- w 1 0 = 1
    dsimp [w]
    have hs10 : sCoeff d a 1 0 = 1 := by
      unfold sCoeff sqMu; simp [phase_zero]
    have hS1 : ∀ t ∈ SF d R, Sqt 1 t = 1 := by
      intro t ht
      have ht1 : 1 ≤ t := (mem_Icc.mp (mem_filter.mp ht).1).1
      have htR : t ≤ R := (mem_Icc.mp (mem_filter.mp ht).1).2
      have hRt : 1 ≤ R / t := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
      dsimp [Sqt]
      simp only [Nat.gcd_one_left, Nat.div_one]
      have h1m : 1 ∈ Icc 1 (R / t) := mem_Icc.mpr ⟨le_rfl, hRt⟩
      rw [Finset.sum_eq_single 1]
      · rw [Finset.sum_eq_single 1]
        · rw [rrA_eval squarefree_one le_rfl le_rfl]; simp
        · intro l₂ hl₂ hne
          rw [rrA_eval squarefree_one le_rfl (mem_Icc.mp hl₂).1]
          have : ¬ (l₂ ∣ 1) := fun hd => hne (Nat.dvd_one.mp hd)
          simp [this]
        · intro h; exact absurd h1m h
      · intro l₁ hl₁ hne
        apply sum_eq_zero; intro l₂ hl₂
        rw [rrA_eval squarefree_one (mem_Icc.mp hl₁).1 (mem_Icc.mp hl₂).1]
        have : ¬ (l₁ ∣ 1) := fun hd => hne (Nat.dvd_one.mp hd)
        simp [this]
      · intro h; exact absurd h1m h
    rw [hs10, one_mul]
    have hsum : ∑ t ∈ SF d R, (1 / (t.totient : ℝ)) * Sqt 1 t = G d R := by
      unfold G
      refine sum_congr rfl fun t ht => by rw [hS1 t ht, mul_one]
    rw [hsum, one_div, inv_mul_cancel₀ hGpos.ne', Complex.ofReal_one]
  · -- ‖w q b‖ ≤ 3^ω(q) / φ(q)
    intro q hq b _
    have hq1 : 1 ≤ q := (mem_Icc.mp (mem_filter.mp hq).1).1
    have hsq : Squarefree q := (mem_filter.mp hq).2.1
    dsimp [w]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hs_norm : ‖sCoeff d a q b‖ = (1 : ℝ) / (q.totient : ℝ) := by
      unfold sCoeff sqMu
      rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow,
        abs_neg, abs_one, one_pow, abs_of_pos (by exact_mod_cast Nat.totient_pos.mpr hq1)]
    rw [hs_norm]
    have hSqt_le : ∀ t ∈ SF d R, |Sqt q t| ≤ (3 : ℝ) ^ q.primeFactors.card := by
      intro t ht
      let q' := q / Nat.gcd q t
      have hq'd : q' ∣ q := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q t)
      have hq'sq : Squarefree q' := hsq.squarefree_of_dvd hq'd
      have hq'pf : q'.primeFactors.card ≤ q.primeFactors.card :=
        card_le_card (Nat.primeFactors_mono hq'd (by omega))
      dsimp [Sqt]
      have htri : |∑ l₁ ∈ Icc 1 (R / t), ∑ l₂ ∈ Icc 1 (R / t), rrA q' l₁ l₂| ≤
          ∑ x ∈ Icc 1 (R / t) ×ˢ Icc 1 (R / t), |rrA q' x.1 x.2| := by
        rw [← sum_product']; exact abs_sum_le_sum_abs _ _
      have hpair : ∑ x ∈ Icc 1 (R / t) ×ˢ Icc 1 (R / t), |rrA q' x.1 x.2| ≤
          (((q'.divisors ×ˢ q'.divisors).filter (fun x => q' ∣ x.1 * x.2)).card : ℝ) := by
        let Good := (q'.divisors ×ˢ q'.divisors).filter (fun x => q' ∣ x.1 * x.2)
        have hstep : ∑ x ∈ Icc 1 (R / t) ×ˢ Icc 1 (R / t), |rrA q' x.1 x.2| =
            ∑ x ∈ (Icc 1 (R / t) ×ˢ Icc 1 (R / t)).filter (fun x => x ∈ Good), (1 : ℝ) := by
          rw [sum_filter]
          refine sum_congr rfl fun ⟨l₁, l₂⟩ hx => ?_
          have hl1 := (mem_Icc.mp (mem_product.mp hx).1).1
          have hl2 := (mem_Icc.mp (mem_product.mp hx).2).1
          rw [rrA_eval hq'sq hl1 hl2]
          have hmem_iff : (l₁, l₂) ∈ Good ↔ (l₁ ∣ q' ∧ l₂ ∣ q' ∧ q' ∣ l₁ * l₂) := by
            have hq'0 : q' ≠ 0 := hq'sq.ne_zero
            simp only [Good, mem_filter, mem_product, Nat.mem_divisors]
            tauto
          by_cases hc : l₁ ∣ q' ∧ l₂ ∣ q' ∧ q' ∣ l₁ * l₂
          · rw [ite_eq_left hc, ite_eq_left (hmem_iff.mpr hc), abs_pow, abs_neg, abs_one, one_pow]
          · rw [ite_eq_right hc, ite_eq_right (fun h => hc (hmem_iff.mp h)), abs_zero]
        rw [hstep, sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast card_le_card (fun x hx => (mem_filter.mp hx).2)
      calc
        |Sqt q t| ≤ (((q'.divisors ×ˢ q'.divisors).filter (fun x => q' ∣ x.1 * x.2)).card : ℝ) :=
          htri.trans hpair
        _ ≤ (3 : ℝ) ^ q'.primeFactors.card := by exact_mod_cast card_rrA_pairs_le q' hq'sq
        _ ≤ (3 : ℝ) ^ q.primeFactors.card := pow_le_pow_right₀ (by norm_num) hq'pf
    have havg : |(1 / G d R) * ∑ t ∈ SF d R, (1 / (t.totient : ℝ)) * Sqt q t| ≤
        (3 : ℝ) ^ q.primeFactors.card := by
      rw [abs_mul, abs_of_pos (div_pos one_pos hGpos)]
      have h1 : |∑ t ∈ SF d R, (1 / (t.totient : ℝ)) * Sqt q t| ≤
          G d R * (3 : ℝ) ^ q.primeFactors.card := by
        calc
          |∑ t ∈ SF d R, (1 / (t.totient : ℝ)) * Sqt q t|
              ≤ ∑ t ∈ SF d R, |(1 / (t.totient : ℝ)) * Sqt q t| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ t ∈ SF d R, (1 / (t.totient : ℝ)) * (3 : ℝ) ^ q.primeFactors.card := by
            refine sum_le_sum fun t ht => ?_
            rw [abs_mul, abs_of_nonneg (by positivity)]
            exact mul_le_mul_of_nonneg_left (hSqt_le t ht) (by positivity)
          _ = G d R * (3 : ℝ) ^ q.primeFactors.card := by rw [← sum_mul]; rfl
      calc
        (1 / G d R) * |∑ t ∈ SF d R, (1 / (t.totient : ℝ)) * Sqt q t|
            ≤ (1 / G d R) * (G d R * (3 : ℝ) ^ q.primeFactors.card) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (3 : ℝ) ^ q.primeFactors.card := by field_simp
    calc
      (1 / (q.totient : ℝ)) * |(1 / G d R) * ∑ t ∈ SF d R, (1 / (t.totient : ℝ)) * Sqt q t|
          ≤ (1 / (q.totient : ℝ)) * (3 : ℝ) ^ q.primeFactors.card :=
        mul_le_mul_of_nonneg_left havg (by positivity)
      _ = (3 : ℝ) ^ q.primeFactors.card / (q.totient : ℝ) := by ring
  · -- Fourier expansion identity
    intro n
    have hα := sieveAlpha_eq_mobius_sum (d := d) (a := a) (R := R) had n
    have hβ : (sieveBeta d a R n : ℂ) =
        ((1 / G d R : ℝ) : ℂ) *
          (∑ x ∈ P, ((ArithmeticFunction.moebius x.1 : ℝ) / gamma d x.2 * indCoprime d a x.2 n : ℂ)) *
          (∑ y ∈ P, ((ArithmeticFunction.moebius y.1 : ℝ) / gamma d y.2 * indCoprime d a y.2 n : ℂ)) := by
      unfold sieveBeta
      rw [hα, Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.ofReal_div, Complex.ofReal_pow,
        sq, Complex.ofReal_sum]
      simp_rw [Complex.ofReal_sum]
      rw [sum_sigma']
      push_cast; ring
    rw [hβ, mul_assoc, sum_mul_sum]
    have hterm_id : ∀ x ∈ P, ∀ y ∈ P,
        ((ArithmeticFunction.moebius x.1 : ℝ) / gamma d x.2 * indCoprime d a x.2 n : ℂ) *
        ((ArithmeticFunction.moebius y.1 : ℝ) / gamma d y.2 * indCoprime d a y.2 n : ℂ) =
        ∑ q ∈ SF d (R ^ 2), ∑ t ∈ SF d R,
          (((if q ∣ Nat.lcm x.2 y.2 ∧ t ∣ x.2 ∧ t ∣ y.2 then
              (1 / (t.totient : ℝ)) * (ArithmeticFunction.moebius x.1 : ℝ) *
                (ArithmeticFunction.moebius y.1 : ℝ)
            else 0) : ℝ) : ℂ) *
          ∑ b ∈ reducedRes q, sCoeff d a q b * phase (-(b : ℝ) * (n : ℝ) / (q : ℝ)) := by
      intro ⟨u₁, r₁⟩ hx ⟨u₂, r₂⟩ hy
      have hu1 : 1 ≤ u₁ := (mem_Icc.mp (mem_sigma.mp hx).1).1
      have hr1 : 1 ≤ r₁ := (mem_Icc.mp (mem_sigma.mp hx).2).1
      have hr1le : r₁ ≤ R / u₁ := (mem_Icc.mp (mem_sigma.mp hx).2).2
      have hr1R : r₁ ≤ R := hr1le.trans (Nat.div_le_self R u₁)
      have hu2 : 1 ≤ u₂ := (mem_Icc.mp (mem_sigma.mp hy).1).1
      have hr2 : 1 ≤ r₂ := (mem_Icc.mp (mem_sigma.mp hy).2).1
      have hr2le : r₂ ≤ R / u₂ := (mem_Icc.mp (mem_sigma.mp hy).2).2
      have hr2R : r₂ ≤ R := hr2le.trans (Nat.div_le_self R u₂)
      have hlcm_pos : 1 ≤ Nat.lcm r₁ r₂ :=
        Nat.pos_of_ne_zero (mt Nat.lcm_eq_zero_iff.mp (by omega))
      have hlcm_le : Nat.lcm r₁ r₂ ≤ R ^ 2 := by
        calc
          Nat.lcm r₁ r₂ ≤ r₁ * r₂ := Nat.le_of_dvd (by nlinarith) (Nat.lcm_dvd_mul r₁ r₂)
          _ ≤ R * R := Nat.mul_le_mul hr1R hr2R
          _ = R ^ 2 := (sq R).symm
      have hind : ((indCoprime d a r₁ n : ℝ) : ℂ) * ((indCoprime d a r₂ n : ℝ) : ℂ) =
          (indCoprime d a (Nat.lcm r₁ r₂) n : ℂ) := by
        rw [← Complex.ofReal_mul, ← indCoprime_lcm d a (by omega) (by omega) n]
      calc
        ((ArithmeticFunction.moebius u₁ : ℝ) / gamma d r₁ * indCoprime d a r₁ n : ℂ) *
            ((ArithmeticFunction.moebius u₂ : ℝ) / gamma d r₂ * indCoprime d a r₂ n : ℂ)
            = (((ArithmeticFunction.moebius u₁ : ℝ) * (ArithmeticFunction.moebius u₂ : ℝ) /
                (gamma d r₁ * gamma d r₂) : ℝ) : ℂ) * (indCoprime d a (Nat.lcm r₁ r₂) n : ℂ) := by
              rw [← hind]; push_cast; ring
        _ = (((ArithmeticFunction.moebius u₁ : ℝ) * (ArithmeticFunction.moebius u₂ : ℝ) *
              (gamma d (Nat.lcm r₁ r₂) / (gamma d r₁ * gamma d r₂)) : ℝ) : ℂ) *
            ∑ q ∈ SF d (R ^ 2), (if q ∣ Nat.lcm r₁ r₂ then (1 : ℂ) else 0) *
              ∑ b ∈ reducedRes q, sCoeff d a q b * phase (-(b : ℝ) * (n : ℝ) / (q : ℝ)) := by
              rw [indCoprime_fourier_eq hlcm_pos hlcm_le had n]; push_cast; ring
        _ = ∑ q ∈ SF d (R ^ 2), ∑ t ∈ SF d R,
            (((if q ∣ Nat.lcm r₁ r₂ ∧ t ∣ r₁ ∧ t ∣ r₂ then
                (1 / (t.totient : ℝ)) * (ArithmeticFunction.moebius u₁ : ℝ) *
                  (ArithmeticFunction.moebius u₂ : ℝ)
              else 0) : ℝ) : ℂ) *
            ∑ b ∈ reducedRes q, sCoeff d a q b * phase (-(b : ℝ) * (n : ℝ) / (q : ℝ)) := by
              rw [gamma_lcm_div_mul hr1 hr2 hr1R, mul_sum]
              refine sum_congr rfl fun q _ => ?_
              rw [mul_sum, Complex.ofReal_sum, sum_mul]
              refine sum_congr rfl fun t _ => ?_
              have hg_iff : t ∣ Nat.gcd r₁ r₂ ↔ t ∣ r₁ ∧ t ∣ r₂ := Nat.dvd_gcd_iff
              by_cases hq : q ∣ Nat.lcm r₁ r₂
              · by_cases ht : t ∣ Nat.gcd r₁ r₂
                · rw [ite_eq_left hq, ite_eq_left ht, ite_eq_left ⟨hq, hg_iff.mp ht⟩]; push_cast; ring
                · rw [ite_eq_left hq, ite_eq_right ht, ite_eq_right (fun h => ht (hg_iff.mpr h.2))]; simp
              · simp [hq]
    -- Combine double sum over P × P and swap with q, t
    have hP_sum : ∑ x ∈ P, ∑ y ∈ P,
          ((ArithmeticFunction.moebius x.1 : ℝ) / gamma d x.2 * indCoprime d a x.2 n : ℂ) *
          ((ArithmeticFunction.moebius y.1 : ℝ) / gamma d y.2 * indCoprime d a y.2 n : ℂ) =
        ∑ q ∈ SF d (R ^ 2),
          (∑ t ∈ SF d R,
            (((1 / (t.totient : ℝ)) *
              ∑ x ∈ P, ∑ y ∈ P,
                (if q ∣ Nat.lcm x.2 y.2 ∧ t ∣ x.2 ∧ t ∣ y.2 then
                  (ArithmeticFunction.moebius x.1 : ℝ) * (ArithmeticFunction.moebius y.1 : ℝ)
                else 0) : ℝ) : ℂ)) *
          ∑ b ∈ reducedRes q, sCoeff d a q b * phase (-(b : ℝ) * (n : ℝ) / (q : ℝ)) := by
      have hrew : ∑ x ∈ P, ∑ y ∈ P,
            ((ArithmeticFunction.moebius x.1 : ℝ) / gamma d x.2 * indCoprime d a x.2 n : ℂ) *
            ((ArithmeticFunction.moebius y.1 : ℝ) / gamma d y.2 * indCoprime d a y.2 n : ℂ) =
          ∑ x ∈ P, ∑ y ∈ P, ∑ q ∈ SF d (R ^ 2), ∑ t ∈ SF d R,
            (((if q ∣ Nat.lcm x.2 y.2 ∧ t ∣ x.2 ∧ t ∣ y.2 then
                (1 / (t.totient : ℝ)) * (ArithmeticFunction.moebius x.1 : ℝ) *
                  (ArithmeticFunction.moebius y.1 : ℝ)
              else 0) : ℝ) : ℂ) *
            ∑ b ∈ reducedRes q, sCoeff d a q b * phase (-(b : ℝ) * (n : ℝ) / (q : ℝ)) :=
        sum_congr rfl fun x hx => sum_congr rfl fun y hy => hterm_id x hx y hy
      rw [hrew]
      simp_rw [← sum_mul]
      have hswap1 : ∀ x ∈ P,
          ∑ y ∈ P, ∑ q ∈ SF d (R ^ 2),
            (∑ t ∈ SF d R, (((if q ∣ Nat.lcm x.2 y.2 ∧ t ∣ x.2 ∧ t ∣ y.2 then
                (1 / (t.totient : ℝ)) * (ArithmeticFunction.moebius x.1 : ℝ) *
                  (ArithmeticFunction.moebius y.1 : ℝ)
              else 0) : ℝ) : ℂ)) *
            ∑ b ∈ reducedRes q, sCoeff d a q b * phase (-(b : ℝ) * (n : ℝ) / (q : ℝ)) =
          ∑ q ∈ SF d (R ^ 2), ∑ y ∈ P,
            (∑ t ∈ SF d R, (((if q ∣ Nat.lcm x.2 y.2 ∧ t ∣ x.2 ∧ t ∣ y.2 then
                (1 / (t.totient : ℝ)) * (ArithmeticFunction.moebius x.1 : ℝ) *
                  (ArithmeticFunction.moebius y.1 : ℝ)
              else 0) : ℝ) : ℂ)) *
            ∑ b ∈ reducedRes q, sCoeff d a q b * phase (-(b : ℝ) * (n : ℝ) / (q : ℝ)) :=
        fun x _ => sum_comm
      rw [sum_congr rfl hswap1, sum_comm]
      refine sum_congr rfl fun q _ => ?_
      simp_rw [← sum_mul]
      congr 1
      have hswap2 : ∀ x ∈ P,
          ∑ y ∈ P, ∑ t ∈ SF d R,
            (((if q ∣ Nat.lcm x.2 y.2 ∧ t ∣ x.2 ∧ t ∣ y.2 then
                (1 / (t.totient : ℝ)) * (ArithmeticFunction.moebius x.1 : ℝ) *
                  (ArithmeticFunction.moebius y.1 : ℝ)
              else 0) : ℝ) : ℂ) =
          ∑ t ∈ SF d R, ∑ y ∈ P,
            (((if q ∣ Nat.lcm x.2 y.2 ∧ t ∣ x.2 ∧ t ∣ y.2 then
                (1 / (t.totient : ℝ)) * (ArithmeticFunction.moebius x.1 : ℝ) *
                  (ArithmeticFunction.moebius y.1 : ℝ)
              else 0) : ℝ) : ℂ) :=
        fun x _ => sum_comm
      rw [sum_congr rfl hswap2, sum_comm]
      refine sum_congr rfl fun t _ => ?_
      rw [Complex.ofReal_mul, Complex.ofReal_sum, mul_sum]
      refine sum_congr rfl fun x _ => ?_
      rw [Complex.ofReal_sum, mul_sum]
      refine sum_congr rfl fun y _ => ?_
      by_cases hcond : q ∣ Nat.lcm x.2 y.2 ∧ t ∣ x.2 ∧ t ∣ y.2
      · rw [ite_eq_left hcond, ite_eq_left hcond]; push_cast; ring
      · rw [ite_eq_right hcond, ite_eq_right hcond]; simp
    -- Bijection between the P×P sum and Sqt q t
    have hSqt_eq : ∀ q ∈ SF d (R ^ 2), ∀ t ∈ SF d R,
        ∑ x ∈ P, ∑ y ∈ P,
          (if q ∣ Nat.lcm x.2 y.2 ∧ t ∣ x.2 ∧ t ∣ y.2 then
            (ArithmeticFunction.moebius x.1 : ℝ) * (ArithmeticFunction.moebius y.1 : ℝ)
          else 0) = Sqt q t := by
      intro q hq t ht
      have ht1 : 1 ≤ t := (mem_Icc.mp (mem_filter.mp ht).1).1
      let P' := (Icc 1 (R / t)).sigma (fun l => l.divisors)
      have hsingle : ∀ (F : ℕ → ℕ → ℝ),
          ∑ x ∈ P, (if t ∣ x.2 then F x.1 (x.2 / t) else 0) =
          ∑ z ∈ P', F (z.1 / z.2) z.2 := by
        intro F
        rw [← sum_filter]
        refine Finset.sum_bij (fun x _ => ⟨x.1 * (x.2 / t), x.2 / t⟩) ?_ ?_ ?_ ?_
        · rintro ⟨u, r⟩ hx
          have hxr := (mem_filter.mp hx).1
          have htr : t ∣ r := (mem_filter.mp hx).2
          have hu1 : 1 ≤ u := (mem_Icc.mp (mem_sigma.mp hxr).1).1
          have hr1 : 1 ≤ r := (mem_Icc.mp (mem_sigma.mp hxr).2).1
          have hrle : r ≤ R / u := (mem_Icc.mp (mem_sigma.mp hxr).2).2
          have hr'pos : 1 ≤ r / t :=
            (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using Nat.le_of_dvd (by omega) htr)
          have hl1 : 1 ≤ u * (r / t) := by nlinarith
          have hlR : u * (r / t) ≤ R / t := by
            apply (Nat.le_div_iff_mul_le (by omega)).mpr
            calc
              u * (r / t) * t = u * (r / t * t) := by ring
              _ = u * r := by rw [Nat.div_mul_cancel htr]
              _ ≤ R := by have := (Nat.le_div_iff_mul_le (by omega)).mp hrle; linarith
          exact mem_sigma.mpr ⟨mem_Icc.mpr ⟨hl1, hlR⟩,
            Nat.mem_divisors.mpr ⟨dvd_mul_left _ _, by nlinarith⟩⟩
        · rintro ⟨u₁, r₁⟩ h₁ ⟨u₂, r₂⟩ h₂ heq
          have htr1 : t ∣ r₁ := (mem_filter.mp h₁).2
          have htr2 : t ∣ r₂ := (mem_filter.mp h₂).2
          have hr1_eq : r₁ / t = r₂ / t := by
            have := congrArg Sigma.snd heq; simpa using this
          have hl_eq : u₁ * (r₁ / t) = u₂ * (r₂ / t) := by
            have := congrArg Sigma.fst heq; simpa using this
          have hr_eq : r₁ = r₂ := by
            calc
              r₁ = r₁ / t * t := (Nat.div_mul_cancel htr1).symm
              _ = r₂ / t * t := by rw [hr1_eq]
              _ = r₂ := Nat.div_mul_cancel htr2
          have hr'pos : 0 < r₁ / t := by
            have hr1 : 1 ≤ r₁ := (mem_Icc.mp (mem_sigma.mp (mem_filter.mp h₁).1).2).1
            exact (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using Nat.le_of_dvd (by omega) htr1)
          have hu_eq : u₁ = u₂ := Nat.eq_of_mul_eq_mul_right hr'pos (hr1_eq ▸ hl_eq)
          exact Sigma.ext hu_eq (heq_of_eq hr_eq)
        · rintro ⟨l, r'⟩ hz
          have hl1 : 1 ≤ l := (mem_Icc.mp (mem_sigma.mp hz).1).1
          have hlR : l ≤ R / t := (mem_Icc.mp (mem_sigma.mp hz).1).2
          have hr'd : r' ∣ l := Nat.dvd_of_mem_divisors (mem_sigma.mp hz).2
          have hr'1 : 1 ≤ r' := Nat.pos_of_dvd_of_pos hr'd (by omega)
          let u := l / r'
          have hu1 : 1 ≤ u := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using Nat.le_of_dvd (by omega) hr'd)
          have hul : u * r' = l := Nat.div_mul_cancel hr'd
          have hur : u * (t * r') ≤ R := by
            have hlRt : l * t ≤ R := (Nat.le_div_iff_mul_le (by omega)).mp hlR
            calc
              u * (t * r') = (u * r') * t := by ring
              _ = l * t := by rw [hul]
              _ ≤ R := hlRt
          have huR : u ≤ R := by nlinarith
          have htr_le : t * r' ≤ R / u := (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)
          refine ⟨⟨u, t * r'⟩, ?_, ?_⟩
          · exact mem_filter.mpr ⟨mem_sigma.mpr ⟨mem_Icc.mpr ⟨hu1, huR⟩,
              mem_Icc.mpr ⟨by nlinarith, htr_le⟩⟩, dvd_mul_right t r'⟩
          · have hdiv : t * r' / t = r' := Nat.mul_div_right r' (by omega)
            exact Sigma.ext (by dsimp; rw [hdiv, hul]) (heq_of_eq (by dsimp; rw [hdiv]))
        · rintro ⟨u, r⟩ hx
          have htr : t ∣ r := (mem_filter.mp hx).2
          have hr1 : 1 ≤ r := (mem_Icc.mp (mem_sigma.mp (mem_filter.mp hx).1).2).1
          have hr'pos : 0 < r / t :=
            (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using Nat.le_of_dvd (by omega) htr)
          dsimp
          rw [Nat.mul_div_cancel u hr'pos]
      have hrew_iff : ∀ r₁ r₂ : ℕ, t ∣ r₁ → t ∣ r₂ →
          (q ∣ Nat.lcm r₁ r₂ ↔ q / Nat.gcd q t ∣ Nat.lcm (r₁ / t) (r₂ / t)) := by
        intro r₁ r₂ ht1' ht2'
        have hlcm_t : Nat.lcm r₁ r₂ = t * Nat.lcm (r₁ / t) (r₂ / t) := by
          conv_lhs => rw [← Nat.mul_div_cancel' ht1', ← Nat.mul_div_cancel' ht2']
          exact Nat.lcm_mul_left t (r₁ / t) (r₂ / t)
        rw [hlcm_t]
        let g := Nat.gcd q t
        let L := Nat.lcm (r₁ / t) (r₂ / t)
        have hgpos : 0 < g := Nat.gcd_pos_of_pos_right q (by omega)
        have hq_eq : q = g * (q / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left q t)).symm
        have ht_eq : t = g * (t / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right q t)).symm
        have hcop_gt : (q / g).Coprime (t / g) := Nat.coprime_div_gcd_div_gcd hgpos
        change q ∣ t * L ↔ q / g ∣ L
        have h1 : q ∣ t * L ↔ g * (q / g) ∣ g * ((t / g) * L) := by
          conv_lhs => rw [hq_eq, ht_eq, mul_assoc]
        rw [h1, mul_dvd_mul_iff_left hgpos.ne']
        exact ⟨fun h => hcop_gt.dvd_of_dvd_mul_left h, fun h => dvd_mul_of_dvd_right h (t / g)⟩
      have hstep_x : ∑ x ∈ P, ∑ y ∈ P,
            (if q ∣ Nat.lcm x.2 y.2 ∧ t ∣ x.2 ∧ t ∣ y.2 then
              (ArithmeticFunction.moebius x.1 : ℝ) * (ArithmeticFunction.moebius y.1 : ℝ)
            else 0) =
          ∑ x ∈ P, (if t ∣ x.2 then
            ∑ y ∈ P, (if t ∣ y.2 then
              (if q / Nat.gcd q t ∣ Nat.lcm (x.2 / t) (y.2 / t) then
                (ArithmeticFunction.moebius x.1 : ℝ) * (ArithmeticFunction.moebius y.1 : ℝ)
              else 0)
            else 0)
          else 0) := by
        refine sum_congr rfl fun x _ => ?_
        by_cases htx : t ∣ x.2
        · rw [ite_eq_left htx]
          refine sum_congr rfl fun y _ => ?_
          by_cases hty : t ∣ y.2
          · simp only [htx, hty, and_true, ite_eq_left, hrew_iff x.2 y.2 htx hty]
          · simp [hty]
        · rw [ite_eq_right htx]
          apply sum_eq_zero; intro y _; simp [htx]
      rw [hstep_x]
      rw [hsingle (fun u₁ r'₁ => ∑ y ∈ P, if t ∣ y.2 then
        (if q / Nat.gcd q t ∣ Nat.lcm r'₁ (y.2 / t) then
          (ArithmeticFunction.moebius u₁ : ℝ) * (ArithmeticFunction.moebius y.1 : ℝ)
        else 0) else 0)]
      have hstep_y : ∀ z₁ ∈ P',
          (∑ y ∈ P, if t ∣ y.2 then
            (if q / Nat.gcd q t ∣ Nat.lcm z₁.2 (y.2 / t) then
              (ArithmeticFunction.moebius (z₁.1 / z₁.2) : ℝ) * (ArithmeticFunction.moebius y.1 : ℝ)
            else 0) else 0) =
          ∑ z₂ ∈ P',
            (if q / Nat.gcd q t ∣ Nat.lcm z₁.2 z₂.2 then
              (ArithmeticFunction.moebius (z₁.1 / z₁.2) : ℝ) *
                (ArithmeticFunction.moebius (z₂.1 / z₂.2) : ℝ)
            else 0) := by
        intro z₁ _
        exact hsingle (fun u₂ r'₂ =>
          if q / Nat.gcd q t ∣ Nat.lcm z₁.2 r'₂ then
            (ArithmeticFunction.moebius (z₁.1 / z₁.2) : ℝ) * (ArithmeticFunction.moebius u₂ : ℝ)
          else 0)
      rw [sum_congr rfl hstep_y]
      dsimp [P', Sqt, rrA]
      rw [Finset.sum_sigma]
      refine sum_congr rfl fun l₁ _ => ?_
      simp_rw [Finset.sum_sigma]
      exact sum_comm
    rw [hP_sum, mul_sum]
    refine sum_congr rfl fun q hq => ?_
    rw [← mul_assoc, mul_sum]
    refine sum_congr rfl fun b _ => ?_
    dsimp [w]
    have hcoeff : ∑ t ∈ SF d R,
        (((1 / (t.totient : ℝ)) *
          ∑ x ∈ P, ∑ y ∈ P,
            (if q ∣ Nat.lcm x.2 y.2 ∧ t ∣ x.2 ∧ t ∣ y.2 then
              (ArithmeticFunction.moebius x.1 : ℝ) * (ArithmeticFunction.moebius y.1 : ℝ)
            else 0) : ℝ) : ℂ) =
        ((∑ t ∈ SF d R, (1 / (t.totient : ℝ)) * Sqt q t : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine sum_congr rfl fun t ht => ?_
      rw [hSqt_eq q hq t ht]
    rw [hcoeff]
    push_cast; ring

/-! ### Section 3: Discrete Fejer L^p restriction and duality -/

lemma sieveBeta_nonneg (d a R : ℕ) (n : ℤ) : 0 ≤ sieveBeta d a R n :=
  div_nonneg (sq_nonneg _) (sum_nonneg fun _ _ => by positivity)

def fejerWeight (L : ℕ) (n : ℤ) : ℝ :=
  max 0 (1 - (|n| : ℝ) / (L : ℝ))

def fejerKernel (L : ℕ) (α : ℝ) : ℝ :=
  (1 / (L : ℝ) ^ 2) * ‖∑ m ∈ range L, phase ((m : ℝ) * α)‖ ^ 2

def distInt (x : ℝ) : ℝ := |x - (round x : ℝ)|

lemma fejerWeight_nonneg (L : ℕ) (n : ℤ) : 0 ≤ fejerWeight L n := le_max_left _ _

lemma fejerWeight_le_one (L : ℕ) (n : ℤ) : fejerWeight L n ≤ 1 := by
  unfold fejerWeight
  apply max_le (by norm_num)
  have h : 0 ≤ (|n| : ℝ) / (L : ℝ) := by positivity
  linarith

lemma fejerWeight_zero (L : ℕ) : fejerWeight L 0 = 1 := by
  unfold fejerWeight; simp

lemma fejerWeight_ge_half {N : ℕ} (hN : 1 ≤ N) {n : ℕ} (hn : n < N) :
    (1 / 2 : ℝ) ≤ fejerWeight (2 * N) (n : ℤ) := by
  unfold fejerWeight
  apply le_trans _ (le_max_right _ _)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hnr : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn.le
  have hdiv : ((|(n : ℤ)| : ℝ)) / ((2 * N : ℕ) : ℝ) ≤ 1 / 2 := by
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n), Nat.cast_mul, Nat.cast_ofNat]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  linarith

lemma fejerKernel_nonneg (L : ℕ) (α : ℝ) : 0 ≤ fejerKernel L α := by
  unfold fejerKernel; positivity

lemma fejerKernel_le_one {L : ℕ} (hL : 1 ≤ L) (α : ℝ) : fejerKernel L α ≤ 1 := by
  unfold fejerKernel
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have htri : ‖∑ m ∈ range L, phase ((m : ℝ) * α)‖ ≤ (L : ℝ) := by
    calc
      ‖∑ m ∈ range L, phase ((m : ℝ) * α)‖ ≤ ∑ m ∈ range L, ‖phase ((m : ℝ) * α)‖ :=
        norm_sum_le _ _
      _ = ∑ _m ∈ range L, (1 : ℝ) := sum_congr rfl fun _ _ => norm_phase _
      _ = (L : ℝ) := by simp
  have hsq : ‖∑ m ∈ range L, phase ((m : ℝ) * α)‖ ^ 2 ≤ (L : ℝ) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  calc
    (1 / (L : ℝ) ^ 2) * ‖∑ m ∈ range L, phase ((m : ℝ) * α)‖ ^ 2
        ≤ (1 / (L : ℝ) ^ 2) * (L : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 1 := by field_simp

lemma fejer_identity {L : ℕ} (hL : 1 ≤ L) (α : ℝ) :
    ((1 / (L : ℝ) : ℝ) : ℂ) *
      ∑ n ∈ Ioo (-(L : ℤ)) (L : ℤ), (fejerWeight L n : ℂ) * phase ((n : ℝ) * α) =
      (fejerKernel L α : ℂ) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hnorm_sq : ((‖∑ m ∈ range L, phase ((m : ℝ) * α)‖ ^ 2 : ℝ) : ℂ) =
      ∑ x ∈ range L ×ˢ range L, phase (((x.1 : ℤ) - (x.2 : ℤ) : ℝ) * α) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, sum_mul_sum, ← sum_product']
    refine sum_congr rfl fun ⟨m₁, m₂⟩ _ => ?_
    rw [← phase_neg, ← phase_add]
    congr 1; push_cast; ring
  have hmaps : ∀ x ∈ range L ×ˢ range L, (x.1 : ℤ) - (x.2 : ℤ) ∈ Ioo (-(L : ℤ)) (L : ℤ) := by
    intro ⟨m₁, m₂⟩ hx
    have h1 := mem_range.mp (mem_product.mp hx).1
    have h2 := mem_range.mp (mem_product.mp hx).2
    exact mem_Ioo.mpr ⟨by omega, by omega⟩
  have hfib_card : ∀ n ∈ Ioo (-(L : ℤ)) (L : ℤ),
      ((range L ×ˢ range L).filter (fun x => (x.1 : ℤ) - (x.2 : ℤ) = n)).card = L - n.natAbs := by
    intro n hn
    have hlo : -(L : ℤ) < n := (mem_Ioo.mp hn).1
    have hhi : n < (L : ℤ) := (mem_Ioo.mp hn).2
    rw [← card_range (L - n.natAbs)]
    by_cases h0 : 0 ≤ n
    · have hna : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg h0
      refine Finset.card_bij (fun x _ => x.2) ?_ ?_ ?_
      · intro ⟨m₁, m₂⟩ hx
        have h1 := mem_range.mp (mem_product.mp (mem_filter.mp hx).1).1
        have h2 := mem_range.mp (mem_product.mp (mem_filter.mp hx).1).2
        have heq : (m₁ : ℤ) - (m₂ : ℤ) = n := (mem_filter.mp hx).2
        exact mem_range.mpr (by omega)
      · intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
        dsimp only at heq
        have e1 : (a₁ : ℤ) - (b₁ : ℤ) = n := (mem_filter.mp h₁).2
        have e2 : (a₂ : ℤ) - (b₂ : ℤ) = n := (mem_filter.mp h₂).2
        exact Prod.ext (by omega) heq
      · intro b hb
        have hb' := mem_range.mp hb
        refine ⟨(b + n.natAbs, b), ?_, rfl⟩
        exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩,
          by omega⟩
    · have hna : (n.natAbs : ℤ) = -n := Int.ofNat_natAbs_of_nonpos (by omega)
      refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
      · intro ⟨m₁, m₂⟩ hx
        have h1 := mem_range.mp (mem_product.mp (mem_filter.mp hx).1).1
        have h2 := mem_range.mp (mem_product.mp (mem_filter.mp hx).1).2
        have heq : (m₁ : ℤ) - (m₂ : ℤ) = n := (mem_filter.mp hx).2
        exact mem_range.mpr (by omega)
      · intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
        dsimp only at heq
        have e1 : (a₁ : ℤ) - (b₁ : ℤ) = n := (mem_filter.mp h₁).2
        have e2 : (a₂ : ℤ) - (b₂ : ℤ) = n := (mem_filter.mp h₂).2
        exact Prod.ext heq (by omega)
      · intro a ha
        have ha' := mem_range.mp ha
        refine ⟨(a, a + n.natAbs), ?_, rfl⟩
        exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩,
          by omega⟩
  have hsum_eq : ∑ x ∈ range L ×ˢ range L, phase (((x.1 : ℤ) - (x.2 : ℤ) : ℝ) * α) =
      ∑ n ∈ Ioo (-(L : ℤ)) (L : ℤ), (((L - n.natAbs : ℕ) : ℝ) : ℂ) * phase ((n : ℝ) * α) := by
    rw [← sum_fiberwise_of_maps_to hmaps]
    refine sum_congr rfl fun n hn => ?_
    have hconst : ∑ x ∈ (range L ×ˢ range L).filter (fun x => (x.1 : ℤ) - (x.2 : ℤ) = n),
        phase (((x.1 : ℤ) - (x.2 : ℤ) : ℝ) * α) =
        ∑ _x ∈ (range L ×ˢ range L).filter (fun x => (x.1 : ℤ) - (x.2 : ℤ) = n),
        phase ((n : ℝ) * α) :=
      sum_congr rfl fun x hx => by
        have heq : ((x.1 : ℤ) - (x.2 : ℤ) : ℤ) = n := (mem_filter.mp hx).2
        congr 1; congr 1; exact_mod_cast heq
    rw [hconst, sum_const, hfib_card n hn, nsmul_eq_mul, Complex.ofReal_natCast]
  unfold fejerKernel
  rw [Complex.ofReal_mul, hnorm_sq, hsum_eq, mul_sum, mul_sum]
  refine sum_congr rfl fun n hn => ?_
  have hlo : -(L : ℤ) < n := (mem_Ioo.mp hn).1
  have hhi : n < (L : ℤ) := (mem_Ioo.mp hn).2
  have hna_le : n.natAbs ≤ L := by omega
  have habs_eq : |(n : ℝ)| = (n.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  have hfw : fejerWeight L n = 1 - (n.natAbs : ℝ) / (L : ℝ) := by
    unfold fejerWeight
    rw [habs_eq, max_eq_right]
    have h1 : (n.natAbs : ℝ) / (L : ℝ) ≤ 1 := (div_le_one hLpos).mpr (by exact_mod_cast hna_le)
    linarith
  rw [hfw, ← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1; congr 1
  rw [Nat.cast_sub hna_le]
  field_simp

lemma distInt_nonneg (x : ℝ) : 0 ≤ distInt x := abs_nonneg _

lemma distInt_le_half (x : ℝ) : distInt x ≤ 1 / 2 := abs_sub_round x

lemma distInt_le_abs_sub_int (x : ℝ) (k : ℤ) : distInt x ≤ |x - (k : ℝ)| := by
  unfold distInt
  by_cases hk : k = round x
  · rw [hk]
  · have hge1 : (1 : ℝ) ≤ |(round x : ℝ) - (k : ℝ)| := by
      have : (1 : ℤ) ≤ |round x - k| := Int.one_le_abs (sub_ne_zero.mpr (Ne.symm hk))
      exact_mod_cast this
    have hhalf := abs_sub_round x
    have htri := abs_sub_le (round x : ℝ) x (k : ℝ)
    rw [abs_sub_comm (round x : ℝ) x] at htri
    linarith

lemma distInt_add_int (x : ℝ) (k : ℤ) : distInt (x + (k : ℝ)) = distInt x := by
  unfold distInt
  rw [round_add_intCast]
  push_cast
  congr 1; ring

lemma distInt_neg (x : ℝ) : distInt (-x) = distInt x := by
  apply le_antisymm
  · have h := distInt_le_abs_sub_int (-x) (-round x)
    push_cast at h
    unfold distInt at h ⊢
    simpa only [sub_neg_eq_add, show -x + (round x : ℝ) = -(x - (round x : ℝ)) by ring, abs_neg] using h
  · have h := distInt_le_abs_sub_int x (-round (-x))
    push_cast at h
    unfold distInt at h ⊢
    simpa only [sub_neg_eq_add, show x + (round (-x) : ℝ) = -(-x - (round (-x) : ℝ)) by ring, abs_neg] using h

lemma norm_phase_sub_one_ge (α : ℝ) : 4 * distInt α ≤ ‖phase α - 1‖ := by
  let t : ℝ := α - (round α : ℝ)
  have ht_abs : |t| = distInt α := rfl
  have ht_half : |t| ≤ 1 / 2 := abs_sub_round α
  have hph : phase α = phase t := phase_eq_of_int_sub (k := round α) (by dsimp [t]; ring)
  rw [hph]
  have hfac : phase t - 1 =
      Complex.exp (((Real.pi * t : ℝ) : ℂ) * Complex.I) *
        (Complex.exp (((Real.pi * t : ℝ) : ℂ) * Complex.I) -
         Complex.exp (((-(Real.pi * t) : ℝ) : ℂ) * Complex.I)) := by
    rw [mul_sub, ← Complex.exp_add, ← Complex.exp_add]
    unfold phase GoldbachMajorArc.phase
    have h1 : (((Real.pi * t : ℝ) : ℂ) * Complex.I) + (((Real.pi * t : ℝ) : ℂ) * Complex.I) =
        (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by push_cast; ring
    have h2 : (((Real.pi * t : ℝ) : ℂ) * Complex.I) + (((-(Real.pi * t) : ℝ) : ℂ) * Complex.I) = 0 := by
      push_cast; ring
    rw [h1, h2, Complex.exp_zero]
  have hsin : Complex.exp (((Real.pi * t : ℝ) : ℂ) * Complex.I) -
      Complex.exp (((-(Real.pi * t) : ℝ) : ℂ) * Complex.I) =
      ((2 * Real.sin (Real.pi * t) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast; ring
  rw [hfac, hsin, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, Complex.norm_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hsin_ge : 2 * |t| ≤ |Real.sin (Real.pi * t)| := by
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have harg_le : Real.pi * |t| ≤ Real.pi / 2 := by nlinarith
    have hmul := Real.mul_le_sin (by positivity : 0 ≤ Real.pi * |t|) harg_le
    have hcalc : 2 / Real.pi * (Real.pi * |t|) = 2 * |t| := by field_simp
    rw [hcalc] at hmul
    have habs_sin : Real.sin (Real.pi * |t|) = |Real.sin (Real.pi * t)| := by
      by_cases ht0 : 0 ≤ t
      · rw [abs_of_nonneg ht0] at ht_half ⊢
        rw [abs_of_nonneg]
        exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)
      · have ht_neg : t < 0 := not_le.mp ht0
        rw [abs_of_neg ht_neg] at ht_half ⊢
        rw [mul_neg, Real.sin_neg, ← abs_neg (Real.sin (Real.pi * t)), abs_of_nonneg]
        have h1 : 0 ≤ Real.sin (-(Real.pi * t)) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by nlinarith)
        rw [Real.sin_neg] at h1
        exact h1
    linarith
  rw [← ht_abs]
  linarith

lemma fejerKernel_le_inv_sq {L : ℕ} (hL : 1 ≤ L) {α : ℝ} (hα : 0 < distInt α) :
    fejerKernel L α ≤ 1 / (4 * (L : ℝ) ^ 2 * (distInt α) ^ 2) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hph_ne : phase α ≠ 1 := by
    intro heq
    have h := norm_phase_sub_one_ge α
    rw [heq, sub_self, norm_zero] at h
    linarith
  have hgeom : ∑ m ∈ range L, phase ((m : ℝ) * α) = (phase ((L : ℝ) * α) - 1) / (phase α - 1) := by
    have hpow : ∀ m : ℕ, phase ((m : ℝ) * α) = (phase α) ^ m := by
      intro m
      induction m with
      | zero => simp [phase_zero]
      | succ k ih =>
        push_cast; rw [add_mul, one_mul, phase_add, ih, pow_succ]
    simp_rw [hpow]
    rw [geom_sum_eq hph_ne, ← hpow L]
  have hnum : ‖phase ((L : ℝ) * α) - 1‖ ≤ 2 := by
    calc
      ‖phase ((L : ℝ) * α) - 1‖ ≤ ‖phase ((L : ℝ) * α)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_phase, norm_one]; norm_num
  have hden : 4 * distInt α ≤ ‖phase α - 1‖ := norm_phase_sub_one_ge α
  have hsum_le : ‖∑ m ∈ range L, phase ((m : ℝ) * α)‖ ≤ 1 / (2 * distInt α) := by
    rw [hgeom, norm_div]
    calc
      ‖phase ((L : ℝ) * α) - 1‖ / ‖phase α - 1‖
          ≤ 2 / (4 * distInt α) :=
        div_le_div₀ (by norm_num) hnum (by positivity) hden
      _ = 1 / (2 * distInt α) := by field_simp; ring
  have hsq : ‖∑ m ∈ range L, phase ((m : ℝ) * α)‖ ^ 2 ≤ 1 / (4 * (distInt α) ^ 2) := by
    have h1 := pow_le_pow_left₀ (norm_nonneg _) hsum_le 2
    have h2 : (1 / (2 * distInt α)) ^ 2 = 1 / (4 * (distInt α) ^ 2) := by ring
    linarith
  unfold fejerKernel
  calc
    (1 / (L : ℝ) ^ 2) * ‖∑ m ∈ range L, phase ((m : ℝ) * α)‖ ^ 2
        ≤ (1 / (L : ℝ) ^ 2) * (1 / (4 * (distInt α) ^ 2)) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 1 / (4 * (L : ℝ) ^ 2 * (distInt α) ^ 2) := by ring

lemma sum_inv_sq_le_two (M : ℕ) :
    ∑ m ∈ Icc 1 M, (1 : ℝ) / ((m : ℝ) ^ 2) ≤ 2 := by
  induction M with
  | zero => simp
  | succ k ih =>
    cases k with
    | zero => simp
    | succ m =>
      have htele : ∑ j ∈ Icc 1 (m + 2), (1 : ℝ) / ((j : ℝ) ^ 2) ≤ 2 - 1 / ((m + 2 : ℕ) : ℝ) := by
        clear ih
        induction m with
        | zero =>
          have : Icc 1 2 = {1, 2} := by decide
          rw [this, sum_pair (by decide)]; norm_num
        | succ m' ihm =>
          have hsplit : Icc 1 (m' + 3) = insert (m' + 3) (Icc 1 (m' + 2)) := by
            ext x; simp only [mem_Icc, mem_insert]; omega
          rw [hsplit, sum_insert (by simp)]
          have hstep : (1 : ℝ) / (((m' + 3 : ℕ) : ℝ) ^ 2) ≤
              1 / ((m' + 2 : ℕ) : ℝ) - 1 / ((m' + 3 : ℕ) : ℝ) := by
            have h1 : (0 : ℝ) < ((m' + 2 : ℕ) : ℝ) := by positivity
            have h2 : (0 : ℝ) < ((m' + 3 : ℕ) : ℝ) := by positivity
            have hdiff : 1 / ((m' + 2 : ℕ) : ℝ) - 1 / ((m' + 3 : ℕ) : ℝ) =
                1 / (((m' + 2 : ℕ) : ℝ) * ((m' + 3 : ℕ) : ℝ)) := by
              field_simp; push_cast; ring
            rw [hdiff]
            apply one_div_le_one_div_of_le (by positivity)
            push_cast; nlinarith
          linarith
      have hpos : (0 : ℝ) ≤ 1 / ((m + 2 : ℕ) : ℝ) := by positivity
      linarith

lemma fejer_separated_sum_le {ι : Type*} [DecidableEq ι] (S : Finset ι) (x : ι → ℝ)
    {L : ℕ} (hL : 1 ≤ L) {δ : ℝ} (hδ : 0 < δ) (hLδ : 1 ≤ (L : ℝ) * δ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ distInt (x i - x j)) (y : ℝ) :
    ∑ i ∈ S, fejerKernel L (y - x i) ≤ 4 := by
  let t : ι → ℝ := fun i => (y - x i) - (round (y - x i) : ℝ)
  let b : ι → ℤ := fun i => ⌊t i / δ⌋
  have hb_inj : ∀ i ∈ S, ∀ j ∈ S, b i = b j → i = j := by
    intro i hi j hj heq
    by_contra hne
    have hs := hsep i hi j hj hne
    have hdiff : |t i - t j| < δ := by
      have hi1 : (b i : ℝ) ≤ t i / δ := Int.floor_le (t i / δ)
      have hi2 : t i / δ < (b i : ℝ) + 1 := Int.lt_floor_add_one (t i / δ)
      have hj1 : (b j : ℝ) ≤ t j / δ := Int.floor_le (t j / δ)
      have hj2 : t j / δ < (b j : ℝ) + 1 := Int.lt_floor_add_one (t j / δ)
      rw [heq] at hi1 hi2
      have hdiv : |t i / δ - t j / δ| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
      rw [← sub_div, abs_div, abs_of_pos hδ, div_lt_one hδ] at hdiv
      exact hdiv
    have hdist_eq : distInt (x i - x j) = distInt (t j - t i) := by
      have hsub : (x i - x j) - (t j - t i) = ((round (y - x j) - round (y - x i) : ℤ) : ℝ) := by
        dsimp [t]; push_cast; ring
      have h1 : x i - x j = (t j - t i) + ((round (y - x j) - round (y - x i) : ℤ) : ℝ) := by
        linarith
      rw [h1, distInt_add_int]
    have hle : distInt (t j - t i) ≤ |t i - t j| := by
      have h0 := distInt_le_abs_sub_int (t j - t i) 0
      simpa only [Int.cast_zero, sub_zero, abs_sub_comm] using h0
    linarith
  -- Split S into middle (b i ∈ {-1, 0}), right (1 ≤ b i), and left (b i ≤ -2)
  let Smid := S.filter (fun i => b i = -1 ∨ b i = 0)
  let Spos := S.filter (fun i => 1 ≤ b i)
  let Sneg := S.filter (fun i => b i ≤ -2)
  have hpart : ∑ i ∈ S, fejerKernel L (y - x i) =
      (∑ i ∈ Smid, fejerKernel L (y - x i)) +
      (∑ i ∈ Spos, fejerKernel L (y - x i)) +
      (∑ i ∈ Sneg, fejerKernel L (y - x i)) := by
    have hdisj1 : Disjoint Smid Spos := by
      rw [Finset.disjoint_filter]; intro i _ h1 h2; omega
    have hdisj2 : Disjoint (Smid ∪ Spos) Sneg := by
      rw [Finset.disjoint_left]; intro i h1 h2
      have h2' := (mem_filter.mp h2).2
      rcases mem_union.mp h1 with hm | hp
      · have := (mem_filter.mp hm).2; omega
      · have := (mem_filter.mp hp).2; omega
    have hunion : S = (Smid ∪ Spos) ∪ Sneg := by
      ext i; simp only [Smid, Spos, Sneg, mem_union, mem_filter]
      constructor
      · intro hi
        by_cases h1 : b i = -1 ∨ b i = 0
        · exact Or.inl (Or.inl ⟨hi, h1⟩)
        · by_cases h2 : 1 ≤ b i
          · exact Or.inl (Or.inr ⟨hi, h2⟩)
          · exact Or.inr ⟨hi, by omega⟩
      · rintro ((⟨hi, _⟩ | ⟨hi, _⟩) | ⟨hi, _⟩) <;> exact hi
    conv_lhs => rw [hunion]
    rw [sum_union hdisj2, sum_union hdisj1]
  have hmid : ∑ i ∈ Smid, fejerKernel L (y - x i) ≤ 2 := by
    have hcard : Smid.card ≤ 2 := by
      have himg : Smid.image b ⊆ ({-1, 0} : Finset ℤ) := by
        intro z hz; obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
        simp only [mem_insert, mem_singleton]; exact (mem_filter.mp hi).2
      calc
        Smid.card = (Smid.image b).card :=
          (card_image_of_injOn fun i₁ h₁ i₂ h₂ h =>
            hb_inj i₁ (mem_filter.mp h₁).1 i₂ (mem_filter.mp h₂).1 h).symm
        _ ≤ ({-1, 0} : Finset ℤ).card := card_le_card himg
        _ ≤ 2 := by decide
    calc
      ∑ i ∈ Smid, fejerKernel L (y - x i) ≤ ∑ _i ∈ Smid, (1 : ℝ) :=
        sum_le_sum fun i _ => fejerKernel_le_one hL _
      _ = (Smid.card : ℝ) := by simp
      _ ≤ 2 := by exact_mod_cast hcard
  have hpos : ∑ i ∈ Spos, fejerKernel L (y - x i) ≤ 1 := by
    let M : ℕ := (Spos.image (fun i => (b i).toNat)).sup id
    have hterm : ∀ i ∈ Spos, fejerKernel L (y - x i) ≤ (1 / 4 : ℝ) * (1 / (((b i).toNat : ℝ) ^ 2)) := by
      intro i hi
      have hbi : 1 ≤ b i := (mem_filter.mp hi).2
      have hbn : 1 ≤ (b i).toNat := by omega
      have hbn_eq : ((b i).toNat : ℝ) = (b i : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ b i)
      have hti : (b i : ℝ) * δ ≤ t i := (le_div_iff₀ hδ).mp (Int.floor_le (t i / δ))
      have hdist_ge : ((b i).toNat : ℝ) * δ ≤ distInt (y - x i) := by
        have hpos_t : 0 < t i := lt_of_lt_of_le (by positivity) hti
        change ((b i).toNat : ℝ) * δ ≤ |t i|
        rw [abs_of_pos hpos_t, hbn_eq]; exact hti
      have hdist_pos : 0 < distInt (y - x i) := lt_of_lt_of_le (by positivity) hdist_ge
      have hfk := fejerKernel_le_inv_sq hL hdist_pos
      have hden_le : 4 * ((b i).toNat : ℝ) ^ 2 ≤ 4 * (L : ℝ) ^ 2 * (distInt (y - x i)) ^ 2 := by
        have h1 : ((b i).toNat : ℝ) ≤ (L : ℝ) * distInt (y - x i) := by
          calc
            ((b i).toNat : ℝ) = ((b i).toNat : ℝ) * 1 := (mul_one _).symm
            _ ≤ ((b i).toNat : ℝ) * ((L : ℝ) * δ) :=
              mul_le_mul_of_nonneg_left hLδ (by positivity)
            _ = (L : ℝ) * (((b i).toNat : ℝ) * δ) := by ring
            _ ≤ (L : ℝ) * distInt (y - x i) := mul_le_mul_of_nonneg_left hdist_ge (by positivity)
        have h2 := pow_le_pow_left₀ (by positivity) h1 2
        rw [mul_pow] at h2
        linarith
      calc
        fejerKernel L (y - x i) ≤ 1 / (4 * (L : ℝ) ^ 2 * (distInt (y - x i)) ^ 2) := hfk
        _ ≤ 1 / (4 * ((b i).toNat : ℝ) ^ 2) := one_div_le_one_div_of_le (by positivity) hden_le
        _ = (1 / 4 : ℝ) * (1 / (((b i).toNat : ℝ) ^ 2)) := by ring
    have hinj : ∀ i₁ ∈ Spos, ∀ i₂ ∈ Spos, (b i₁).toNat = (b i₂).toNat → i₁ = i₂ := by
      intro i₁ h₁ i₂ h₂ heq
      have hb1 := (mem_filter.mp h₁).2
      have hb2 := (mem_filter.mp h₂).2
      have hbeq : b i₁ = b i₂ := by omega
      exact hb_inj i₁ (mem_filter.mp h₁).1 i₂ (mem_filter.mp h₂).1 hbeq
    calc
      ∑ i ∈ Spos, fejerKernel L (y - x i)
          ≤ ∑ i ∈ Spos, (1 / 4 : ℝ) * (1 / (((b i).toNat : ℝ) ^ 2)) := sum_le_sum hterm
      _ = (1 / 4 : ℝ) * ∑ m ∈ Spos.image (fun i => (b i).toNat), (1 : ℝ) / ((m : ℝ) ^ 2) := by
        rw [← mul_sum, sum_image (f := fun m : ℕ => (1 : ℝ) / ((m : ℝ) ^ 2)) hinj]
      _ ≤ (1 / 4 : ℝ) * ∑ m ∈ Icc 1 M, (1 : ℝ) / ((m : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply sum_le_sum_of_subset_of_nonneg
        · intro m hm
          obtain ⟨i, hi, rfl⟩ := mem_image.mp hm
          have hbi := (mem_filter.mp hi).2
          exact mem_Icc.mpr ⟨by omega, Finset.le_sup (f := id) hm⟩
        · intro _ _ _; positivity
      _ ≤ (1 / 4 : ℝ) * 2 := mul_le_mul_of_nonneg_left (sum_inv_sq_le_two M) (by norm_num)
      _ ≤ 1 := by norm_num
  have hneg : ∑ i ∈ Sneg, fejerKernel L (y - x i) ≤ 1 := by
    let g : ι → ℕ := fun i => (-b i - 1).toNat
    let M : ℕ := (Sneg.image g).sup id
    have hterm : ∀ i ∈ Sneg, fejerKernel L (y - x i) ≤ (1 / 4 : ℝ) * (1 / ((g i : ℝ) ^ 2)) := by
      intro i hi
      have hbi : b i ≤ -2 := (mem_filter.mp hi).2
      have hgn : 1 ≤ g i := by dsimp [g]; omega
      have hgn_eq : (g i : ℝ) = -(b i : ℝ) - 1 := by
        dsimp [g]; exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ -b i - 1)
      have hti : t i < ((b i : ℝ) + 1) * δ := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (t i / δ))
      have hdist_ge : (g i : ℝ) * δ ≤ distInt (y - x i) := by
        have hneg_t : t i < 0 := lt_of_lt_of_le hti (by
          have : (b i : ℝ) + 1 ≤ -1 := by exact_mod_cast (by omega : b i + 1 ≤ -1)
          nlinarith)
        change (g i : ℝ) * δ ≤ |t i|
        rw [abs_of_neg hneg_t, hgn_eq]; linarith
      have hdist_pos : 0 < distInt (y - x i) := lt_of_lt_of_le (by positivity) hdist_ge
      have hfk := fejerKernel_le_inv_sq hL hdist_pos
      have hden_le : 4 * (g i : ℝ) ^ 2 ≤ 4 * (L : ℝ) ^ 2 * (distInt (y - x i)) ^ 2 := by
        have h1 : (g i : ℝ) ≤ (L : ℝ) * distInt (y - x i) := by
          calc
            (g i : ℝ) = (g i : ℝ) * 1 := (mul_one _).symm
            _ ≤ (g i : ℝ) * ((L : ℝ) * δ) := mul_le_mul_of_nonneg_left hLδ (by positivity)
            _ = (L : ℝ) * ((g i : ℝ) * δ) := by ring
            _ ≤ (L : ℝ) * distInt (y - x i) := mul_le_mul_of_nonneg_left hdist_ge (by positivity)
        have h2 := pow_le_pow_left₀ (by positivity) h1 2
        rw [mul_pow] at h2
        linarith
      calc
        fejerKernel L (y - x i) ≤ 1 / (4 * (L : ℝ) ^ 2 * (distInt (y - x i)) ^ 2) := hfk
        _ ≤ 1 / (4 * (g i : ℝ) ^ 2) := one_div_le_one_div_of_le (by positivity) hden_le
        _ = (1 / 4 : ℝ) * (1 / ((g i : ℝ) ^ 2)) := by ring
    have hinj : ∀ i₁ ∈ Sneg, ∀ i₂ ∈ Sneg, g i₁ = g i₂ → i₁ = i₂ := by
      intro i₁ h₁ i₂ h₂ heq
      have hb1 := (mem_filter.mp h₁).2
      have hb2 := (mem_filter.mp h₂).2
      dsimp [g] at heq
      have hbeq : b i₁ = b i₂ := by omega
      exact hb_inj i₁ (mem_filter.mp h₁).1 i₂ (mem_filter.mp h₂).1 hbeq
    calc
      ∑ i ∈ Sneg, fejerKernel L (y - x i)
          ≤ ∑ i ∈ Sneg, (1 / 4 : ℝ) * (1 / ((g i : ℝ) ^ 2)) := sum_le_sum hterm
      _ = (1 / 4 : ℝ) * ∑ m ∈ Sneg.image g, (1 : ℝ) / ((m : ℝ) ^ 2) := by
        rw [← mul_sum, sum_image (f := fun m : ℕ => (1 : ℝ) / ((m : ℝ) ^ 2)) hinj]
      _ ≤ (1 / 4 : ℝ) * ∑ m ∈ Icc 1 M, (1 : ℝ) / ((m : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply sum_le_sum_of_subset_of_nonneg
        · intro m hm
          obtain ⟨i, hi, rfl⟩ := mem_image.mp hm
          have hbi := (mem_filter.mp hi).2
          exact mem_Icc.mpr ⟨by dsimp [g]; omega, Finset.le_sup (f := id) hm⟩
        · intro _ _ _; positivity
      _ ≤ (1 / 4 : ℝ) * 2 := mul_le_mul_of_nonneg_left (sum_inv_sq_le_two M) (by norm_num)
      _ ≤ 1 := by norm_num
  linarith

lemma phase_orthog {q : ℕ} (hq : 1 ≤ q) (n : ℤ) :
    ((1 / (q : ℝ) : ℝ) : ℂ) * ∑ r ∈ range q, phase (-(r : ℝ) * (n : ℝ) / (q : ℝ)) =
      if (q : ℤ) ∣ n then 1 else 0 := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  by_cases hdvd : (q : ℤ) ∣ n
  · rw [ite_eq_left hdvd]
    obtain ⟨k, rfl⟩ := hdvd
    have hsum : ∑ r ∈ range q, phase (-(r : ℝ) * (((q : ℤ) * k : ℤ) : ℝ) / (q : ℝ)) = (q : ℂ) := by
      have h1 : ∀ r ∈ range q, phase (-(r : ℝ) * (((q : ℤ) * k : ℤ) : ℝ) / (q : ℝ)) = 1 := by
        intro r _
        have harg : -(r : ℝ) * (((q : ℤ) * k : ℤ) : ℝ) / (q : ℝ) = ((-(r : ℤ) * k : ℤ) : ℝ) := by
          push_cast; field_simp
        rw [harg, phase_int]
      rw [sum_congr rfl h1, sum_const, card_range, nsmul_eq_mul, mul_one]
    rw [hsum]; push_cast; field_simp
  · rw [ite_eq_right hdvd]
    let z : ℂ := phase (-(n : ℝ) / (q : ℝ))
    have hz_ne : z ≠ 1 := by
      intro heq
      have hdist : distInt (-(n : ℝ) / (q : ℝ)) = 0 := by
        have h1 := norm_phase_sub_one_ge (-(n : ℝ) / (q : ℝ))
        have h0 := distInt_nonneg (-(n : ℝ) / (q : ℝ))
        dsimp [z] at heq
        rw [heq, sub_self, norm_zero] at h1
        linarith
      unfold distInt at hdist
      rw [abs_eq_zero, sub_eq_zero] at hdist
      have hmul : -(n : ℝ) = (round (-(n : ℝ) / (q : ℝ)) : ℝ) * (q : ℝ) := by
        have h1 := congrArg (· * (q : ℝ)) hdist
        rwa [div_mul_cancel₀ _ hqpos.ne'] at h1
      have hint : -n = round (-(n : ℝ) / (q : ℝ)) * (q : ℤ) := by exact_mod_cast hmul
      apply hdvd
      refine ⟨-round (-(n : ℝ) / (q : ℝ)), ?_⟩
      linarith
    have hpow : ∀ r : ℕ, phase (-(r : ℝ) * (n : ℝ) / (q : ℝ)) = z ^ r := by
      intro r
      induction r with
      | zero => simp [phase_zero]
      | succ k ih =>
        push_cast
        have harg : -(((k : ℝ) + 1) * (n : ℝ)) / (q : ℝ) =
            -(k : ℝ) * (n : ℝ) / (q : ℝ) + -(n : ℝ) / (q : ℝ) := by ring
        rw [show -((k : ℝ) + 1) * (n : ℝ) / (q : ℝ) =
            -(k : ℝ) * (n : ℝ) / (q : ℝ) + -(n : ℝ) / (q : ℝ) by ring,
          phase_add, ih, pow_succ]
    simp_rw [hpow]
    rw [geom_sum_eq hz_ne]
    have hzq : z ^ q = 1 := by
      rw [← hpow q]
      have harg : -(q : ℝ) * (n : ℝ) / (q : ℝ) = ((-n : ℤ) : ℝ) := by push_cast; field_simp
      rw [harg, phase_int]
    rw [hzq, sub_self, zero_div, mul_zero]

lemma ch_eq_phase {N : ℕ} [NeZero N] (r x : ZMod N) :
    PolynomialTransfer.ch r x = phase (-(r.val : ℝ) * (x.val : ℝ) / (N : ℝ)) := by
  unfold PolynomialTransfer.ch phase GoldbachMajorArc.phase
  have hcoe : ((-(r.val * x.val : ℤ) : ℤ) : ZMod N) = -(r * x) := by
    push_cast; simp [ZMod.natCast_zmod_val]
  rw [← hcoe, ZMod.stdAddChar_coe]
  push_cast; congr 1; ring

set_option maxHeartbeats 1200000 in
lemma sieveBeta_crude_bound :
    ∃ C_crude : ℝ, 0 < C_crude ∧ ∀ d a N : ℕ, 1 ≤ N → 1 ≤ a → a < d → d ≤ N →
      ∀ n : ℕ, n < N →
        sieveBeta d a ⌊(N : ℝ) ^ (1 / 20 : ℝ)⌋₊ (n : ℤ) ≤
          C_crude * (⌊(N : ℝ) ^ (1 / 20 : ℝ)⌋₊ : ℝ) ^ (1 / 10 : ℝ) := by
  obtain ⟨CG, hCG, hGup⟩ := G_upper_bound
  obtain ⟨CD, hCD, hDup⟩ := divisor_bound_eps (1 / 1000 : ℝ) (by norm_num)
  refine ⟨CG * CD ^ 2 * (2 : ℝ) ^ (41 / 500 : ℝ), by positivity, ?_⟩
  intro d a N hN ha had hdN n hn
  let R := ⌊(N : ℝ) ^ (1 / 20 : ℝ)⌋₊
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hR1 : 1 ≤ R := by
    dsimp [R]; exact Nat.le_floor (Real.one_le_rpow hN1 (by norm_num))
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR1
  have hN_le : (N : ℝ) ≤ (2 * (R : ℝ)) ^ 20 := by
    have hlt : (N : ℝ) ^ (1 / 20 : ℝ) < (R : ℝ) + 1 := Nat.lt_floor_add_one _
    have hle : (N : ℝ) ^ (1 / 20 : ℝ) ≤ 2 * (R : ℝ) := by
      have : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1
      linarith
    have hpow := pow_le_pow_left₀ (by positivity) hle 20
    have hlhs : ((N : ℝ) ^ (1 / 20 : ℝ)) ^ 20 = (N : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    linarith
  let M : ℕ := d * n + a
  have hM1 : 1 ≤ M := by omega
  have hM_ne : (d : ℤ) * (n : ℤ) + (a : ℤ) ≠ 0 := by omega
  have hM_natAbs : ((d : ℤ) * (n : ℤ) + (a : ℤ)).natAbs = M := by
    have : (d : ℤ) * (n : ℤ) + (a : ℤ) = (M : ℤ) := by simp [M]
    rw [this, Int.natAbs_natCast]
  have hM_le : (M : ℝ) ≤ 2 * (2 * (R : ℝ)) ^ 40 := by
    have h1 : M ≤ 2 * N ^ 2 := by dsimp [M]; nlinarith
    have h2 : (M : ℝ) ≤ 2 * (N : ℝ) ^ 2 := by exact_mod_cast h1
    have h3 : (N : ℝ) ^ 2 ≤ ((2 * (R : ℝ)) ^ 20) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hN_le 2
    have h4 : ((2 * (R : ℝ)) ^ 20) ^ 2 = (2 * (R : ℝ)) ^ 40 := by ring
    linarith
  have hraw := sieveBeta_crude_bound_raw (d := d) (a := a) (R := R) hR1 hM_ne
  rw [hM_natAbs] at hraw
  have hdiv_sq : (M.divisors.card : ℝ) ^ 2 ≤ CD ^ 2 * (2 : ℝ) ^ (41 / 500 : ℝ) * (R : ℝ) ^ (2 / 25 : ℝ) := by
    have hd1 : (M.divisors.card : ℝ) ≤ CD * (M : ℝ) ^ (1 / 1000 : ℝ) := hDup M hM1
    have hd2 : (M.divisors.card : ℝ) ^ 2 ≤ (CD * (M : ℝ) ^ (1 / 1000 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hd1 2
    have hMpos : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hm2 : ((M : ℝ) ^ (1 / 1000 : ℝ)) ^ 2 ≤ (2 * (2 * (R : ℝ)) ^ 40) ^ (2 / 1000 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hMpos]
      have hmul2 : (1 / 1000 : ℝ) * ((2 : ℕ) : ℝ) = 2 / 1000 := by norm_num
      rw [hmul2]
      exact Real.rpow_le_rpow hMpos hM_le (by norm_num)
    have hpow_eval : (2 * (2 * (R : ℝ)) ^ 40) ^ (2 / 1000 : ℝ) =
        (2 : ℝ) ^ (41 / 500 : ℝ) * (R : ℝ) ^ (2 / 25 : ℝ) := by
      have heq : 2 * (2 * (R : ℝ)) ^ 40 = (2 : ℝ) ^ 41 * (R : ℝ) ^ 40 := by ring
      have h41 : ((41 : ℕ) : ℝ) * (2 / 1000 : ℝ) = 41 / 500 := by norm_num
      have h40 : ((40 : ℕ) : ℝ) * (2 / 1000 : ℝ) = 2 / 25 := by norm_num
      rw [heq, Real.mul_rpow (pow_nonneg (by norm_num) 41) (pow_nonneg hRpos.le 40),
        ← Real.rpow_natCast (2 : ℝ), ← Real.rpow_natCast (R : ℝ),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_mul hRpos.le, h41, h40]
    calc
      (M.divisors.card : ℝ) ^ 2 ≤ CD ^ 2 * ((M : ℝ) ^ (1 / 1000 : ℝ)) ^ 2 := by
        simpa only [mul_pow] using hd2
      _ ≤ CD ^ 2 * ((2 : ℝ) ^ (41 / 500 : ℝ) * (R : ℝ) ^ (2 / 25 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hm2.trans_eq hpow_eval) (sq_nonneg CD)
      _ = CD ^ 2 * (2 : ℝ) ^ (41 / 500 : ℝ) * (R : ℝ) ^ (2 / 25 : ℝ) := by ring
  have hG_le : G d R ≤ CG * (R : ℝ) ^ (1 / 50 : ℝ) := hGup d R hR1
  have hexp : (R : ℝ) ^ (1 / 50 : ℝ) * (R : ℝ) ^ (2 / 25 : ℝ) = (R : ℝ) ^ (1 / 10 : ℝ) := by
    rw [← Real.rpow_add hRpos]; norm_num
  calc
    sieveBeta d a R (n : ℤ) ≤ G d R * (M.divisors.card : ℝ) ^ 2 := hraw
    _ ≤ (CG * (R : ℝ) ^ (1 / 50 : ℝ)) * (CD ^ 2 * (2 : ℝ) ^ (41 / 500 : ℝ) * (R : ℝ) ^ (2 / 25 : ℝ)) :=
      mul_le_mul hG_le hdiv_sq (by positivity) (by positivity)
    _ = CG * CD ^ 2 * (2 : ℝ) ^ (41 / 500 : ℝ) * ((R : ℝ) ^ (1 / 50 : ℝ) * (R : ℝ) ^ (2 / 25 : ℝ)) := by ring
    _ = CG * CD ^ 2 * (2 : ℝ) ^ (41 / 500 : ℝ) * (R : ℝ) ^ (1 / 10 : ℝ) := by rw [hexp]

lemma card_multiples_nonzero_Ioo_le {N L : ℕ} (hL : 1 ≤ L) :
    (((Ioo (-(2 * (N : ℤ))) (2 * (N : ℤ))).erase 0).filter (fun n : ℤ => (L : ℤ) ∣ n)).card ≤
      4 * N / L := by
  let S := ((Ioo (-(2 * (N : ℤ))) (2 * (N : ℤ))).erase 0).filter (fun n : ℤ => (L : ℤ) ∣ n)
  let Spos := S.filter (fun n : ℤ => 0 < n)
  let Sneg := S.filter (fun n : ℤ => n < 0)
  have hpart : S = Spos ∪ Sneg := by
    ext n; simp only [Spos, Sneg, mem_union, mem_filter]
    constructor
    · intro hn
      have hne : n ≠ 0 := (mem_erase.mp (mem_filter.mp hn).1).1
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inr ⟨hn, h⟩
      · exact Or.inl ⟨hn, h⟩
    · rintro (⟨hn, _⟩ | ⟨hn, _⟩) <;> exact hn
  have hdisj : Disjoint Spos Sneg := by
    rw [Finset.disjoint_filter]; intro n _ h1 h2; omega
  have hpos_le : Spos.card ≤ 2 * N / L := by
    let f : ℤ → ℕ := fun n => (n / (L : ℤ)).toNat
    have hmaps : ∀ n ∈ Spos, f n ∈ Icc 1 (2 * N / L) := by
      intro n hn
      have hS := (mem_filter.mp hn).1
      have hgt : 0 < n := (mem_filter.mp hn).2
      have hlt : n < 2 * (N : ℤ) := (mem_Ioo.mp (mem_erase.mp (mem_filter.mp hS).1).2).2
      have hdvd : (L : ℤ) ∣ n := (mem_filter.mp hS).2
      obtain ⟨k, rfl⟩ := hdvd
      have hkpos : 1 ≤ k := by nlinarith
      have hfk : f ((L : ℤ) * k) = k.toNat := by
        dsimp [f]; rw [Int.mul_ediv_cancel_left k (by omega : (L : ℤ) ≠ 0)]
      rw [hfk]
      have hkle : k.toNat ≤ 2 * N / L := by
        apply (Nat.le_div_iff_mul_le (by omega)).mpr
        have hk_eq : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (by omega)
        have : (L : ℤ) * (k.toNat : ℤ) ≤ 2 * (N : ℤ) := by rw [hk_eq]; omega
        have : L * k.toNat ≤ 2 * N := by exact_mod_cast this
        linarith
      exact mem_Icc.mpr ⟨by omega, hkle⟩
    have hinj : ∀ n₁ ∈ Spos, ∀ n₂ ∈ Spos, f n₁ = f n₂ → n₁ = n₂ := by
      intro n₁ h₁ n₂ h₂ heq
      obtain ⟨k₁, rfl⟩ := (mem_filter.mp (mem_filter.mp h₁).1).2
      obtain ⟨k₂, rfl⟩ := (mem_filter.mp (mem_filter.mp h₂).1).2
      have hk1 : 0 < k₁ := by have := (mem_filter.mp h₁).2; nlinarith
      have hk2 : 0 < k₂ := by have := (mem_filter.mp h₂).2; nlinarith
      dsimp [f] at heq
      rw [Int.mul_ediv_cancel_left k₁ (by omega : (L : ℤ) ≠ 0),
        Int.mul_ediv_cancel_left k₂ (by omega : (L : ℤ) ≠ 0)] at heq
      have : k₁ = k₂ := by omega
      rw [this]
    calc
      Spos.card = (Spos.image f).card := (card_image_of_injOn fun a ha b hb h => hinj a ha b hb h).symm
      _ ≤ (Icc 1 (2 * N / L)).card := card_le_card (fun m hm => by
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hm; exact hmaps n hn)
      _ = 2 * N / L := by simp
  have hneg_le : Sneg.card ≤ 2 * N / L := by
    let f : ℤ → ℕ := fun n => ((-n) / (L : ℤ)).toNat
    have hmaps : ∀ n ∈ Sneg, f n ∈ Icc 1 (2 * N / L) := by
      intro n hn
      have hS := (mem_filter.mp hn).1
      have hlt0 : n < 0 := (mem_filter.mp hn).2
      have hlo : -(2 * (N : ℤ)) < n := (mem_Ioo.mp (mem_erase.mp (mem_filter.mp hS).1).2).1
      have hdvd : (L : ℤ) ∣ -n := dvd_neg.mpr (mem_filter.mp hS).2
      obtain ⟨k, hk⟩ := hdvd
      have hkpos : 1 ≤ k := by nlinarith
      have hfk : f n = k.toNat := by
        dsimp [f]; rw [hk, Int.mul_ediv_cancel_left k (by omega : (L : ℤ) ≠ 0)]
      rw [hfk]
      have hkle : k.toNat ≤ 2 * N / L := by
        apply (Nat.le_div_iff_mul_le (by omega)).mpr
        have hk_eq : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (by omega)
        have : (L : ℤ) * (k.toNat : ℤ) ≤ 2 * (N : ℤ) := by rw [hk_eq, ← hk]; omega
        have : L * k.toNat ≤ 2 * N := by exact_mod_cast this
        linarith
      exact mem_Icc.mpr ⟨by omega, hkle⟩
    have hinj : ∀ n₁ ∈ Sneg, ∀ n₂ ∈ Sneg, f n₁ = f n₂ → n₁ = n₂ := by
      intro n₁ h₁ n₂ h₂ heq
      obtain ⟨k₁, hk1eq⟩ := dvd_neg.mpr (mem_filter.mp (mem_filter.mp h₁).1).2
      obtain ⟨k₂, hk2eq⟩ := dvd_neg.mpr (mem_filter.mp (mem_filter.mp h₂).1).2
      have hk1 : 0 < k₁ := by have := (mem_filter.mp h₁).2; nlinarith
      have hk2 : 0 < k₂ := by have := (mem_filter.mp h₂).2; nlinarith
      dsimp [f] at heq
      rw [hk1eq, hk2eq, Int.mul_ediv_cancel_left k₁ (by omega : (L : ℤ) ≠ 0),
        Int.mul_ediv_cancel_left k₂ (by omega : (L : ℤ) ≠ 0)] at heq
      have : k₁ = k₂ := by omega
      rw [this] at hk1eq
      linarith
    calc
      Sneg.card = (Sneg.image f).card := (card_image_of_injOn fun a ha b hb h => hinj a ha b hb h).symm
      _ ≤ (Icc 1 (2 * N / L)).card := card_le_card (fun m hm => by
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hm; exact hmaps n hn)
      _ = 2 * N / L := by simp
  have h2div : 2 * N / L + 2 * N / L ≤ 4 * N / L := by
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    have h1 := Nat.div_mul_le_self (2 * N) L
    have h2 : (2 * N / L + 2 * N / L) * L = (2 * N / L) * L + (2 * N / L) * L := by ring
    omega
  change S.card ≤ 4 * N / L
  rw [hpart, card_union_of_disjoint hdisj]
  omega

set_option maxHeartbeats 1600000 in
lemma restriction_set_bound :
    ∃ C_set : ℝ, 0 < C_set ∧
      ∀ d a N : ℕ, [NeZero N] → 1 ≤ a → a < d → d ≤ N → a.Coprime d →
      ∀ (B : Finset (ZMod N)), 1 ≤ B.card →
      ∀ (f : ZMod N → ℂ), (∀ r, r ∉ B → f r = 0) → (∀ r, ‖f r‖ ≤ 1) →
        PolynomialTransfer.E (fun x : ZMod N =>
          sieveBeta d a ⌊(N : ℝ) ^ (1 / 20 : ℝ)⌋₊ (x.val : ℤ) *
            ‖PolynomialTransfer.P f x‖ ^ 2) ≤
          C_set * (B.card : ℝ) ^ (7 / 5 : ℝ) := by
  obtain ⟨C_crude, hC_crude, hcrude⟩ := sieveBeta_crude_bound
  obtain ⟨C_w, hC_w, hw_bound⟩ := three_omega_div_totient_bound
  let C_log : ℝ := (331 : ℝ) ^ 11
  let C_set : ℝ := max C_crude (20 * C_w + 8 * C_w * C_log)
  refine ⟨C_set, lt_of_lt_of_le hC_crude (le_max_left _ _), ?_⟩
  intro d a N inst ha had hdN hcop B hB f hfsupp hfnorm
  have hN : 1 ≤ N := NeZero.pos N
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hBpos : (0 : ℝ) < (B.card : ℝ) := by exact_mod_cast hB
  have hB1 : (1 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hB
  let R : ℕ := ⌊(N : ℝ) ^ (1 / 20 : ℝ)⌋₊
  have hR1 : 1 ≤ R := Nat.le_floor (Real.one_le_rpow (by exact_mod_cast hN) (by norm_num))
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR1
  have hR_le : (R : ℝ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) := Nat.floor_le (by positivity)
  by_cases hlarge : (R : ℝ) ^ (2 / 5 : ℝ) ≤ (B.card : ℝ)
  · -- Case 1: Large B, use crude bound on sieveBeta + Parseval
    have hR10 : (R : ℝ) ^ (1 / 10 : ℝ) ≤ (B.card : ℝ) ^ (2 / 5 : ℝ) := by
      calc
        (R : ℝ) ^ (1 / 10 : ℝ) = ((R : ℝ) ^ (2 / 5 : ℝ)) ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_mul hRpos.le]; norm_num
        _ ≤ (B.card : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) hlarge (by norm_num)
        _ ≤ (B.card : ℝ) ^ (2 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num)
    have hpt : ∀ x : ZMod N,
        sieveBeta d a R (x.val : ℤ) * ‖PolynomialTransfer.P f x‖ ^ 2 ≤
        (C_crude * (B.card : ℝ) ^ (2 / 5 : ℝ)) * ‖PolynomialTransfer.P f x‖ ^ 2 := by
      intro x
      have hbx := hcrude d a N hN ha had hdN x.val x.val_lt
      have h1 : sieveBeta d a R (x.val : ℤ) ≤ C_crude * (B.card : ℝ) ^ (2 / 5 : ℝ) :=
        hbx.trans (mul_le_mul_of_nonneg_left hR10 hC_crude.le)
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have hparse : PolynomialTransfer.E (fun x : ZMod N => ‖PolynomialTransfer.P f x‖ ^ 2) ≤ (B.card : ℝ) := by
      rw [PolynomialTransfer.parseP]
      calc
        ∑ r : ZMod N, ‖f r‖ ^ 2 = ∑ r ∈ B, ‖f r‖ ^ 2 := by
          symm; apply sum_subset (subset_univ B)
          intro r _ hr; rw [hfsupp r hr, norm_zero, zero_pow (by decide)]
        _ ≤ ∑ _r ∈ B, (1 : ℝ) := sum_le_sum fun r _ => by
          have := pow_le_pow_left₀ (norm_nonneg _) (hfnorm r) 2; linarith
        _ = (B.card : ℝ) := by simp
    calc
      PolynomialTransfer.E (fun x : ZMod N => sieveBeta d a R (x.val : ℤ) * ‖PolynomialTransfer.P f x‖ ^ 2)
          ≤ PolynomialTransfer.E (fun x : ZMod N => (C_crude * (B.card : ℝ) ^ (2 / 5 : ℝ)) * ‖PolynomialTransfer.P f x‖ ^ 2) :=
        PolynomialTransfer.Emono hpt
      _ = (C_crude * (B.card : ℝ) ^ (2 / 5 : ℝ)) *
          PolynomialTransfer.E (fun x : ZMod N => ‖PolynomialTransfer.P f x‖ ^ 2) :=
        PolynomialTransfer.Emul _ _
      _ ≤ (C_crude * (B.card : ℝ) ^ (2 / 5 : ℝ)) * (B.card : ℝ) :=
        mul_le_mul_of_nonneg_left hparse (by positivity)
      _ = C_crude * ((B.card : ℝ) ^ (2 / 5 : ℝ) * (B.card : ℝ) ^ (1 : ℝ)) := by
        rw [Real.rpow_one]; ring
      _ = C_crude * (B.card : ℝ) ^ (7 / 5 : ℝ) := by
        rw [← Real.rpow_add hBpos]; norm_num
      _ ≤ C_set * (B.card : ℝ) ^ (7 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · -- Case 2: Small B, |B| < R^(2/5). Use discrete Fejer weight at L = 2 * N
    have hB_lt : (B.card : ℝ) < (R : ℝ) ^ (2 / 5 : ℝ) := not_le.mp hlarge
    obtain ⟨w, _, hw_le, hβ_exp⟩ := sieveBeta_fourier_expansion (d := d) (a := a) (R := R) hR1 hcop
    let L : ℕ := 2 * N
    have hL1 : 1 ≤ L := by omega
    have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
    let trig : ℤ → ℂ := fun n => ∑ b ∈ B, f b * phase (-(b.val : ℝ) * (n : ℝ) / (N : ℝ))
    have htrig_eq : ∀ x : ZMod N, PolynomialTransfer.P f x = trig (x.val : ℤ) := by
      intro x
      unfold PolynomialTransfer.P trig
      symm
      rw [← sum_subset (subset_univ B) (fun r _ hr => by rw [hfsupp r hr, zero_mul])]
      refine sum_congr rfl fun r _ => by rw [ch_eq_phase, Int.cast_natCast]
    have hfejer_dom : PolynomialTransfer.E (fun x : ZMod N =>
          sieveBeta d a R (x.val : ℤ) * ‖PolynomialTransfer.P f x‖ ^ 2) ≤
        4 * ((1 / (L : ℝ)) * ∑ n ∈ Ioo (-(L : ℤ)) (L : ℤ),
          fejerWeight L n * sieveBeta d a R n * ‖trig n‖ ^ 2) := by
      unfold PolynomialTransfer.E
      have h1 : (∑ x : ZMod N, sieveBeta d a R (x.val : ℤ) * ‖PolynomialTransfer.P f x‖ ^ 2) / (N : ℝ) ≤
          (2 / (N : ℝ)) * ∑ x : ZMod N,
            fejerWeight L (x.val : ℤ) * sieveBeta d a R (x.val : ℤ) * ‖trig (x.val : ℤ)‖ ^ 2 := by
        rw [div_eq_mul_inv, mul_comm _ (N : ℝ)⁻¹, show (2 : ℝ) / (N : ℝ) = (N : ℝ)⁻¹ * 2 by ring,
          mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [mul_sum]
        refine sum_le_sum fun x _ => ?_
        rw [htrig_eq x]
        have hfw : (1 / 2 : ℝ) ≤ fejerWeight L (x.val : ℤ) := fejerWeight_ge_half hN x.val_lt
        have hβ0 : 0 ≤ sieveBeta d a R (x.val : ℤ) := sieveBeta_nonneg d a R (x.val : ℤ)
        have ht0 : 0 ≤ ‖trig (x.val : ℤ)‖ ^ 2 := by positivity
        have hprod : 0 ≤ sieveBeta d a R (x.val : ℤ) * ‖trig (x.val : ℤ)‖ ^ 2 := mul_nonneg hβ0 ht0
        nlinarith only [hfw, hprod]
      have h2 : ∑ x : ZMod N,
            fejerWeight L (x.val : ℤ) * sieveBeta d a R (x.val : ℤ) * ‖trig (x.val : ℤ)‖ ^ 2 ≤
          ∑ n ∈ Ioo (-(L : ℤ)) (L : ℤ),
            fejerWeight L n * sieveBeta d a R n * ‖trig n‖ ^ 2 := by
        let emb : ZMod N → ℤ := fun x => (x.val : ℤ)
        have hinj : ∀ x₁ ∈ (univ : Finset (ZMod N)), ∀ x₂ ∈ (univ : Finset (ZMod N)),
            emb x₁ = emb x₂ → x₁ = x₂ := by
          intro x₁ _ x₂ _ heq
          dsimp [emb] at heq
          exact ZMod.val_injective N (by exact_mod_cast heq)
        rw [← sum_image (f := fun n : ℤ => fejerWeight L n * sieveBeta d a R n * ‖trig n‖ ^ 2) hinj]
        apply sum_le_sum_of_subset_of_nonneg
        · intro n hn
          obtain ⟨x, _, rfl⟩ := mem_image.mp hn
          have hlt := x.val_lt
          exact mem_Ioo.mpr ⟨by dsimp [emb, L]; omega, by dsimp [emb, L]; omega⟩
        · intro n _ _
          have hfw := fejerWeight_nonneg L n
          have hβ0 : 0 ≤ sieveBeta d a R n := sieveBeta_nonneg d a R n
          positivity
      have h4L : 4 * (1 / (L : ℝ)) = 2 / (N : ℝ) := by
        dsimp [L]; push_cast; field_simp; ring
      rw [← mul_assoc, h4L]
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    -- Expand via sieveBeta_fourier_expansion and fejer_identity
    have hexpand : ((1 / (L : ℝ)) * ∑ n ∈ Ioo (-(L : ℤ)) (L : ℤ),
          fejerWeight L n * sieveBeta d a R n * ‖trig n‖ ^ 2) ≤
        C_w * ∑ q ∈ SF d (R ^ 2), (q : ℝ) ^ (-(4 / 5 : ℝ)) *
          ∑ r ∈ reducedRes q, ∑ b₁ ∈ B, ∑ b₂ ∈ B,
            fejerKernel L (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ) - (r : ℝ) / (q : ℝ)) := by
      let LHS_R : ℝ := (1 / (L : ℝ)) * ∑ n ∈ Ioo (-(L : ℤ)) (L : ℤ),
        fejerWeight L n * sieveBeta d a R n * ‖trig n‖ ^ 2
      have hLHS_nonneg : 0 ≤ LHS_R := by
        dsimp [LHS_R]
        apply mul_nonneg (by positivity)
        exact sum_nonneg fun n _ => mul_nonneg (mul_nonneg (fejerWeight_nonneg L n)
          (sieveBeta_nonneg d a R n)) (by positivity)
      have hC_eq : (LHS_R : ℂ) =
          ∑ q ∈ SF d (R ^ 2), ∑ r ∈ reducedRes q, ∑ b₁ ∈ B, ∑ b₂ ∈ B,
            w q r * f b₁ * conj (f b₂) *
              (fejerKernel L (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ) - (r : ℝ) / (q : ℝ)) : ℂ) := by
        have hstep1 : (LHS_R : ℂ) =
            ((1 / (L : ℝ) : ℝ) : ℂ) * ∑ n ∈ Ioo (-(L : ℤ)) (L : ℤ),
              ∑ q ∈ SF d (R ^ 2), ∑ r ∈ reducedRes q, ∑ b₁ ∈ B, ∑ b₂ ∈ B,
                w q r * f b₁ * conj (f b₂) *
                  ((fejerWeight L n : ℂ) *
                    phase ((n : ℝ) * (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ) - (r : ℝ) / (q : ℝ)))) := by
          dsimp [LHS_R]
          rw [Complex.ofReal_mul, Complex.ofReal_sum]
          congr 1
          refine sum_congr rfl fun n _ => ?_
          rw [Complex.ofReal_mul, Complex.ofReal_mul, hβ_exp n]
          have htrig_sq : ((‖trig n‖ ^ 2 : ℝ) : ℂ) =
              ∑ b₁ ∈ B, ∑ b₂ ∈ B, f b₁ * conj (f b₂) *
                phase ((n : ℝ) * (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ))) := by
            rw [Complex.ofReal_pow, ← Complex.mul_conj']
            dsimp [trig]
            rw [map_sum, sum_mul_sum]
            refine sum_congr rfl fun b₁ _ => sum_congr rfl fun b₂ _ => ?_
            rw [map_mul, ← phase_neg]
            have hph : phase (-(b₁.val : ℝ) * (n : ℝ) / (N : ℝ)) *
                phase (-(-(b₂.val : ℝ) * (n : ℝ) / (N : ℝ))) =
                phase ((n : ℝ) * (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ))) := by
              rw [← phase_add]; congr 1; ring
            calc
              f b₁ * phase (-(b₁.val : ℝ) * (n : ℝ) / (N : ℝ)) *
                  (conj (f b₂) * phase (-(-(b₂.val : ℝ) * (n : ℝ) / (N : ℝ))))
                  = f b₁ * conj (f b₂) *
                    (phase (-(b₁.val : ℝ) * (n : ℝ) / (N : ℝ)) *
                      phase (-(-(b₂.val : ℝ) * (n : ℝ) / (N : ℝ)))) := by ring
              _ = _ := by rw [hph]
          rw [htrig_sq, mul_sum (a := (fejerWeight L n : ℂ)), sum_mul]
          refine sum_congr rfl fun q _ => ?_
          rw [mul_sum (a := (fejerWeight L n : ℂ)), sum_mul]
          refine sum_congr rfl fun r _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun b₁ _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun b₂ _ => ?_
          have hph2 : phase (-(r : ℝ) * (n : ℝ) / (q : ℝ)) *
              phase ((n : ℝ) * (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ))) =
              phase ((n : ℝ) * (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ) - (r : ℝ) / (q : ℝ))) := by
            rw [← phase_add]; congr 1; ring
          calc
            (fejerWeight L n : ℂ) * (w q r * phase (-(r : ℝ) * (n : ℝ) / (q : ℝ))) *
                (f b₁ * conj (f b₂) * phase ((n : ℝ) * (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ))))
                = w q r * f b₁ * conj (f b₂) * ((fejerWeight L n : ℂ) *
                  (phase (-(r : ℝ) * (n : ℝ) / (q : ℝ)) *
                    phase ((n : ℝ) * (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ))))) := by ring
            _ = _ := by rw [hph2]
        rw [hstep1]
        rw [sum_comm, mul_sum]
        refine sum_congr rfl fun q _ => ?_
        rw [sum_comm, mul_sum]
        refine sum_congr rfl fun r _ => ?_
        rw [sum_comm, mul_sum]
        refine sum_congr rfl fun b₁ _ => ?_
        rw [sum_comm, mul_sum]
        refine sum_congr rfl fun b₂ _ => ?_
        rw [← mul_sum, ← mul_assoc, mul_comm (((1 / (L : ℝ) : ℝ) : ℂ)), mul_assoc,
          fejer_identity hL1]
      have hnorm : LHS_R = ‖(LHS_R : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hLHS_nonneg]
      rw [show (1 / (L : ℝ)) * ∑ n ∈ Ioo (-(L : ℤ)) (L : ℤ),
          fejerWeight L n * sieveBeta d a R n * ‖trig n‖ ^ 2 = LHS_R from rfl,
        hnorm, hC_eq, mul_sum]
      refine (norm_sum_le _ _).trans (sum_le_sum fun q hq => ?_)
      have hq1 : 1 ≤ q := (mem_Icc.mp (mem_filter.mp hq).1).1
      have hqsq : Squarefree q := (mem_filter.mp hq).2.1
      rw [← mul_assoc, mul_sum]
      refine (norm_sum_le _ _).trans (sum_le_sum fun r hr => ?_)
      rw [mul_sum]
      refine (norm_sum_le _ _).trans (sum_le_sum fun b₁ _ => ?_)
      rw [mul_sum]
      refine (norm_sum_le _ _).trans (sum_le_sum fun b₂ _ => ?_)
      rw [norm_mul, norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (fejerKernel_nonneg L _)]
      have hwb : ‖w q r‖ ≤ C_w * (q : ℝ) ^ (-(4 / 5 : ℝ)) :=
        (hw_le q hq r hr).trans (hw_bound q hq1 hqsq)
      have hprod1 : ‖w q r‖ * ‖f b₁‖ * ‖f b₂‖ ≤ C_w * (q : ℝ) ^ (-(4 / 5 : ℝ)) := by
        calc
          ‖w q r‖ * ‖f b₁‖ * ‖f b₂‖ ≤ (C_w * (q : ℝ) ^ (-(4 / 5 : ℝ))) * 1 * 1 :=
            mul_le_mul (mul_le_mul hwb (hfnorm b₁) (norm_nonneg _) (by positivity))
              (hfnorm b₂) (norm_nonneg _) (by positivity)
          _ = C_w * (q : ℝ) ^ (-(4 / 5 : ℝ)) := by ring
      calc
        ‖w q r‖ * ‖f b₁‖ * ‖f b₂‖ * fejerKernel L _
            ≤ (C_w * (q : ℝ) ^ (-(4 / 5 : ℝ))) * fejerKernel L _ :=
          mul_le_mul_of_nonneg_right hprod1 (fejerKernel_nonneg L _)
        _ = C_w * (q : ℝ) ^ (-(4 / 5 : ℝ)) * fejerKernel L _ := by ring
    -- Split SF d (R^2) into q > B.card (large q) and q ≤ B.card (small q)
    let Sbig := (SF d (R ^ 2)).filter (fun q => B.card < q)
    let Ssmall := (SF d (R ^ 2)).filter (fun q => ¬ B.card < q)
    have hsplit_q : ∑ q ∈ SF d (R ^ 2), (q : ℝ) ^ (-(4 / 5 : ℝ)) *
          ∑ r ∈ reducedRes q, ∑ b₁ ∈ B, ∑ b₂ ∈ B,
            fejerKernel L (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ) - (r : ℝ) / (q : ℝ)) =
        (∑ q ∈ Sbig, (q : ℝ) ^ (-(4 / 5 : ℝ)) *
          ∑ r ∈ reducedRes q, ∑ b₁ ∈ B, ∑ b₂ ∈ B,
            fejerKernel L (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ) - (r : ℝ) / (q : ℝ))) +
        (∑ q ∈ Ssmall, (q : ℝ) ^ (-(4 / 5 : ℝ)) *
          ∑ r ∈ reducedRes q, ∑ b₁ ∈ B, ∑ b₂ ∈ B,
            fejerKernel L (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ) - (r : ℝ) / (q : ℝ))) :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    -- Subcase 2a: Large q > B.card
    have hbig : ∑ q ∈ Sbig, (q : ℝ) ^ (-(4 / 5 : ℝ)) *
          ∑ r ∈ reducedRes q, ∑ b₁ ∈ B, ∑ b₂ ∈ B,
            fejerKernel L (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ) - (r : ℝ) / (q : ℝ)) ≤
        4 * (B.card : ℝ) ^ (7 / 5 : ℝ) := by
      let Pairs := Sbig.sigma (fun q => reducedRes q)
      have hsep : ∀ x ∈ Pairs, ∀ y ∈ Pairs, x ≠ y →
          (1 / (R : ℝ) ^ 4) ≤ distInt ((x.2 : ℝ) / (x.1 : ℝ) - (y.2 : ℝ) / (y.1 : ℝ)) := by
        intro ⟨q₁, r₁⟩ hx ⟨q₂, r₂⟩ hy hne
        have hq1_sf := (mem_filter.mp (mem_sigma.mp hx).1).1
        have hq2_sf := (mem_filter.mp (mem_sigma.mp hy).1).1
        have hq1_1 : 1 ≤ q₁ := (mem_Icc.mp (mem_filter.mp hq1_sf).1).1
        have hq1_le : q₁ ≤ R ^ 2 := (mem_Icc.mp (mem_filter.mp hq1_sf).1).2
        have hq2_1 : 1 ≤ q₂ := (mem_Icc.mp (mem_filter.mp hq2_sf).1).1
        have hq2_le : q₂ ≤ R ^ 2 := (mem_Icc.mp (mem_filter.mp hq2_sf).1).2
        have hr1_lt : r₁ < q₁ := mem_range.mp (mem_filter.mp (mem_sigma.mp hx).2).1
        have hr1_cop : r₁.Coprime q₁ := (mem_filter.mp (mem_sigma.mp hx).2).2
        have hr2_lt : r₂ < q₂ := mem_range.mp (mem_filter.mp (mem_sigma.mp hy).2).1
        have hr2_cop : r₂.Coprime q₂ := (mem_filter.mp (mem_sigma.mp hy).2).2
        let k : ℤ := round ((r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ))
        unfold distInt
        have hnum_ne : (r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) ≠ 0 := by
          intro h0
          have hrat : (r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ) = (k : ℝ) := by
            have hq1ne : (q₁ : ℝ) ≠ 0 := by exact_mod_cast (by omega : q₁ ≠ 0)
            have hq2ne : (q₂ : ℝ) ≠ 0 := by exact_mod_cast (by omega : q₂ ≠ 0)
            have h0r : (r₁ : ℝ) * (q₂ : ℝ) - (r₂ : ℝ) * (q₁ : ℝ) - (k : ℝ) * ((q₁ : ℝ) * (q₂ : ℝ)) = 0 := by
              exact_mod_cast h0
            field_simp; linarith
          have hbound1 : (r₁ : ℝ) / (q₁ : ℝ) < 1 := (div_lt_one (by exact_mod_cast hq1_1)).mpr (by exact_mod_cast hr1_lt)
          have hbound2 : (r₂ : ℝ) / (q₂ : ℝ) < 1 := (div_lt_one (by exact_mod_cast hq2_1)).mpr (by exact_mod_cast hr2_lt)
          have hlo : (-1 : ℝ) < (k : ℝ) := by linarith [div_nonneg (Nat.cast_nonneg (α := ℝ) r₁) (Nat.cast_nonneg (α := ℝ) q₁)]
          have hhi : (k : ℝ) < 1 := by linarith [div_nonneg (Nat.cast_nonneg (α := ℝ) r₂) (Nat.cast_nonneg (α := ℝ) q₂)]
          have hk0 : k = 0 := by
            have h1 : (-1 : ℤ) < k := by exact_mod_cast hlo
            have h2 : k < (1 : ℤ) := by exact_mod_cast hhi
            omega
          rw [hk0, zero_mul, sub_zero] at h0
          have heq_nat : r₁ * q₂ = r₂ * q₁ := by exact_mod_cast (show (r₁ : ℤ) * (q₂ : ℤ) = (r₂ : ℤ) * (q₁ : ℤ) by linarith)
          have hq1_dvd : q₁ ∣ q₂ := hr1_cop.symm.dvd_of_dvd_mul_left ⟨r₂, by linarith⟩
          have hq2_dvd : q₂ ∣ q₁ := hr2_cop.symm.dvd_of_dvd_mul_left ⟨r₁, by linarith⟩
          have hq_eq : q₁ = q₂ := Nat.dvd_antisymm hq1_dvd hq2_dvd
          have hr_eq : r₁ = r₂ := Nat.eq_of_mul_eq_mul_right (by omega) (hq_eq ▸ heq_nat)
          exact hne (Sigma.ext hq_eq (heq_of_eq hr_eq))
        have habs_ge1 : (1 : ℝ) ≤ |((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℝ)| := by
          have : (1 : ℤ) ≤ |(r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ))| :=
            Int.one_le_abs hnum_ne
          exact_mod_cast this
        have hqprod : (q₁ : ℝ) * (q₂ : ℝ) ≤ (R : ℝ) ^ 4 := by
          have h1 : (q₁ : ℝ) ≤ (R : ℝ) ^ 2 := by exact_mod_cast hq1_le
          have h2 : (q₂ : ℝ) ≤ (R : ℝ) ^ 2 := by exact_mod_cast hq2_le
          calc
            (q₁ : ℝ) * (q₂ : ℝ) ≤ (R : ℝ) ^ 2 * (R : ℝ) ^ 2 :=
              mul_le_mul h1 h2 (by positivity) (by positivity)
            _ = (R : ℝ) ^ 4 := by ring
        have heq_frac : |(r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ) - (k : ℝ)| =
            |((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℝ)| /
              ((q₁ : ℝ) * (q₂ : ℝ)) := by
          have hq1pos : (0 : ℝ) < (q₁ : ℝ) := by exact_mod_cast hq1_1
          have hq2pos : (0 : ℝ) < (q₂ : ℝ) := by exact_mod_cast hq2_1
          rw [← abs_of_pos (mul_pos hq1pos hq2pos), ← abs_div]
          congr 1; push_cast; field_simp
        rw [heq_frac]
        exact (one_div_le_one_div_of_le (by positivity) hqprod).trans
          (div_le_div_of_nonneg_right habs_ge1 (by positivity))
      have hLδ : 1 ≤ (L : ℝ) * (1 / (R : ℝ) ^ 4) := by
        have hR4 : (R : ℝ) ^ 4 ≤ (L : ℝ) := by
          have h1 : (R : ℝ) ^ 4 ≤ ((N : ℝ) ^ (1 / 20 : ℝ)) ^ 4 := pow_le_pow_left₀ hRpos.le hR_le 4
          have h2 : ((N : ℝ) ^ (1 / 20 : ℝ)) ^ 4 = (N : ℝ) ^ (1 / 5 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num
          have h3 : (N : ℝ) ^ (1 / 5 : ℝ) ≤ (N : ℝ) := by
            conv_rhs => rw [← Real.rpow_one (N : ℝ)]
            exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)
          have h4 : (N : ℝ) ≤ (L : ℝ) := by dsimp [L]; push_cast; linarith
          linarith
        rw [mul_one_div, one_le_div (by positivity)]
        exact hR4
      have hbound_q : ∑ q ∈ Sbig, (q : ℝ) ^ (-(4 / 5 : ℝ)) *
            ∑ r ∈ reducedRes q, ∑ b₁ ∈ B, ∑ b₂ ∈ B,
              fejerKernel L (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ) - (r : ℝ) / (q : ℝ)) ≤
          (B.card : ℝ) ^ (-(4 / 5 : ℝ)) *
            ∑ b₁ ∈ B, ∑ b₂ ∈ B, ∑ x ∈ Pairs,
              fejerKernel L (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ) - (x.2 : ℝ) / (x.1 : ℝ)) := by
        have hstep : ∑ q ∈ Sbig, (q : ℝ) ^ (-(4 / 5 : ℝ)) *
              ∑ r ∈ reducedRes q, ∑ b₁ ∈ B, ∑ b₂ ∈ B,
                fejerKernel L (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ) - (r : ℝ) / (q : ℝ)) ≤
            (B.card : ℝ) ^ (-(4 / 5 : ℝ)) *
              ∑ q ∈ Sbig, ∑ r ∈ reducedRes q, ∑ b₁ ∈ B, ∑ b₂ ∈ B,
                fejerKernel L (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ) - (r : ℝ) / (q : ℝ)) := by
          rw [mul_sum]
          refine sum_le_sum fun q hq => ?_
          have hqgt : B.card < q := (mem_filter.mp hq).2
          have hqpow : (q : ℝ) ^ (-(4 / 5 : ℝ)) ≤ (B.card : ℝ) ^ (-(4 / 5 : ℝ)) := by
            rw [Real.rpow_neg (by positivity), Real.rpow_neg hBpos.le]
            exact inv_anti₀ (Real.rpow_pos_of_pos hBpos _)
              (Real.rpow_le_rpow hBpos.le (by exact_mod_cast hqgt.le) (by norm_num))
          exact mul_le_mul_of_nonneg_right hqpow
            (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => fejerKernel_nonneg L _)
        refine hstep.trans_eq ?_
        congr 1
        rw [Finset.sum_sigma']
        rw [sum_comm]
        refine sum_congr rfl fun b₁ _ => sum_comm
      have hsep_all : ∑ b₁ ∈ B, ∑ b₂ ∈ B, ∑ x ∈ Pairs,
            fejerKernel L (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ) - (x.2 : ℝ) / (x.1 : ℝ)) ≤
          (B.card : ℝ) ^ 2 * 4 := by
        calc
          ∑ b₁ ∈ B, ∑ b₂ ∈ B, ∑ x ∈ Pairs,
              fejerKernel L (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ) - (x.2 : ℝ) / (x.1 : ℝ))
              ≤ ∑ _b₁ ∈ B, ∑ _b₂ ∈ B, (4 : ℝ) :=
            sum_le_sum fun b₁ _ => sum_le_sum fun b₂ _ =>
              fejer_separated_sum_le Pairs (fun x => (x.2 : ℝ) / (x.1 : ℝ)) hL1
                (by positivity) hLδ hsep (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ))
          _ = (B.card : ℝ) ^ 2 * 4 := by simp [sq]; ring
      have hBexp : (B.card : ℝ) ^ (-(4 / 5 : ℝ)) * (B.card : ℝ) ^ 2 ≤ (B.card : ℝ) ^ (7 / 5 : ℝ) := by
        rw [← Real.rpow_natCast (B.card : ℝ) 2, ← Real.rpow_add hBpos]
        exact Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num)
      calc
        _ ≤ (B.card : ℝ) ^ (-(4 / 5 : ℝ)) * ((B.card : ℝ) ^ 2 * 4) :=
          hbound_q.trans (mul_le_mul_of_nonneg_left hsep_all (by positivity))
        _ = 4 * ((B.card : ℝ) ^ (-(4 / 5 : ℝ)) * (B.card : ℝ) ^ 2) := by ring
        _ ≤ 4 * (B.card : ℝ) ^ (7 / 5 : ℝ) := mul_le_mul_of_nonneg_left hBexp (by norm_num)
    -- Subcase 2b: Small q ≤ B.card
    have hsmall : ∑ q ∈ Ssmall, (q : ℝ) ^ (-(4 / 5 : ℝ)) *
          ∑ r ∈ reducedRes q, ∑ b₁ ∈ B, ∑ b₂ ∈ B,
            fejerKernel L (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ) - (r : ℝ) / (q : ℝ)) ≤
        (1 + 2 * C_log) * (B.card : ℝ) ^ (7 / 5 : ℝ) := by
      let T : ℝ := ∑ q ∈ Icc 1 B.card, (1 / (q : ℝ)) *
        ∑ r ∈ range q, ∑ b₁ ∈ B, ∑ b₂ ∈ B,
          fejerKernel L (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ) - (r : ℝ) / (q : ℝ))
      have hstep1 : ∑ q ∈ Ssmall, (q : ℝ) ^ (-(4 / 5 : ℝ)) *
            ∑ r ∈ reducedRes q, ∑ b₁ ∈ B, ∑ b₂ ∈ B,
              fejerKernel L (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ) - (r : ℝ) / (q : ℝ)) ≤
          (B.card : ℝ) ^ (1 / 5 : ℝ) * T := by
        rw [mul_sum]
        have hsub_q : Ssmall ⊆ Icc 1 B.card := by
          intro q hq
          have hq1 := (mem_Icc.mp (mem_filter.mp (mem_filter.mp hq).1).1).1
          have hqB : q ≤ B.card := not_lt.mp (mem_filter.mp hq).2
          exact mem_Icc.mpr ⟨hq1, hqB⟩
        refine (sum_le_sum fun q hq => ?_).trans
          (sum_le_sum_of_subset_of_nonneg hsub_q fun q _ _ => by
            apply mul_nonneg (by positivity)
            exact mul_nonneg (by positivity)
              (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => fejerKernel_nonneg L _))
        have hq1 : 1 ≤ q := (mem_Icc.mp (hsub_q hq)).1
        have hqB : q ≤ B.card := (mem_Icc.mp (hsub_q hq)).2
        have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
        have hqpow : (q : ℝ) ^ (-(4 / 5 : ℝ)) ≤ (B.card : ℝ) ^ (1 / 5 : ℝ) * (1 / (q : ℝ)) := by
          have h1 : (q : ℝ) ^ (-(4 / 5 : ℝ)) = (q : ℝ) ^ (1 / 5 : ℝ) * (1 / (q : ℝ)) := by
            rw [one_div (q : ℝ), ← Real.rpow_neg_one (q : ℝ), ← Real.rpow_add hqpos]; norm_num
          rw [h1]
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow hqpos.le (by exact_mod_cast hqB) (by norm_num)) (by positivity)
        have hsub_r : ∑ r ∈ reducedRes q, ∑ b₁ ∈ B, ∑ b₂ ∈ B,
              fejerKernel L (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ) - (r : ℝ) / (q : ℝ)) ≤
            ∑ r ∈ range q, ∑ b₁ ∈ B, ∑ b₂ ∈ B,
              fejerKernel L (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ) - (r : ℝ) / (q : ℝ)) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ =>
            sum_nonneg fun _ _ => sum_nonneg fun _ _ => fejerKernel_nonneg L _
        rw [← mul_assoc]
        exact mul_le_mul hqpow hsub_r
          (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => fejerKernel_nonneg L _)
          (by positivity)
      -- Reverse fejer_identity on T
      let divS : ℤ → ℝ := fun n => ∑ q ∈ Icc 1 B.card, if (q : ℤ) ∣ n then (1 : ℝ) else 0
      let trig1 : ℤ → ℂ := fun n => ∑ b ∈ B, phase (-(b.val : ℝ) * (n : ℝ) / (N : ℝ))
      have hT_eq : T = (1 / (L : ℝ)) * ∑ n ∈ Ioo (-(L : ℤ)) (L : ℤ),
          fejerWeight L n * ‖trig1 n‖ ^ 2 * divS n := by
        apply Complex.ofReal_injective
        change ((∑ q ∈ Icc 1 B.card, (1 / (q : ℝ)) *
          ∑ r ∈ range q, ∑ b₁ ∈ B, ∑ b₂ ∈ B,
            fejerKernel L (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ) - (r : ℝ) / (q : ℝ)) : ℝ) : ℂ) = _
        rw [Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_sum]
        have hrhs : ((1 / (L : ℝ) : ℝ) : ℂ) * ∑ n ∈ Ioo (-(L : ℤ)) (L : ℤ),
              ((fejerWeight L n * ‖trig1 n‖ ^ 2 * divS n : ℝ) : ℂ) =
            ∑ q ∈ Icc 1 B.card, ((1 / (q : ℝ) : ℝ) : ℂ) *
              ∑ r ∈ range q, ∑ b₁ ∈ B, ∑ b₂ ∈ B,
                ((1 / (L : ℝ) : ℝ) : ℂ) * ∑ n ∈ Ioo (-(L : ℤ)) (L : ℤ),
                  (fejerWeight L n : ℂ) *
                    phase ((n : ℝ) * (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ) - (r : ℝ) / (q : ℝ))) := by
          have hstep_n : ∀ n ∈ Ioo (-(L : ℤ)) (L : ℤ),
              ((fejerWeight L n * ‖trig1 n‖ ^ 2 * divS n : ℝ) : ℂ) =
              ∑ q ∈ Icc 1 B.card, ((1 / (q : ℝ) : ℝ) : ℂ) *
                ∑ r ∈ range q, ∑ b₁ ∈ B, ∑ b₂ ∈ B,
                  (fejerWeight L n : ℂ) *
                    phase ((n : ℝ) * (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ) - (r : ℝ) / (q : ℝ))) := by
            intro n _
            rw [Complex.ofReal_mul, Complex.ofReal_mul]
            have hdivC : (divS n : ℂ) = ∑ q ∈ Icc 1 B.card, ((1 / (q : ℝ) : ℝ) : ℂ) *
                ∑ r ∈ range q, phase (-(r : ℝ) * (n : ℝ) / (q : ℝ)) := by
              dsimp [divS]
              rw [Complex.ofReal_sum]
              refine sum_congr rfl fun q hq => ?_
              rw [phase_orthog (mem_Icc.mp hq).1 n]
              by_cases hd : (q : ℤ) ∣ n <;> simp [hd]
            have htrig1_sq : ((‖trig1 n‖ ^ 2 : ℝ) : ℂ) =
                ∑ b₁ ∈ B, ∑ b₂ ∈ B, phase ((n : ℝ) * (-((b₁.val : ℝ) - (b₂.val : ℝ)) / (N : ℝ))) := by
              rw [Complex.ofReal_pow, ← Complex.mul_conj']
              dsimp [trig1]
              rw [map_sum, sum_mul_sum]
              refine sum_congr rfl fun b₁ _ => sum_congr rfl fun b₂ _ => ?_
              rw [← phase_neg, ← phase_add]; congr 1; ring
            rw [hdivC, htrig1_sq, mul_sum]
            refine sum_congr rfl fun q _ => ?_
            rw [mul_left_comm, mul_sum]
            congr 1
            refine sum_congr rfl fun r _ => ?_
            rw [mul_assoc, sum_mul, mul_sum]
            refine sum_congr rfl fun b₁ _ => ?_
            rw [sum_mul, mul_sum]
            refine sum_congr rfl fun b₂ _ => ?_
            rw [← phase_add]
            congr 1; congr 1; ring
          rw [sum_congr rfl hstep_n, sum_comm, mul_sum]
          refine sum_congr rfl fun q _ => ?_
          rw [← mul_sum, mul_left_comm]
          congr 1
          rw [sum_comm, mul_sum]
          refine sum_congr rfl fun r _ => ?_
          rw [sum_comm, mul_sum]
          refine sum_congr rfl fun b₁ _ => ?_
          rw [sum_comm, mul_sum]
        rw [hrhs]
        refine sum_congr rfl fun q _ => ?_
        rw [Complex.ofReal_mul, Complex.ofReal_sum]
        congr 1
        refine sum_congr rfl fun r _ => ?_
        rw [Complex.ofReal_sum]
        refine sum_congr rfl fun b₁ _ => ?_
        rw [Complex.ofReal_sum]
        refine sum_congr rfl fun b₂ _ => ?_
        exact (fejer_identity hL1 _).symm
      -- Split n = 0 vs n ≠ 0
      let I0 := (Ioo (-(L : ℤ)) (L : ℤ)).erase 0
      have h0mem : (0 : ℤ) ∈ Ioo (-(L : ℤ)) (L : ℤ) := mem_Ioo.mpr ⟨by omega, by omega⟩
      have hsplit_0 : T = (1 / (L : ℝ)) * (fejerWeight L 0 * ‖trig1 0‖ ^ 2 * divS 0) +
          (1 / (L : ℝ)) * ∑ n ∈ I0, fejerWeight L n * ‖trig1 n‖ ^ 2 * divS n := by
        rw [hT_eq, ← Finset.add_sum_erase _ _ h0mem, mul_add]
      have hterm0 : (1 / (L : ℝ)) * (fejerWeight L 0 * ‖trig1 0‖ ^ 2 * divS 0) ≤ (B.card : ℝ) := by
        have ht0 : ‖trig1 0‖ = (B.card : ℝ) := by
          dsimp [trig1]; simp [phase_zero]
        have hd0 : divS 0 = (B.card : ℝ) := by
          dsimp [divS]; simp
        rw [fejerWeight_zero, one_mul, ht0, hd0]
        have hB2_le : (B.card : ℝ) ^ 2 ≤ (L : ℝ) := by
          have h1 : (B.card : ℝ) ^ 2 ≤ ((R : ℝ) ^ (2 / 5 : ℝ)) ^ 2 :=
            pow_le_pow_left₀ hBpos.le hB_lt.le 2
          have h2 : ((R : ℝ) ^ (2 / 5 : ℝ)) ^ 2 ≤ (R : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hRpos.le]
            conv_rhs => rw [← Real.rpow_one (R : ℝ)]
            exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hR1) (by norm_num)
          have h3 : (R : ℝ) ≤ (N : ℝ) := by
            refine hR_le.trans ?_
            conv_rhs => rw [← Real.rpow_one (N : ℝ)]
            exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)
          have h4 : (N : ℝ) ≤ (L : ℝ) := by dsimp [L]; push_cast; linarith
          linarith
        calc
          (1 / (L : ℝ)) * ((B.card : ℝ) ^ 2 * (B.card : ℝ))
              = ((B.card : ℝ) ^ 2 / (L : ℝ)) * (B.card : ℝ) := by ring
          _ ≤ 1 * (B.card : ℝ) :=
            mul_le_mul_of_nonneg_right ((div_le_one hLpos).mpr hB2_le) hBpos.le
          _ = (B.card : ℝ) := one_mul _
      -- Bound the nonzero sum by Holder (6/5, 6) + Parseval + Ruzsa LCM moment
      have hterm_nz : (1 / (L : ℝ)) * ∑ n ∈ I0, fejerWeight L n * ‖trig1 n‖ ^ 2 * divS n ≤
          2 * C_log * (B.card : ℝ) ^ (6 / 5 : ℝ) := by
        have hdrop : ∑ n ∈ I0, fejerWeight L n * ‖trig1 n‖ ^ 2 * divS n ≤
            ∑ n ∈ I0, ‖trig1 n‖ ^ 2 * divS n := by
          refine sum_le_sum fun n _ => ?_
          have h1 : fejerWeight L n * ‖trig1 n‖ ^ 2 ≤ 1 * ‖trig1 n‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (fejerWeight_le_one L n) (by positivity)
          have hdiv0 : 0 ≤ divS n := sum_nonneg fun q _ => by split_ifs <;> norm_num
          nlinarith
        have hconj : Real.HolderConjugate (6 / 5 : ℝ) (6 : ℝ) :=
          Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
        have hholder := Real.inner_le_Lp_mul_Lq I0 (fun n => ‖trig1 n‖ ^ 2) divS hconj
        -- Bound L^(6/5) of ‖trig1 n‖^2
        have htrig_parse : ∑ n ∈ I0, ‖trig1 n‖ ^ 2 ≤ 4 * (N : ℝ) * (B.card : ℝ) := by
          have hsub : I0 ⊆ Ico (-(2 * (N : ℤ))) (2 * (N : ℤ)) := by
            intro n hn
            have hm := mem_Ioo.mp (mem_erase.mp hn).2
            exact mem_Ico.mpr ⟨by dsimp [L] at hm; omega, by dsimp [L] at hm; omega⟩
          have h1 : ∑ n ∈ I0, ‖trig1 n‖ ^ 2 ≤ ∑ n ∈ Ico (-(2 * (N : ℤ))) (2 * (N : ℤ)), ‖trig1 n‖ ^ 2 :=
            sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
          have hper : ∀ k : ℤ, ∑ j ∈ range N, ‖trig1 (k * (N : ℤ) + (j : ℤ))‖ ^ 2 = (N : ℝ) * (B.card : ℝ) := by
            intro k
            have hshift : ∀ j ∈ range N, ‖trig1 (k * (N : ℤ) + (j : ℤ))‖ ^ 2 =
                ‖PolynomialTransfer.P (fun r : ZMod N => if r ∈ B then (1 : ℂ) else 0) (j : ZMod N)‖ ^ 2 := by
              intro j hj
              have hval : ((j : ZMod N).val : ℤ) = (j : ℤ) := by
                rw [ZMod.val_natCast_of_lt (mem_range.mp hj)]
              congr 1; congr 1
              unfold PolynomialTransfer.P trig1
              rw [← sum_subset (subset_univ B) (fun r _ hr => by simp [hr])]
              refine sum_congr rfl fun r hr => ?_
              dsimp only
              rw [ite_eq_left hr, one_mul, ch_eq_phase]
              have hvalr : ((j : ZMod N).val : ℝ) = (j : ℝ) := by exact_mod_cast hval
              rw [hvalr]
              apply phase_eq_of_int_sub (k := -(r.val : ℤ) * k)
              push_cast; field_simp; ring
            rw [sum_congr rfl hshift]
            have hbi : ∑ j ∈ range N, ‖PolynomialTransfer.P (fun r : ZMod N => if r ∈ B then (1 : ℂ) else 0) (j : ZMod N)‖ ^ 2 =
                ∑ x : ZMod N, ‖PolynomialTransfer.P (fun r : ZMod N => if r ∈ B then (1 : ℂ) else 0) x‖ ^ 2 := by
              refine Finset.sum_bij (fun j _ => (j : ZMod N)) (fun _ _ => mem_univ _) ?_ ?_ (fun _ _ => rfl)
              · intro j₁ hj₁ j₂ hj₂ heq
                have := congrArg ZMod.val heq
                rwa [ZMod.val_natCast_of_lt (mem_range.mp hj₁), ZMod.val_natCast_of_lt (mem_range.mp hj₂)] at this
              · intro x _
                exact ⟨x.val, mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
            rw [hbi]
            have hp := PolynomialTransfer.parseP (N := N) (fun r : ZMod N => if r ∈ B then (1 : ℂ) else 0)
            unfold PolynomialTransfer.E at hp
            have hsum_ind : ∑ r : ZMod N, ‖(if r ∈ B then (1 : ℂ) else 0)‖ ^ 2 = (B.card : ℝ) := by
              rw [← sum_subset (subset_univ B) (fun r _ hr => by simp [hr])]
              calc
                ∑ r ∈ B, ‖(if r ∈ B then (1 : ℂ) else 0)‖ ^ 2 = ∑ _r ∈ B, (1 : ℝ) :=
                  sum_congr rfl fun r hr => by simp [hr]
                _ = (B.card : ℝ) := by simp
            rw [hsum_ind, div_eq_iff hNpos.ne'] at hp
            linarith
          have h4blocks : ∑ n ∈ Ico (-(2 * (N : ℤ))) (2 * (N : ℤ)), ‖trig1 n‖ ^ 2 =
              ∑ k ∈ Ico (-2 : ℤ) 2, ∑ j ∈ range N, ‖trig1 (k * (N : ℤ) + (j : ℤ))‖ ^ 2 := by
            rw [← sum_product']
            symm
            refine Finset.sum_bij (fun x _ => x.1 * (N : ℤ) + (x.2 : ℤ)) ?_ ?_ ?_ (fun _ _ => rfl)
            · intro ⟨k, j⟩ hx
              have hk := mem_Ico.mp (mem_product.mp hx).1
              have hj := mem_range.mp (mem_product.mp hx).2
              exact mem_Ico.mpr ⟨by nlinarith, by nlinarith⟩
            · intro ⟨k₁, j₁⟩ h₁ ⟨k₂, j₂⟩ h₂ heq
              have hj1 := mem_range.mp (mem_product.mp h₁).2
              have hj2 := mem_range.mp (mem_product.mp h₂).2
              dsimp only at heq
              have hk : k₁ = k₂ := by nlinarith
              subst hk
              exact Prod.ext rfl (by omega)
            · intro n hn
              have hm := mem_Ico.mp hn
              let k := n / (N : ℤ)
              let j := (n % (N : ℤ)).toNat
              have hrem0 : 0 ≤ n % (N : ℤ) := Int.emod_nonneg n (by omega)
              have hrem_lt : n % (N : ℤ) < (N : ℤ) := Int.emod_lt_of_pos n (by omega)
              have hj_eq : (j : ℤ) = n % (N : ℤ) := Int.toNat_of_nonneg hrem0
              have hkn : (N : ℤ) * k + (j : ℤ) = n := by rw [hj_eq]; exact Int.mul_ediv_add_emod n (N : ℤ)
              have hk_bounds : -2 ≤ k ∧ k < 2 := by constructor <;> nlinarith
              refine ⟨(k, j), mem_product.mpr ⟨mem_Ico.mpr hk_bounds, mem_range.mpr (by omega)⟩, ?_⟩
              dsimp only; linarith
          rw [h4blocks] at h1
          rw [sum_congr rfl fun k _ => hper k] at h1
          have hcard4 : (Ico (-2 : ℤ) 2).card = 4 := by decide
          rw [sum_const, hcard4, nsmul_eq_mul] at h1
          push_cast at h1
          linarith
        have hLp : (∑ n ∈ I0, |‖trig1 n‖ ^ 2| ^ (6 / 5 : ℝ)) ^ (1 / (6 / 5 : ℝ)) ≤
            (4 * (N : ℝ)) ^ (5 / 6 : ℝ) * (B.card : ℝ) ^ (7 / 6 : ℝ) := by
          have hpt_trig : ∀ n ∈ I0, |‖trig1 n‖ ^ 2| ^ (6 / 5 : ℝ) ≤
              (B.card : ℝ) ^ (2 / 5 : ℝ) * ‖trig1 n‖ ^ 2 := by
            intro n _
            have htn : ‖trig1 n‖ ≤ (B.card : ℝ) := by
              calc
                ‖trig1 n‖ ≤ ∑ b ∈ B, ‖phase (-(b.val : ℝ) * (n : ℝ) / (N : ℝ))‖ := norm_sum_le _ _
                _ = (B.card : ℝ) := by simp [norm_phase]
            have htsq : ‖trig1 n‖ ^ 2 ≤ (B.card : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) htn 2
            rw [abs_of_nonneg (by positivity)]
            have hsplit_p : (‖trig1 n‖ ^ 2) ^ (6 / 5 : ℝ) =
                (‖trig1 n‖ ^ 2) ^ (1 / 5 : ℝ) * (‖trig1 n‖ ^ 2) := by
              by_cases hz : ‖trig1 n‖ ^ 2 = 0
              · rw [hz, Real.zero_rpow (by norm_num), mul_zero]
              · have hp : 0 < ‖trig1 n‖ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hz)
                conv_rhs => arg 2; rw [← Real.rpow_one (‖trig1 n‖ ^ 2)]
                rw [← Real.rpow_add hp]; norm_num
            rw [hsplit_p]
            have h15 : (‖trig1 n‖ ^ 2) ^ (1 / 5 : ℝ) ≤ (B.card : ℝ) ^ (2 / 5 : ℝ) := by
              calc
                (‖trig1 n‖ ^ 2) ^ (1 / 5 : ℝ) ≤ ((B.card : ℝ) ^ 2) ^ (1 / 5 : ℝ) :=
                  Real.rpow_le_rpow (by positivity) htsq (by norm_num)
                _ = (B.card : ℝ) ^ (2 / 5 : ℝ) := by
                  rw [← Real.rpow_natCast, ← Real.rpow_mul hBpos.le]; norm_num
            exact mul_le_mul_of_nonneg_right h15 (by positivity)
          have hsum_le : ∑ n ∈ I0, |‖trig1 n‖ ^ 2| ^ (6 / 5 : ℝ) ≤
              (4 * (N : ℝ)) * (B.card : ℝ) ^ (7 / 5 : ℝ) := by
            calc
              ∑ n ∈ I0, |‖trig1 n‖ ^ 2| ^ (6 / 5 : ℝ)
                  ≤ ∑ n ∈ I0, (B.card : ℝ) ^ (2 / 5 : ℝ) * ‖trig1 n‖ ^ 2 := sum_le_sum hpt_trig
              _ = (B.card : ℝ) ^ (2 / 5 : ℝ) * ∑ n ∈ I0, ‖trig1 n‖ ^ 2 := (mul_sum _ _ _).symm
              _ ≤ (B.card : ℝ) ^ (2 / 5 : ℝ) * (4 * (N : ℝ) * (B.card : ℝ)) :=
                mul_le_mul_of_nonneg_left htrig_parse (by positivity)
              _ = (4 * (N : ℝ)) * ((B.card : ℝ) ^ (2 / 5 : ℝ) * (B.card : ℝ) ^ (1 : ℝ)) := by
                rw [Real.rpow_one]; ring
              _ = (4 * (N : ℝ)) * (B.card : ℝ) ^ (7 / 5 : ℝ) := by
                rw [← Real.rpow_add hBpos]; norm_num
          have h56 : (1 : ℝ) / (6 / 5 : ℝ) = 5 / 6 := by norm_num
          rw [h56]
          calc
            (∑ n ∈ I0, |‖trig1 n‖ ^ 2| ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ)
                ≤ ((4 * (N : ℝ)) * (B.card : ℝ) ^ (7 / 5 : ℝ)) ^ (5 / 6 : ℝ) :=
              Real.rpow_le_rpow (sum_nonneg fun _ _ => by positivity) hsum_le (by norm_num)
            _ = (4 * (N : ℝ)) ^ (5 / 6 : ℝ) * ((B.card : ℝ) ^ (7 / 5 : ℝ)) ^ (5 / 6 : ℝ) :=
              Real.mul_rpow (by positivity) (by positivity)
            _ = (4 * (N : ℝ)) ^ (5 / 6 : ℝ) * (B.card : ℝ) ^ (7 / 6 : ℝ) := by
              rw [← Real.rpow_mul hBpos.le]; norm_num
        -- Bound L^6 of divS using ruzsa_lcm_sum 6 B.card
        have hLq : (∑ n ∈ I0, |divS n| ^ (6 : ℝ)) ^ (1 / (6 : ℝ)) ≤
            (4 * (N : ℝ)) ^ (1 / 6 : ℝ) * C_log * (B.card : ℝ) ^ (1 / 30 : ℝ) := by
          have hsum6 : ∑ n ∈ I0, |divS n| ^ (6 : ℝ) ≤
              4 * (N : ℝ) * (1 + Real.log (B.card : ℝ)) ^ 63 := by
            have hpow6 : ∀ n ∈ I0, |divS n| ^ (6 : ℝ) =
                ∑ q ∈ Fintype.piFinset (fun _ : Fin 6 => Icc 1 B.card),
                  if ((Finset.univ.lcm q : ℕ) : ℤ) ∣ n then (1 : ℝ) else 0 := by
              intro n _
              have hdiv0 : 0 ≤ divS n := sum_nonneg fun q _ => by split_ifs <;> norm_num
              rw [abs_of_nonneg hdiv0, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
              dsimp [divS]
              have hpi := Finset.prod_univ_sum (t := fun _ : Fin 6 => Icc 1 B.card)
                (f := fun _ q => if (q : ℤ) ∣ n then (1 : ℝ) else 0)
              have hconst : (∑ q ∈ Icc 1 B.card, if (q : ℤ) ∣ n then (1 : ℝ) else 0) ^ 6 =
                  ∏ _i : Fin 6, ∑ q ∈ Icc 1 B.card, if (q : ℤ) ∣ n then (1 : ℝ) else 0 := by
                simp [prod_const]
              rw [hconst, hpi]
              refine sum_congr rfl fun q hq => ?_
              have hlcm_iff : ((Finset.univ.lcm q : ℕ) : ℤ) ∣ n ↔ ∀ i : Fin 6, (q i : ℤ) ∣ n := by
                rw [Int.ofNat_dvd_left, Finset.lcm_dvd_iff]
                simp [Int.ofNat_dvd_left]
              by_cases hall : ∀ i : Fin 6, (q i : ℤ) ∣ n
              · rw [ite_eq_left (hlcm_iff.mpr hall)]
                exact prod_eq_one fun i _ => ite_eq_left (hall i)
              · rw [ite_eq_right (fun h => hall (hlcm_iff.mp h))]
                push Not at hall
                obtain ⟨i, hi⟩ := hall
                exact prod_eq_zero (mem_univ i) (ite_eq_right hi)
            rw [sum_congr rfl hpow6, sum_comm]
            have hcount : ∀ q ∈ Fintype.piFinset (fun _ : Fin 6 => Icc 1 B.card),
                ∑ n ∈ I0, (if ((Finset.univ.lcm q : ℕ) : ℤ) ∣ n then (1 : ℝ) else 0) ≤
                4 * (N : ℝ) * (1 / ((Finset.univ.lcm q : ℕ) : ℝ)) := by
              intro q hq
              have hlcm1 : 1 ≤ Finset.univ.lcm q := by
                apply Nat.pos_of_ne_zero
                have hnz : ∀ (s : Finset (Fin 6)), (∀ i ∈ s, q i ≠ 0) → s.lcm q ≠ 0 := by
                  intro s
                  induction s using Finset.induction_on with
                  | empty => intro _; simp
                  | @insert a s has ih =>
                    intro hs
                    rw [Finset.lcm_insert]
                    exact mt Nat.lcm_eq_zero_iff.mp (not_or.mpr ⟨hs a (mem_insert_self _ _),
                      ih fun i hi => hs i (mem_insert_of_mem hi)⟩)
                exact hnz Finset.univ (fun i _ => (by have := (mem_Icc.mp (Fintype.mem_piFinset.mp hq i)).1; omega))
              rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
              have hcard := card_multiples_nonzero_Ioo_le (N := N) (L := Finset.univ.lcm q) hlcm1
              have hcard_r : ((I0.filter (fun n : ℤ => ((Finset.univ.lcm q : ℕ) : ℤ) ∣ n)).card : ℝ) ≤
                  ((4 * N / Finset.univ.lcm q : ℕ) : ℝ) := by
                dsimp [I0, L] at hcard ⊢; exact_mod_cast hcard
              have hdiv_r : ((4 * N / Finset.univ.lcm q : ℕ) : ℝ) ≤
                  4 * (N : ℝ) * (1 / ((Finset.univ.lcm q : ℕ) : ℝ)) := by
                rw [mul_one_div, le_div_iff₀ (by exact_mod_cast hlcm1)]
                have hle := Nat.div_mul_le_self (4 * N) (Finset.univ.lcm q)
                exact_mod_cast hle
              exact hcard_r.trans hdiv_r
            calc
              ∑ q ∈ Fintype.piFinset (fun _ : Fin 6 => Icc 1 B.card),
                  ∑ n ∈ I0, (if ((Finset.univ.lcm q : ℕ) : ℤ) ∣ n then (1 : ℝ) else 0)
                  ≤ ∑ q ∈ Fintype.piFinset (fun _ : Fin 6 => Icc 1 B.card),
                    4 * (N : ℝ) * (1 / ((Finset.univ.lcm q : ℕ) : ℝ)) := sum_le_sum hcount
              _ = 4 * (N : ℝ) * ∑ q ∈ Fintype.piFinset (fun _ : Fin 6 => Icc 1 B.card),
                    (1 : ℝ) / ((Finset.univ.lcm q : ℕ) : ℝ) := (mul_sum _ _ _).symm
              _ ≤ 4 * (N : ℝ) * (1 + Real.log (B.card : ℝ)) ^ 63 := by
                have hr := ruzsa_lcm_sum 6 B.card hB
                have h63 : 2 ^ 6 - 1 = 63 := by decide
                rw [h63] at hr
                exact mul_le_mul_of_nonneg_left hr (by positivity)
          have hlog1 : 1 ≤ 1 + Real.log (B.card : ℝ) := by
            linarith [Real.log_nonneg hB1]
          have h63_66 : (1 + Real.log (B.card : ℝ)) ^ 63 ≤ (1 + Real.log (B.card : ℝ)) ^ 66 :=
            pow_le_pow_right₀ hlog1 (by decide)
          have hlog_b := one_add_log_le_rpow (1 / 330 : ℝ) (by norm_num) hB1
          have hlog_b' : 1 + Real.log (B.card : ℝ) ≤ 331 * (B.card : ℝ) ^ (1 / 330 : ℝ) := by
            norm_num at hlog_b; exact hlog_b
          have h11 : (1 + Real.log (B.card : ℝ)) ^ 11 ≤ C_log * (B.card : ℝ) ^ (1 / 30 : ℝ) := by
            calc
              (1 + Real.log (B.card : ℝ)) ^ 11 ≤ (331 * (B.card : ℝ) ^ (1 / 330 : ℝ)) ^ 11 :=
                pow_le_pow_left₀ (by linarith) hlog_b' 11
              _ = C_log * ((B.card : ℝ) ^ (1 / 330 : ℝ)) ^ 11 := by rw [mul_pow]
              _ = C_log * (B.card : ℝ) ^ (1 / 30 : ℝ) := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul hBpos.le]; norm_num
          calc
            (∑ n ∈ I0, |divS n| ^ (6 : ℝ)) ^ (1 / (6 : ℝ))
                ≤ (4 * (N : ℝ) * (1 + Real.log (B.card : ℝ)) ^ 66) ^ (1 / (6 : ℝ)) :=
              Real.rpow_le_rpow (sum_nonneg fun _ _ => by positivity)
                (hsum6.trans (mul_le_mul_of_nonneg_left h63_66 (by positivity))) (by norm_num)
            _ = (4 * (N : ℝ)) ^ (1 / 6 : ℝ) * ((1 + Real.log (B.card : ℝ)) ^ 66) ^ (1 / 6 : ℝ) :=
              Real.mul_rpow (by positivity) (by positivity)
            _ = (4 * (N : ℝ)) ^ (1 / 6 : ℝ) * (1 + Real.log (B.card : ℝ)) ^ 11 := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
              norm_num
            _ ≤ (4 * (N : ℝ)) ^ (1 / 6 : ℝ) * (C_log * (B.card : ℝ) ^ (1 / 30 : ℝ)) :=
              mul_le_mul_of_nonneg_left h11 (by positivity)
            _ = (4 * (N : ℝ)) ^ (1 / 6 : ℝ) * C_log * (B.card : ℝ) ^ (1 / 30 : ℝ) := by ring
        have hmul_hl : ∑ n ∈ I0, ‖trig1 n‖ ^ 2 * divS n ≤
            4 * (N : ℝ) * C_log * (B.card : ℝ) ^ (6 / 5 : ℝ) := by
          have hN_pow : (4 * (N : ℝ)) ^ (5 / 6 : ℝ) * (4 * (N : ℝ)) ^ (1 / 6 : ℝ) = 4 * (N : ℝ) := by
            rw [← Real.rpow_add (by positivity)]; norm_num
          have hB_pow : (B.card : ℝ) ^ (7 / 6 : ℝ) * (B.card : ℝ) ^ (1 / 30 : ℝ) = (B.card : ℝ) ^ (6 / 5 : ℝ) := by
            rw [← Real.rpow_add hBpos]; norm_num
          calc
            ∑ n ∈ I0, ‖trig1 n‖ ^ 2 * divS n
                ≤ ((4 * (N : ℝ)) ^ (5 / 6 : ℝ) * (B.card : ℝ) ^ (7 / 6 : ℝ)) *
                  ((4 * (N : ℝ)) ^ (1 / 6 : ℝ) * C_log * (B.card : ℝ) ^ (1 / 30 : ℝ)) :=
              hholder.trans (mul_le_mul hLp hLq (Real.rpow_nonneg (sum_nonneg fun _ _ => by positivity) _)
                (by positivity))
            _ = ((4 * (N : ℝ)) ^ (5 / 6 : ℝ) * (4 * (N : ℝ)) ^ (1 / 6 : ℝ)) *
                C_log * ((B.card : ℝ) ^ (7 / 6 : ℝ) * (B.card : ℝ) ^ (1 / 30 : ℝ)) := by ring
            _ = 4 * (N : ℝ) * C_log * (B.card : ℝ) ^ (6 / 5 : ℝ) := by rw [hN_pow, hB_pow]
        calc
          (1 / (L : ℝ)) * ∑ n ∈ I0, fejerWeight L n * ‖trig1 n‖ ^ 2 * divS n
              ≤ (1 / (L : ℝ)) * (4 * (N : ℝ) * C_log * (B.card : ℝ) ^ (6 / 5 : ℝ)) :=
            mul_le_mul_of_nonneg_left (hdrop.trans hmul_hl) (by positivity)
          _ = 2 * C_log * (B.card : ℝ) ^ (6 / 5 : ℝ) := by
            dsimp [L]; push_cast; field_simp; ring
      have hT_le : T ≤ (1 + 2 * C_log) * (B.card : ℝ) ^ (6 / 5 : ℝ) := by
        have hB_le_65 : (B.card : ℝ) ≤ (B.card : ℝ) ^ (6 / 5 : ℝ) := by
          conv_lhs => rw [← Real.rpow_one (B.card : ℝ)]
          exact Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num)
        linarith
      have hB_exp : (B.card : ℝ) ^ (1 / 5 : ℝ) * (B.card : ℝ) ^ (6 / 5 : ℝ) = (B.card : ℝ) ^ (7 / 5 : ℝ) := by
        rw [← Real.rpow_add hBpos]; norm_num
      calc
        _ ≤ (B.card : ℝ) ^ (1 / 5 : ℝ) * ((1 + 2 * C_log) * (B.card : ℝ) ^ (6 / 5 : ℝ)) :=
          hstep1.trans (mul_le_mul_of_nonneg_left hT_le (by positivity))
        _ = (1 + 2 * C_log) * ((B.card : ℝ) ^ (1 / 5 : ℝ) * (B.card : ℝ) ^ (6 / 5 : ℝ)) := by ring
        _ = (1 + 2 * C_log) * (B.card : ℝ) ^ (7 / 5 : ℝ) := by rw [hB_exp]
    -- Combine large q and small q
    calc
      PolynomialTransfer.E (fun x : ZMod N => sieveBeta d a R (x.val : ℤ) * ‖PolynomialTransfer.P f x‖ ^ 2)
          ≤ 4 * (C_w * (4 * (B.card : ℝ) ^ (7 / 5 : ℝ) + (1 + 2 * C_log) * (B.card : ℝ) ^ (7 / 5 : ℝ))) :=
        hfejer_dom.trans (mul_le_mul_of_nonneg_left
          (hexpand.trans (mul_le_mul_of_nonneg_left (hsplit_q ▸ add_le_add hbig hsmall) hC_w.le))
          (by norm_num))
      _ = (20 * C_w + 8 * C_w * C_log) * (B.card : ℝ) ^ (7 / 5 : ℝ) := by ring
      _ ≤ C_set * (B.card : ℝ) ^ (7 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

lemma l2_weighted_add_le {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ x ∈ s, 0 ≤ w x)
    (a b : ι → ℂ) :
    Real.sqrt (∑ x ∈ s, w x * ‖a x + b x‖ ^ 2) ≤
      Real.sqrt (∑ x ∈ s, w x * ‖a x‖ ^ 2) + Real.sqrt (∑ x ∈ s, w x * ‖b x‖ ^ 2) := by
  have hA0 : 0 ≤ ∑ x ∈ s, w x * ‖a x‖ ^ 2 := sum_nonneg fun x hx => mul_nonneg (hw x hx) (by positivity)
  have hB0 : 0 ≤ ∑ x ∈ s, w x * ‖b x‖ ^ 2 := sum_nonneg fun x hx => mul_nonneg (hw x hx) (by positivity)
  have hCS : ∑ x ∈ s, w x * ‖a x‖ * ‖b x‖ ≤
      Real.sqrt (∑ x ∈ s, w x * ‖a x‖ ^ 2) * Real.sqrt (∑ x ∈ s, w x * ‖b x‖ ^ 2) := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq s (fun x => Real.sqrt (w x) * ‖a x‖)
      (fun x => Real.sqrt (w x) * ‖b x‖)
    have hlhs : ∑ x ∈ s, (Real.sqrt (w x) * ‖a x‖) * (Real.sqrt (w x) * ‖b x‖) =
        ∑ x ∈ s, w x * ‖a x‖ * ‖b x‖ := by
      refine sum_congr rfl fun x hx => ?_
      have hsq : Real.sqrt (w x) * Real.sqrt (w x) = w x := Real.mul_self_sqrt (hw x hx)
      calc
        (Real.sqrt (w x) * ‖a x‖) * (Real.sqrt (w x) * ‖b x‖)
            = (Real.sqrt (w x) * Real.sqrt (w x)) * ‖a x‖ * ‖b x‖ := by ring
        _ = w x * ‖a x‖ * ‖b x‖ := by rw [hsq]
    have hr1 : ∑ x ∈ s, (Real.sqrt (w x) * ‖a x‖) ^ 2 = ∑ x ∈ s, w x * ‖a x‖ ^ 2 := by
      refine sum_congr rfl fun x hx => by rw [mul_pow, Real.sq_sqrt (hw x hx)]
    have hr2 : ∑ x ∈ s, (Real.sqrt (w x) * ‖b x‖) ^ 2 = ∑ x ∈ s, w x * ‖b x‖ ^ 2 := by
      refine sum_congr rfl fun x hx => by rw [mul_pow, Real.sq_sqrt (hw x hx)]
    rw [hlhs, hr1, hr2] at h1
    have hnon : 0 ≤ ∑ x ∈ s, w x * ‖a x‖ * ‖b x‖ :=
      sum_nonneg fun x hx => mul_nonneg (mul_nonneg (hw x hx) (norm_nonneg _)) (norm_nonneg _)
    have hrt := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq hnon, Real.sqrt_mul hA0] at hrt
    exact hrt
  have hsq : ∑ x ∈ s, w x * ‖a x + b x‖ ^ 2 ≤
      (Real.sqrt (∑ x ∈ s, w x * ‖a x‖ ^ 2) + Real.sqrt (∑ x ∈ s, w x * ‖b x‖ ^ 2)) ^ 2 := by
    have htri : ∑ x ∈ s, w x * ‖a x + b x‖ ^ 2 ≤
        (∑ x ∈ s, w x * ‖a x‖ ^ 2) + 2 * (∑ x ∈ s, w x * ‖a x‖ * ‖b x‖) +
          (∑ x ∈ s, w x * ‖b x‖ ^ 2) := by
      rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
      refine sum_le_sum fun x hx => ?_
      have hn := norm_add_le (a x) (b x)
      have hn2 : ‖a x + b x‖ ^ 2 ≤ (‖a x‖ + ‖b x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
      have hwx := hw x hx
      nlinarith
    have hexp : (Real.sqrt (∑ x ∈ s, w x * ‖a x‖ ^ 2) + Real.sqrt (∑ x ∈ s, w x * ‖b x‖ ^ 2)) ^ 2 =
        (∑ x ∈ s, w x * ‖a x‖ ^ 2) +
        2 * (Real.sqrt (∑ x ∈ s, w x * ‖a x‖ ^ 2) * Real.sqrt (∑ x ∈ s, w x * ‖b x‖ ^ 2)) +
        (∑ x ∈ s, w x * ‖b x‖ ^ 2) := by
      rw [add_sq, Real.sq_sqrt hA0, Real.sq_sqrt hB0]; ring
    linarith
  have hrt := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by positivity)] at hrt

lemma l2_weighted_sum_le {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (t : Finset κ)
    (w : ι → ℝ) (hw : ∀ x ∈ s, 0 ≤ w x) (a : κ → ι → ℂ) :
    Real.sqrt (∑ x ∈ s, w x * ‖∑ j ∈ t, a j x‖ ^ 2) ≤
      ∑ j ∈ t, Real.sqrt (∑ x ∈ s, w x * ‖a j x‖ ^ 2) := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert k t hkt ih =>
    simp_rw [sum_insert hkt]
    exact (l2_weighted_add_le s w hw (a k) (fun x => ∑ j ∈ t, a j x)).trans
      (add_le_add le_rfl ih)

set_option maxHeartbeats 1600000 in
lemma restriction_lq :
    ∃ C_restr : ℝ, 0 < C_restr ∧
      ∀ d a N : ℕ, [NeZero N] → 1 ≤ a → a < d → d ≤ N → a.Coprime d →
      ∀ f : ZMod N → ℂ,
        Real.sqrt (PolynomialTransfer.E (fun x : ZMod N =>
          sieveBeta d a ⌊(N : ℝ) ^ (1 / 20 : ℝ)⌋₊ (x.val : ℤ) *
            ‖PolynomialTransfer.P f x‖ ^ 2)) ≤
          C_restr * (∑ r : ZMod N, ‖f r‖ ^ (15 / 11 : ℝ)) ^ (11 / 15 : ℝ) := by
  obtain ⟨C_set, hC_set, hset⟩ := restriction_set_bound
  let ρ : ℝ := (2 : ℝ) ^ (-(1 / 22 : ℝ))
  have hρ_pos : 0 < ρ := by dsimp [ρ]; positivity
  have hρ_lt1 : ρ < 1 := by
    dsimp [ρ]
    conv_rhs => rw [← Real.rpow_zero (2 : ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  let C_restr : ℝ := Real.sqrt C_set * 2 / (1 - ρ)
  have hC_restr_pos : 0 < C_restr :=
    div_pos (mul_pos (Real.sqrt_pos.mpr hC_set) (by norm_num)) (by linarith)
  refine ⟨C_restr, hC_restr_pos, ?_⟩
  intro d a N inst ha had hdN hcop f
  let R : ℕ := ⌊(N : ℝ) ^ (1 / 20 : ℝ)⌋₊
  let S : ℝ := (∑ r : ZMod N, ‖f r‖ ^ (15 / 11 : ℝ)) ^ (11 / 15 : ℝ)
  have hS_nonneg : 0 ≤ S := Real.rpow_nonneg (sum_nonneg fun _ _ => by positivity) _
  by_cases hS0 : S = 0
  · have hf0 : ∀ r : ZMod N, f r = 0 := by
      intro r
      have hsum0 : ∑ r : ZMod N, ‖f r‖ ^ (15 / 11 : ℝ) = 0 := by
        by_contra hne
        have hpos : 0 < ∑ r : ZMod N, ‖f r‖ ^ (15 / 11 : ℝ) :=
          lt_of_le_of_ne (sum_nonneg fun _ _ => by positivity) (Ne.symm hne)
        have : 0 < S := Real.rpow_pos_of_pos hpos _
        linarith
      have hterm0 : ‖f r‖ ^ (15 / 11 : ℝ) = 0 :=
        (sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).mp hsum0 r (mem_univ r)
      have hn0 : ‖f r‖ = 0 := by
        by_contra hne
        have hpos : 0 < ‖f r‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
        have : 0 < ‖f r‖ ^ (15 / 11 : ℝ) := Real.rpow_pos_of_pos hpos _
        linarith
      exact norm_eq_zero.mp hn0
    have hP0 : ∀ x : ZMod N, PolynomialTransfer.P f x = 0 := fun x => by
      unfold PolynomialTransfer.P; simp [hf0]
    simp [hP0, PolynomialTransfer.E]
    exact mul_nonneg hC_restr_pos.le hS_nonneg
  · -- Scale to unit l^(15/11) norm
    have hSpos : 0 < S := lt_of_le_of_ne hS_nonneg (Ne.symm hS0)
    let g : ZMod N → ℂ := fun r => ((1 / S : ℝ) : ℂ) * f r
    have hg_norm : ∑ r : ZMod N, ‖g r‖ ^ (15 / 11 : ℝ) = 1 := by
      have h1 : ∀ r : ZMod N, ‖g r‖ ^ (15 / 11 : ℝ) = (1 / S) ^ (15 / 11 : ℝ) * ‖f r‖ ^ (15 / 11 : ℝ) := by
        intro r
        dsimp [g]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
          Real.mul_rpow (by positivity) (norm_nonneg _)]
      simp_rw [h1, ← mul_sum]
      have hS15 : S ^ (15 / 11 : ℝ) = ∑ r : ZMod N, ‖f r‖ ^ (15 / 11 : ℝ) := by
        dsimp [S]
        rw [← Real.rpow_mul (sum_nonneg fun _ _ => by positivity)]
        norm_num
      rw [← hS15, one_div, Real.inv_rpow hSpos.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hSpos _).ne']
    have hg_le1 : ∀ r : ZMod N, ‖g r‖ ≤ 1 := by
      intro r
      have h1 : ‖g r‖ ^ (15 / 11 : ℝ) ≤ 1 := by
        rw [← hg_norm]
        exact single_le_sum (f := fun r => ‖g r‖ ^ (15 / 11 : ℝ))
          (fun _ _ => by positivity) (mem_univ r)
      by_contra hgt
      push Not at hgt
      have : 1 < ‖g r‖ ^ (15 / 11 : ℝ) := Real.one_lt_rpow hgt (by norm_num)
      linarith
    -- Find J such that every nonzero g r has ‖g r‖ > (1/2)^(J+1)
    have hexJ : ∃ J : ℕ, ∀ r : ZMod N, g r ≠ 0 → (1 / 2 : ℝ) ^ (J + 1) < ‖g r‖ := by
      let nz := (univ : Finset (ZMod N)).filter (fun r => g r ≠ 0)
      by_cases hne : nz.Nonempty
      · obtain ⟨r0, hr0, hmin⟩ := nz.exists_min_image (fun r => ‖g r‖) hne
        have hpos0 : 0 < ‖g r0‖ := norm_pos_iff.mpr (mem_filter.mp hr0).2
        obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one hpos0 (by norm_num : (1 / 2 : ℝ) < 1)
        refine ⟨J, fun r hr => ?_⟩
        have hmem : r ∈ nz := mem_filter.mpr ⟨mem_univ r, hr⟩
        have hlt : (1 / 2 : ℝ) ^ (J + 1) < (1 / 2 : ℝ) ^ J := by
          rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) J]
        exact hlt.trans (hJ.trans_le (hmin r hmem))
      · refine ⟨0, fun r hr => ?_⟩
        exfalso; exact hne ⟨r, mem_filter.mpr ⟨mem_univ r, hr⟩⟩
    obtain ⟨J, hJ⟩ := hexJ
    let Bj : ℕ → Finset (ZMod N) := fun j =>
      univ.filter (fun r => (1 / 2 : ℝ) ^ (j + 1) < ‖g r‖ ∧ ‖g r‖ ≤ (1 / 2 : ℝ) ^ j)
    let gj : ℕ → ZMod N → ℂ := fun j r => if r ∈ Bj j then g r else 0
    have hg_decomp : ∀ r : ZMod N, g r = ∑ j ∈ range (J + 1), gj j r := by
      intro r
      by_cases hr0 : g r = 0
      · rw [hr0]; symm; apply sum_eq_zero; intro j _
        dsimp [gj]; simp [hr0]
      · have hpos : 0 < ‖g r‖ := norm_pos_iff.mpr hr0
        have hgtJ : (1 / 2 : ℝ) ^ (J + 1) < ‖g r‖ := hJ r hr0
        -- Exists unique j ≤ J with (1/2)^(j+1) < ‖g r‖ ≤ (1/2)^j
        have hex_j : ∃ j ∈ range (J + 1), r ∈ Bj j := by
          have hex_k : ∃ k : ℕ, (1 / 2 : ℝ) ^ (k + 1) < ‖g r‖ := ⟨J, hgtJ⟩
          let j0 := Nat.find hex_k
          have hj0_spec : (1 / 2 : ℝ) ^ (j0 + 1) < ‖g r‖ := Nat.find_spec hex_k
          have hj0_le : j0 ≤ J := Nat.find_min' hex_k hgtJ
          have hj0_up : ‖g r‖ ≤ (1 / 2 : ℝ) ^ j0 := by
            cases hj : j0 with
            | zero => simpa using hg_le1 r
            | succ k =>
              have hnot := Nat.find_min hex_k (show k < j0 by omega)
              exact not_lt.mp hnot
          exact ⟨j0, mem_range.mpr (by omega), mem_filter.mpr ⟨mem_univ r, hj0_spec, hj0_up⟩⟩
        obtain ⟨j0, hj0_mem, hj0_in⟩ := hex_j
        rw [Finset.sum_eq_single j0]
        · dsimp [gj]; rw [ite_eq_left hj0_in]
        · intro j _ hjne
          dsimp [gj]
          have hnotin : r ∉ Bj j := by
            intro hmem
            have h1 := (mem_filter.mp hj0_in).2
            have h2 := (mem_filter.mp hmem).2
            rcases lt_or_gt_of_ne hjne with hlt | hgt
            · have : (1 / 2 : ℝ) ^ j0 ≤ (1 / 2 : ℝ) ^ (j + 1) :=
                pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
              linarith
            · have : (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ (j0 + 1) :=
                pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
              linarith
          rw [ite_eq_right hnotin]
        · intro h; exact absurd hj0_mem h
    have hP_decomp : ∀ x : ZMod N, PolynomialTransfer.P g x =
        ∑ j ∈ range (J + 1), PolynomialTransfer.P (gj j) x := by
      intro x
      unfold PolynomialTransfer.P
      calc
        ∑ r : ZMod N, g r * PolynomialTransfer.ch r x
            = ∑ r : ZMod N, (∑ j ∈ range (J + 1), gj j r) * PolynomialTransfer.ch r x :=
          sum_congr rfl fun r _ => by rw [hg_decomp r]
        _ = ∑ r : ZMod N, ∑ j ∈ range (J + 1), gj j r * PolynomialTransfer.ch r x :=
          sum_congr rfl fun r _ => sum_mul _ _ _
        _ = ∑ j ∈ range (J + 1), ∑ r : ZMod N, gj j r * PolynomialTransfer.ch r x := sum_comm
    -- Bound E(sieveBeta * ‖P g‖^2)^(1/2) via Minkowski + restriction_set_bound on each Bj
    have hPg_bound : Real.sqrt (PolynomialTransfer.E (fun x : ZMod N =>
          sieveBeta d a R (x.val : ℤ) * ‖PolynomialTransfer.P g x‖ ^ 2)) ≤ C_restr := by
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast NeZero.pos N
      have hw_nonneg : ∀ x ∈ (univ : Finset (ZMod N)), 0 ≤ sieveBeta d a R (x.val : ℤ) / (N : ℝ) :=
        fun x _ => div_nonneg (sieveBeta_nonneg d a R (x.val : ℤ)) hNpos.le
      have hmink : Real.sqrt (PolynomialTransfer.E (fun x : ZMod N =>
            sieveBeta d a R (x.val : ℤ) * ‖PolynomialTransfer.P g x‖ ^ 2)) ≤
          ∑ j ∈ range (J + 1), Real.sqrt (PolynomialTransfer.E (fun x : ZMod N =>
            sieveBeta d a R (x.val : ℤ) * ‖PolynomialTransfer.P (gj j) x‖ ^ 2)) := by
        have hrew : ∀ (h : ZMod N → ℂ),
            PolynomialTransfer.E (fun x : ZMod N => sieveBeta d a R (x.val : ℤ) * ‖h x‖ ^ 2) =
            ∑ x : ZMod N, (sieveBeta d a R (x.val : ℤ) / (N : ℝ)) * ‖h x‖ ^ 2 := by
          intro h; unfold PolynomialTransfer.E; rw [sum_div]
          exact sum_congr rfl fun x _ => by ring
        rw [hrew (PolynomialTransfer.P g)]
        simp_rw [hP_decomp]
        have hrhs : ∑ j ∈ range (J + 1), Real.sqrt (PolynomialTransfer.E (fun x : ZMod N =>
              sieveBeta d a R (x.val : ℤ) * ‖PolynomialTransfer.P (gj j) x‖ ^ 2)) =
            ∑ j ∈ range (J + 1), Real.sqrt (∑ x : ZMod N,
              (sieveBeta d a R (x.val : ℤ) / (N : ℝ)) * ‖PolynomialTransfer.P (gj j) x‖ ^ 2) :=
          sum_congr rfl fun j _ => by rw [hrew (PolynomialTransfer.P (gj j))]
        rw [hrhs]
        exact l2_weighted_sum_le (univ : Finset (ZMod N)) (range (J + 1))
          (fun (x : ZMod N) => sieveBeta d a R (x.val : ℤ) / (N : ℝ))
          hw_nonneg (fun j (x : ZMod N) => PolynomialTransfer.P (gj j) x)
      have hj_bound : ∀ j ∈ range (J + 1),
          Real.sqrt (PolynomialTransfer.E (fun x : ZMod N =>
            sieveBeta d a R (x.val : ℤ) * ‖PolynomialTransfer.P (gj j) x‖ ^ 2)) ≤
          Real.sqrt C_set * 2 * ρ ^ j := by
        intro j _
        by_cases hBj : (Bj j).card = 0
        · have hgj0 : ∀ r : ZMod N, gj j r = 0 := by
            intro r; dsimp [gj]; rw [ite_eq_right]
            intro hmem; have := Finset.card_pos.mpr ⟨r, hmem⟩; omega
          have hP0 : ∀ x : ZMod N, PolynomialTransfer.P (gj j) x = 0 := fun x => by
            unfold PolynomialTransfer.P; simp [hgj0]
          simp only [hP0, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, PolynomialTransfer.E,
            sum_const_zero, zero_div, Real.sqrt_zero]
          positivity
        · have hBj1 : 1 ≤ (Bj j).card := by omega
          let fj : ZMod N → ℂ := fun r => ((2 ^ j : ℝ) : ℂ) * gj j r
          have hfj_supp : ∀ r, r ∉ Bj j → fj r = 0 := fun r hr => by
            dsimp [fj, gj]; rw [ite_eq_right hr, mul_zero]
          have hfj_norm : ∀ r, ‖fj r‖ ≤ 1 := by
            intro r; dsimp [fj, gj]
            by_cases hr : r ∈ Bj j
            · rw [ite_eq_left hr, norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (by positivity)]
              have hup := (mem_filter.mp hr).2.2
              calc
                (2 : ℝ) ^ j * ‖g r‖ ≤ (2 : ℝ) ^ j * (1 / 2 : ℝ) ^ j :=
                  mul_le_mul_of_nonneg_left hup (by positivity)
                _ = 1 := by rw [← mul_pow]; norm_num
            · rw [ite_eq_right hr, mul_zero, norm_zero]; norm_num
          have hset_j := hset d a N ha had hdN hcop (Bj j) hBj1 fj hfj_supp hfj_norm
          have hP_scale : ∀ x : ZMod N, ‖PolynomialTransfer.P (gj j) x‖ ^ 2 =
              ((1 / 2 : ℝ) ^ j) ^ 2 * ‖PolynomialTransfer.P fj x‖ ^ 2 := by
            intro x
            have h1 : PolynomialTransfer.P fj x = ((2 ^ j : ℝ) : ℂ) * PolynomialTransfer.P (gj j) x := by
              unfold PolynomialTransfer.P; rw [mul_sum]
              exact sum_congr rfl fun r _ => by dsimp [fj]; ring
            rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
              mul_pow, ← mul_assoc, ← mul_pow]
            have : (1 / 2 : ℝ) ^ j * (2 : ℝ) ^ j = 1 := by rw [← mul_pow]; norm_num
            rw [this, one_pow, one_mul]
          have hE_scale : PolynomialTransfer.E (fun x : ZMod N =>
                sieveBeta d a R (x.val : ℤ) * ‖PolynomialTransfer.P (gj j) x‖ ^ 2) ≤
              ((1 / 2 : ℝ) ^ j) ^ 2 * (C_set * ((Bj j).card : ℝ) ^ (7 / 5 : ℝ)) := by
            have heq : (fun x : ZMod N => sieveBeta d a R (x.val : ℤ) * ‖PolynomialTransfer.P (gj j) x‖ ^ 2) =
                (fun x : ZMod N => ((1 / 2 : ℝ) ^ j) ^ 2 * (sieveBeta d a R (x.val : ℤ) * ‖PolynomialTransfer.P fj x‖ ^ 2)) := by
              funext x; rw [hP_scale x]; ring
            rw [heq, PolynomialTransfer.Emul]
            exact mul_le_mul_of_nonneg_left hset_j (by positivity)
          have hcard_le : ((Bj j).card : ℝ) ≤ (2 : ℝ) ^ ((15 / 11 : ℝ) * ((j : ℝ) + 1)) := by
            have h1 : ((Bj j).card : ℝ) * ((1 / 2 : ℝ) ^ (j + 1)) ^ (15 / 11 : ℝ) ≤ 1 := by
              calc
                ((Bj j).card : ℝ) * ((1 / 2 : ℝ) ^ (j + 1)) ^ (15 / 11 : ℝ)
                    = ∑ _r ∈ Bj j, ((1 / 2 : ℝ) ^ (j + 1)) ^ (15 / 11 : ℝ) := by simp
                _ ≤ ∑ r ∈ Bj j, ‖g r‖ ^ (15 / 11 : ℝ) := sum_le_sum fun r hr =>
                    Real.rpow_le_rpow (by positivity) (mem_filter.mp hr).2.1.le (by norm_num)
                _ ≤ ∑ r : ZMod N, ‖g r‖ ^ (15 / 11 : ℝ) :=
                    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => by positivity
                _ = 1 := hg_norm
            have h2 : ((1 / 2 : ℝ) ^ (j + 1)) ^ (15 / 11 : ℝ) =
                ((2 : ℝ) ^ ((15 / 11 : ℝ) * ((j : ℝ) + 1)))⁻¹ := by
              rw [one_div, inv_pow, Real.inv_rpow (by positivity),
                ← Real.rpow_natCast (2 : ℝ), ← Real.rpow_mul (by positivity)]
              push_cast; ring_nf
            rw [h2] at h1
            have hpos2 : 0 < (2 : ℝ) ^ ((15 / 11 : ℝ) * ((j : ℝ) + 1)) := by positivity
            have h3 := mul_le_mul_of_nonneg_right h1 hpos2.le
            rwa [mul_assoc, inv_mul_cancel₀ hpos2.ne', mul_one, one_mul] at h3
          have hrt := Real.sqrt_le_sqrt hE_scale
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
            Real.sqrt_mul hC_set.le] at hrt
          have hB710 : Real.sqrt (((Bj j).card : ℝ) ^ (7 / 5 : ℝ)) ≤
              2 * (2 : ℝ) ^ ((21 / 22 : ℝ) * (j : ℝ)) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg _)]
            calc
              ((Bj j).card : ℝ) ^ (7 / 5 * (1 / 2) : ℝ)
                  ≤ ((2 : ℝ) ^ ((15 / 11 : ℝ) * ((j : ℝ) + 1))) ^ (7 / 10 : ℝ) := by
                have : (7 / 5 : ℝ) * (1 / 2) = 7 / 10 := by norm_num
                rw [this]
                exact Real.rpow_le_rpow (Nat.cast_nonneg _) hcard_le (by norm_num)
              _ = (2 : ℝ) ^ ((21 / 22 : ℝ) + (21 / 22 : ℝ) * (j : ℝ)) := by
                rw [← Real.rpow_mul (by positivity)]; congr 1; ring
              _ = (2 : ℝ) ^ (21 / 22 : ℝ) * (2 : ℝ) ^ ((21 / 22 : ℝ) * (j : ℝ)) :=
                Real.rpow_add (by norm_num) _ _
              _ ≤ 2 * (2 : ℝ) ^ ((21 / 22 : ℝ) * (j : ℝ)) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                conv_rhs => rw [← Real.rpow_one (2 : ℝ)]
                exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          have hcomb : (1 / 2 : ℝ) ^ j * (2 * (2 : ℝ) ^ ((21 / 22 : ℝ) * (j : ℝ))) = 2 * ρ ^ j := by
            dsimp [ρ]
            rw [one_div, inv_pow, ← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_neg (by norm_num),
              ← Real.rpow_natCast ((2 : ℝ) ^ (-(1 / 22 : ℝ))) j, ← Real.rpow_mul (by positivity)]
            calc
              (2 : ℝ) ^ (-(j : ℝ)) * (2 * (2 : ℝ) ^ ((21 / 22 : ℝ) * (j : ℝ)))
                  = 2 * ((2 : ℝ) ^ (-(j : ℝ)) * (2 : ℝ) ^ ((21 / 22 : ℝ) * (j : ℝ))) := by ring
              _ = 2 * (2 : ℝ) ^ (-(j : ℝ) + (21 / 22 : ℝ) * (j : ℝ)) := by
                rw [← Real.rpow_add (by norm_num)]
              _ = 2 * (2 : ℝ) ^ (-(1 / 22 : ℝ) * (j : ℝ)) := by congr 2; ring
          calc
            Real.sqrt (PolynomialTransfer.E (fun x : ZMod N =>
                sieveBeta d a R (x.val : ℤ) * ‖PolynomialTransfer.P (gj j) x‖ ^ 2))
                ≤ (1 / 2 : ℝ) ^ j * (Real.sqrt C_set * (2 * (2 : ℝ) ^ ((21 / 22 : ℝ) * (j : ℝ)))) :=
              hrt.trans (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hB710 (Real.sqrt_nonneg _)) (by positivity))
            _ = Real.sqrt C_set * ((1 / 2 : ℝ) ^ j * (2 * (2 : ℝ) ^ ((21 / 22 : ℝ) * (j : ℝ)))) := by ring
            _ = Real.sqrt C_set * 2 * ρ ^ j := by rw [hcomb]; ring
      have hgeom : ∑ j ∈ range (J + 1), ρ ^ j ≤ 1 / (1 - ρ) := by
        rw [geom_sum_eq hρ_lt1.ne]
        have hden : 0 < 1 - ρ := by linarith
        have heq : (ρ ^ (J + 1) - 1) / (ρ - 1) = (1 - ρ ^ (J + 1)) / (1 - ρ) := by
          have : ρ - 1 ≠ 0 := by linarith
          rw [div_eq_div_iff this hden.ne']; ring
        rw [heq]
        exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hρ_pos.le (J + 1)]) hden.le
      calc
        Real.sqrt (PolynomialTransfer.E (fun x : ZMod N =>
            sieveBeta d a R (x.val : ℤ) * ‖PolynomialTransfer.P g x‖ ^ 2))
            ≤ ∑ j ∈ range (J + 1), Real.sqrt C_set * 2 * ρ ^ j :=
          hmink.trans (sum_le_sum hj_bound)
        _ = Real.sqrt C_set * 2 * ∑ j ∈ range (J + 1), ρ ^ j := (mul_sum _ _ _).symm
        _ ≤ Real.sqrt C_set * 2 * (1 / (1 - ρ)) :=
          mul_le_mul_of_nonneg_left hgeom (by positivity)
        _ = C_restr := by dsimp [C_restr]; ring
    -- Undo scaling from g = (1 / S) * f
    have hPf_eq : ∀ x : ZMod N, ‖PolynomialTransfer.P f x‖ ^ 2 = S ^ 2 * ‖PolynomialTransfer.P g x‖ ^ 2 := by
      intro x
      have h1 : PolynomialTransfer.P g x = ((1 / S : ℝ) : ℂ) * PolynomialTransfer.P f x := by
        unfold PolynomialTransfer.P; rw [mul_sum]
        exact sum_congr rfl fun r _ => by dsimp [g]; ring
      rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), mul_pow]
      field_simp
    have hE_eq : PolynomialTransfer.E (fun x : ZMod N =>
          sieveBeta d a R (x.val : ℤ) * ‖PolynomialTransfer.P f x‖ ^ 2) =
        S ^ 2 * PolynomialTransfer.E (fun x : ZMod N =>
          sieveBeta d a R (x.val : ℤ) * ‖PolynomialTransfer.P g x‖ ^ 2) := by
      have : (fun x : ZMod N => sieveBeta d a R (x.val : ℤ) * ‖PolynomialTransfer.P f x‖ ^ 2) =
          (fun x : ZMod N => S ^ 2 * (sieveBeta d a R (x.val : ℤ) * ‖PolynomialTransfer.P g x‖ ^ 2)) := by
        funext x; rw [hPf_eq x]; ring
      rw [this, PolynomialTransfer.Emul]
    rw [hE_eq, Real.sqrt_mul (by positivity), Real.sqrt_sq hSpos.le, mul_comm]
    exact mul_le_mul_of_nonneg_right hPg_bound hSpos.le

set_option maxHeartbeats 1600000 in
theorem sieveBeta_extension_lp :
    ∃ M_abs : ℝ, 1 ≤ M_abs ∧
      ∀ d a N : ℕ, [NeZero N] → 1 ≤ a → a < d → d ≤ N → a.Coprime d →
      ∀ g : ZMod N → ℝ, (∀ x, 0 ≤ g x) →
        (∀ x, g x ≤ 50 * sieveBeta d a ⌊(N : ℝ) ^ (1 / 20 : ℝ)⌋₊ (x.val : ℤ)) →
        ∑ r : ZMod N, ‖PolynomialTransfer.F g r‖ ^ (15 / 4 : ℝ) ≤ M_abs ^ (15 / 4 : ℝ) := by
  obtain ⟨C_set, hC_set, hset⟩ := restriction_set_bound
  obtain ⟨C_restr, hC_restr, hrestr⟩ := restriction_lq
  let M_abs : ℝ := max 1 (50 * Real.sqrt C_set * C_restr)
  refine ⟨M_abs, le_max_left _ _, ?_⟩
  intro d a N inst ha had hdN hcop g hg0 hgle
  let R : ℕ := ⌊(N : ℝ) ^ (1 / 20 : ℝ)⌋₊
  let S : ℝ := ∑ r : ZMod N, ‖PolynomialTransfer.F g r‖ ^ (15 / 4 : ℝ)
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => by positivity
  by_cases hSzero : S = 0
  · change S ≤ M_abs ^ (15 / 4 : ℝ)
    rw [hSzero]; positivity
  · have hSpos : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hSzero)
    -- Average bound on sieveBeta via B = {0}, f = δ_0
    have hbeta_avg : PolynomialTransfer.E (fun x : ZMod N => sieveBeta d a R (x.val : ℤ)) ≤ C_set := by
      let f0 : ZMod N → ℂ := fun r => if r = 0 then 1 else 0
      have hP0 : ∀ x : ZMod N, ‖PolynomialTransfer.P f0 x‖ ^ 2 = 1 := by
        intro x
        have h1 : PolynomialTransfer.P f0 x = 1 := by
          unfold PolynomialTransfer.P
          rw [Finset.sum_eq_single 0]
          · simp [f0, PolynomialTransfer.ch]
          · intro r _ hr; simp [f0, hr]
          · intro h; exact absurd (mem_univ 0) h
        rw [h1, norm_one, one_pow]
      have hset0 := hset d a N ha had hdN hcop ({0} : Finset (ZMod N)) (by simp) f0
        (fun r hr => by simp [f0, mem_singleton.not.mp hr])
        (fun r => by dsimp [f0]; split_ifs <;> norm_num)
      dsimp only [R]
      simpa [hP0] using hset0
    -- Duality test function f r = ‖F g r‖^(7/4) * conj (F g r)
    let f : ZMod N → ℂ := fun r =>
      ((‖PolynomialTransfer.F g r‖ ^ (7 / 4 : ℝ) : ℝ) : ℂ) * conj (PolynomialTransfer.F g r)
    have hpair_val : (S : ℂ) = PolynomialTransfer.C (fun x : ZMod N => (g x : ℂ) * PolynomialTransfer.P f x) := by
      rw [PolynomialTransfer.pair]
      dsimp [S]
      rw [Complex.ofReal_sum]
      refine sum_congr rfl fun r _ => ?_
      dsimp [f]
      rw [mul_assoc, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul]
      congr 1
      by_cases hz : ‖PolynomialTransfer.F g r‖ = 0
      · rw [hz, Real.zero_rpow (by norm_num), Real.zero_rpow (by norm_num), zero_mul]
      · have hp : 0 < ‖PolynomialTransfer.F g r‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
        rw [← Real.rpow_natCast ‖PolynomialTransfer.F g r‖ 2, ← Real.rpow_add hp]; norm_num
    have hf_lq : ∑ r : ZMod N, ‖f r‖ ^ (15 / 11 : ℝ) = S := by
      dsimp [S]
      refine sum_congr rfl fun r _ => ?_
      dsimp [f]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        RCLike.norm_conj]
      by_cases hz : ‖PolynomialTransfer.F g r‖ = 0
      · rw [hz, Real.zero_rpow (by norm_num), zero_mul, Real.zero_rpow (by norm_num),
          Real.zero_rpow (by norm_num)]
      · have hp : 0 < ‖PolynomialTransfer.F g r‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
        have h1 : ‖PolynomialTransfer.F g r‖ ^ (7 / 4 : ℝ) * ‖PolynomialTransfer.F g r‖ =
            ‖PolynomialTransfer.F g r‖ ^ (11 / 4 : ℝ) := by
          conv_lhs => arg 2; rw [← Real.rpow_one ‖PolynomialTransfer.F g r‖]
          rw [← Real.rpow_add hp]; norm_num
        rw [h1, ← Real.rpow_mul hp.le]; norm_num
    have hS_cs : S ≤ Real.sqrt (PolynomialTransfer.E g) *
        Real.sqrt (PolynomialTransfer.E (fun x : ZMod N => g x * ‖PolynomialTransfer.P f x‖ ^ 2)) := by
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast NeZero.pos N
      have h1 : S ≤ PolynomialTransfer.E (fun x : ZMod N => g x * ‖PolynomialTransfer.P f x‖) := by
        have hnorm : S = ‖(S : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0]
        rw [hnorm, hpair_val]
        unfold PolynomialTransfer.C PolynomialTransfer.E
        rw [norm_div, Complex.norm_natCast]
        apply div_le_div_of_nonneg_right _ hNpos.le
        refine (norm_sum_le _ _).trans (sum_le_sum fun x _ => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (ZMod N))
        (fun x => Real.sqrt (g x)) (fun x => Real.sqrt (g x) * ‖PolynomialTransfer.P f x‖)
      have hl : ∑ x : ZMod N, Real.sqrt (g x) * (Real.sqrt (g x) * ‖PolynomialTransfer.P f x‖) =
          ∑ x : ZMod N, g x * ‖PolynomialTransfer.P f x‖ := by
        refine sum_congr rfl fun x _ => by
          rw [← mul_assoc, Real.mul_self_sqrt (hg0 x)]
      have hr1 : ∑ x : ZMod N, Real.sqrt (g x) ^ 2 = ∑ x : ZMod N, g x :=
        sum_congr rfl fun x _ => Real.sq_sqrt (hg0 x)
      have hr2 : ∑ x : ZMod N, (Real.sqrt (g x) * ‖PolynomialTransfer.P f x‖) ^ 2 =
          ∑ x : ZMod N, g x * ‖PolynomialTransfer.P f x‖ ^ 2 :=
        sum_congr rfl fun x _ => by rw [mul_pow, Real.sq_sqrt (hg0 x)]
      rw [hl, hr1, hr2] at hcs
      have hnon : 0 ≤ ∑ x : ZMod N, g x * ‖PolynomialTransfer.P f x‖ :=
        sum_nonneg fun x _ => mul_nonneg (hg0 x) (norm_nonneg _)
      have hrt := Real.sqrt_le_sqrt hcs
      rw [Real.sqrt_sq hnon, Real.sqrt_mul (sum_nonneg fun x _ => hg0 x)] at hrt
      have hE_cs : PolynomialTransfer.E (fun x : ZMod N => g x * ‖PolynomialTransfer.P f x‖) ≤
          Real.sqrt (PolynomialTransfer.E g) *
          Real.sqrt (PolynomialTransfer.E (fun x : ZMod N => g x * ‖PolynomialTransfer.P f x‖ ^ 2)) := by
        unfold PolynomialTransfer.E
        rw [Real.sqrt_div (sum_nonneg fun x _ => hg0 x),
          Real.sqrt_div (sum_nonneg fun x _ => mul_nonneg (hg0 x) (by positivity)),
          div_mul_div_comm, Real.mul_self_sqrt hNpos.le]
        exact div_le_div_of_nonneg_right hrt hNpos.le
      exact h1.trans hE_cs
    have hEg_le : Real.sqrt (PolynomialTransfer.E g) ≤ Real.sqrt 50 * Real.sqrt C_set := by
      have h1 : PolynomialTransfer.E g ≤ 50 * C_set := by
        calc
          PolynomialTransfer.E g ≤ PolynomialTransfer.E (fun x : ZMod N => 50 * sieveBeta d a R (x.val : ℤ)) :=
            PolynomialTransfer.Emono hgle
          _ = 50 * PolynomialTransfer.E (fun x : ZMod N => sieveBeta d a R (x.val : ℤ)) :=
            PolynomialTransfer.Emul _ _
          _ ≤ 50 * C_set := mul_le_mul_of_nonneg_left hbeta_avg (by norm_num)
      have hrt := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_mul (by norm_num)] at hrt
    have hEgP_le : Real.sqrt (PolynomialTransfer.E (fun x : ZMod N => g x * ‖PolynomialTransfer.P f x‖ ^ 2)) ≤
        Real.sqrt 50 * (C_restr * S ^ (11 / 15 : ℝ)) := by
      have h1 : PolynomialTransfer.E (fun x : ZMod N => g x * ‖PolynomialTransfer.P f x‖ ^ 2) ≤
          50 * PolynomialTransfer.E (fun x : ZMod N => sieveBeta d a R (x.val : ℤ) * ‖PolynomialTransfer.P f x‖ ^ 2) := by
        rw [← PolynomialTransfer.Emul]
        exact PolynomialTransfer.Emono fun x => by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hgle x) (by positivity)
      have hrt := Real.sqrt_le_sqrt h1
      rw [Real.sqrt_mul (by norm_num)] at hrt
      have hr := hrestr d a N ha had hdN hcop f
      rw [hf_lq] at hr
      exact hrt.trans (mul_le_mul_of_nonneg_left hr (by positivity))
    have hS_bound : S ≤ M_abs * S ^ (11 / 15 : ℝ) := by
      have h50 : Real.sqrt 50 * Real.sqrt 50 = 50 := Real.mul_self_sqrt (by norm_num)
      calc
        S ≤ (Real.sqrt 50 * Real.sqrt C_set) * (Real.sqrt 50 * (C_restr * S ^ (11 / 15 : ℝ))) :=
          hS_cs.trans (mul_le_mul hEg_le hEgP_le (Real.sqrt_nonneg _) (by positivity))
        _ = (Real.sqrt 50 * Real.sqrt 50 * Real.sqrt C_set * C_restr) * S ^ (11 / 15 : ℝ) := by ring
        _ = (50 * Real.sqrt C_set * C_restr) * S ^ (11 / 15 : ℝ) := by rw [h50]
        _ ≤ M_abs * S ^ (11 / 15 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    have hS415 : S ^ (4 / 15 : ℝ) ≤ M_abs := by
      have hdiv := div_le_div_of_nonneg_right hS_bound (Real.rpow_pos_of_pos hSpos (11 / 15 : ℝ)).le
      have hl : S / S ^ (11 / 15 : ℝ) = S ^ (4 / 15 : ℝ) := by
        conv_lhs => arg 1; rw [← Real.rpow_one S]
        rw [← Real.rpow_sub hSpos]; norm_num
      have hr : M_abs * S ^ (11 / 15 : ℝ) / S ^ (11 / 15 : ℝ) = M_abs :=
        mul_div_cancel_right₀ M_abs (Real.rpow_pos_of_pos hSpos _).ne'
      rw [hl, hr] at hdiv
      exact hdiv
    change S ≤ M_abs ^ (15 / 4 : ℝ)
    have hpow := Real.rpow_le_rpow (by positivity) hS415 (by norm_num : (0 : ℝ) ≤ 15 / 4)
    rw [← Real.rpow_mul hSpos.le] at hpow
    norm_num at hpow
    exact hpow

/-! ### Section 4: Fourier decay of the W-tricked prime weight -/

def nu (d a N : ℕ) (x : ZMod N) : ℝ :=
  ((d.totient : ℝ) / (d : ℝ)) * GoldbachMajorArc.primeWeight (d * x.val + a)

lemma nat_log2_le_two_log {n : ℕ} (hn : 1 ≤ n) :
    (Nat.log 2 n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
  have h1 : (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_pow] at h2
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 n)]

lemma log_pow_le_rpow (K : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → (Real.log x) ^ K ≤ C * x ^ c := by
  cases K with
  | zero =>
    refine ⟨1, one_pos, fun x hx => ?_⟩
    simpa using Real.one_le_rpow hx hc.le
  | succ k =>
    let K' : ℕ := k + 1
    let c' : ℝ := c / (K' : ℝ)
    have hc' : 0 < c' := div_pos hc (by positivity)
    refine ⟨(1 + 1 / c') ^ K', by positivity, fun x hx => ?_⟩
    have h1 : Real.log x ≤ (1 + 1 / c') * x ^ c' := by
      have := one_add_log_le_rpow c' hc' hx
      linarith
    have hpow := pow_le_pow_left₀ (Real.log_nonneg hx) h1 K'
    rw [mul_pow, ← Real.rpow_natCast (x ^ c'), ← Real.rpow_mul (by linarith)] at hpow
    have hc_eq : c' * (K' : ℝ) = c := div_mul_cancel₀ c (by positivity)
    rwa [hc_eq] at hpow

lemma exists_nat_log_ge (M : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → M ≤ Real.log (N : ℝ) := by
  let N₀ : ℕ := max 2 (⌈Real.exp M⌉₊ + 1)
  refine ⟨N₀, le_max_left _ _, fun N hN => ?_⟩
  have hge : Real.exp M ≤ (N : ℝ) := by
    have h1 : Real.exp M ≤ (⌈Real.exp M⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp M⌉₊ : ℝ) ≤ (N₀ : ℝ) := by
      exact_mod_cast (Nat.le_succ _).trans (le_max_right 2 _)
    have h3 : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hlog := Real.log_le_log (Real.exp_pos M) hge
  rwa [Real.log_exp] at hlog

lemma norm_ram_one_le (q : ℕ) : ‖GoldbachMajorArc.ram q 1‖ ≤ 1 := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [GoldbachMajorArc.ram]
  | prime_pow p k hp =>
    cases k with
    | zero => simp [GoldbachMajorArc.ram_one]
    | succ j =>
      rw [GoldbachMajorArc.ram_primePower p j 1 hp]
      have hnot1 : ¬ (p ^ (j + 1) ∣ 1) := by
        intro hd
        have h1 := Nat.dvd_one.mp hd
        have hlt := Nat.one_lt_pow (by omega : j + 1 ≠ 0) hp.one_lt
        omega
      rw [ite_eq_right hnot1]
      cases j with
      | zero => simp
      | succ j' =>
        have hnot2 : ¬ (p ^ (j' + 1) ∣ 1) := by
          intro hd
          have h1 := Nat.dvd_one.mp hd
          have hlt := Nat.one_lt_pow (by omega : j' + 1 ≠ 0) hp.one_lt
          omega
        simp [hnot2]
  | coprime a b ha hb hcop iha ihb =>
    rw [GoldbachMajorArc.ram_mul (by omega) (by omega) hcop, norm_mul]
    exact mul_le_one₀ iha (norm_nonneg _) ihb

lemma classMass_ap_eq {d a q k m : ℕ} (hd : 1 ≤ d) (ha : a < d) (hq : 1 ≤ q) (hm : m < q) :
    ∑ n ∈ (range k).filter (fun n => n % q = m), GoldbachMajorArc.primeWeight (d * n + a) =
      GoldbachMajorArc.classMass (d * k) (d * q) (d * m + a) := by
  unfold GoldbachMajorArc.classMass
  refine Finset.sum_bij (fun n _ => d * n + a) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro n hn
    have hnk : n < k := mem_range.mp (mem_filter.mp hn).1
    have hnm : n % q = m := (mem_filter.mp hn).2
    have hlt : d * n + a < d * k := by nlinarith
    have hmod : (d * n + a) % (d * q) = d * m + a := by
      let t := n / q
      have hdiv : n = q * t + m := by dsimp [t]; rw [← hnm]; exact (Nat.div_add_mod n q).symm
      have heq : d * n + a = (d * q) * t + (d * m + a) := by
        rw [hdiv]; ring
      have hrem_lt : d * m + a < d * q := by nlinarith
      rw [heq, Nat.mul_add_mod, Nat.mod_eq_of_lt hrem_lt]
    exact mem_filter.mpr ⟨mem_range.mpr hlt, hmod⟩
  · intro n₁ _ n₂ _ heq
    have : d * n₁ = d * n₂ := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  · intro x hx
    have hxk : x < d * k := mem_range.mp (mem_filter.mp hx).1
    have hxm : x % (d * q) = d * m + a := (mem_filter.mp hx).2
    let t := x / (d * q)
    let n := q * t + m
    have hx_eq : x = (d * q) * t + (d * m + a) := by
      rw [← hxm]; exact (Nat.div_add_mod x (d * q)).symm
    have hdn : d * n + a = x := by dsimp [n]; linarith
    have hnk : n < k := by nlinarith
    have hnm : n % q = m := by dsimp [n]; rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hm]
    exact ⟨n, mem_filter.mpr ⟨mem_range.mpr hnk, hnm⟩, hdn⟩

lemma ap_major_prefix_eq {d a q b k : ℕ} (hd : 1 ≤ d) (ha : a < d) (hq : 1 ≤ q) :
    ∑ n ∈ range k,
        ((((d.totient : ℝ) / (d : ℝ) * GoldbachMajorArc.primeWeight (d * n + a) : ℝ) : ℂ) *
          phase ((n : ℝ) * ((b : ℝ) / (q : ℝ)))) -
      (k : ℂ) * ((((d.totient : ℝ) / ((d * q).totient : ℝ) : ℝ) : ℂ) *
        ∑ m ∈ (range q).filter (fun m => (d * m + a).Coprime (d * q)),
          phase ((m : ℝ) * ((b : ℝ) / (q : ℝ)))) =
    (((d.totient : ℝ) / (d : ℝ) : ℝ) : ℂ) *
      ∑ m ∈ range q, (GoldbachMajorArc.classError (d * k) (d * q) (d * m + a) : ℂ) *
        phase ((m : ℝ) * ((b : ℝ) / (q : ℝ))) := by
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hfirst : ∑ n ∈ range k,
        ((((d.totient : ℝ) / (d : ℝ) * GoldbachMajorArc.primeWeight (d * n + a) : ℝ) : ℂ) *
          phase ((n : ℝ) * ((b : ℝ) / (q : ℝ)))) =
      (((d.totient : ℝ) / (d : ℝ) : ℝ) : ℂ) *
        ∑ m ∈ range q, (GoldbachMajorArc.classMass (d * k) (d * q) (d * m + a) : ℂ) *
          phase ((m : ℝ) * ((b : ℝ) / (q : ℝ))) := by
    have hmaps : ∀ n ∈ range k, n % q ∈ range q := fun n _ => mem_range.mpr (Nat.mod_lt n (by omega))
    rw [← sum_fiberwise_of_maps_to hmaps, mul_sum]
    refine sum_congr rfl fun m hm => ?_
    rw [← classMass_ap_eq hd ha hq (mem_range.mp hm), Complex.ofReal_sum, sum_mul, mul_sum]
    refine sum_congr rfl fun n hn => ?_
    have hnm : n % q = m := (mem_filter.mp hn).2
    have hph : phase ((n : ℝ) * ((b : ℝ) / (q : ℝ))) = phase ((m : ℝ) * ((b : ℝ) / (q : ℝ))) := by
      let t := n / q
      have hdiv : n = q * t + m := by dsimp [t]; rw [← hnm]; exact (Nat.div_add_mod n q).symm
      apply phase_eq_of_int_sub (k := ((t * b : ℕ) : ℤ))
      have hnr : (n : ℝ) = (q : ℝ) * (t : ℝ) + (m : ℝ) := by exact_mod_cast hdiv
      have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
      rw [hnr]; push_cast; field_simp; ring
    rw [hph]; push_cast; ring
  have hsecond : (k : ℂ) * ((((d.totient : ℝ) / ((d * q).totient : ℝ) : ℝ) : ℂ) *
        ∑ m ∈ (range q).filter (fun m => (d * m + a).Coprime (d * q)),
          phase ((m : ℝ) * ((b : ℝ) / (q : ℝ)))) =
      (((d.totient : ℝ) / (d : ℝ) : ℝ) : ℂ) *
        ∑ m ∈ range q,
          (((if (d * m + a).Coprime (d * q) then ((d * k : ℕ) : ℝ) / ((d * q).totient : ℝ) else 0 : ℝ) : ℂ) *
            phase ((m : ℝ) * ((b : ℝ) / (q : ℝ)))) := by
    rw [mul_sum, mul_sum, sum_filter, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    by_cases hc : (d * m + a).Coprime (d * q)
    · rw [ite_eq_left hc, ite_eq_left hc]
      push_cast
      have hdneC : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
      field_simp
    · rw [ite_eq_right hc, ite_eq_right hc]; simp
  rw [hfirst, hsecond, ← mul_sub, ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun m _ => ?_
  rw [← sub_mul, ← Complex.ofReal_sub]
  rfl

lemma major_coeff_eq_zero_of_not_coprime {d a q b : ℕ} (hd : 1 ≤ d) (hq : 2 ≤ q)
    (hb : b.Coprime q) (hncop : ¬ q.Coprime d) :
    ∑ m ∈ (range q).filter (fun m => (d * m + a).Coprime (d * q)),
      phase ((m : ℝ) * ((b : ℝ) / (q : ℝ))) = 0 := by
  have hgne : Nat.gcd q d ≠ 1 := fun h => hncop (Nat.coprime_iff_gcd_eq_one.mpr h)
  obtain ⟨p, hpp, hpg⟩ := Nat.exists_prime_and_dvd hgne
  have hpq : p ∣ q := hpg.trans (Nat.gcd_dvd_left q d)
  have hpd : p ∣ d := hpg.trans (Nat.gcd_dvd_right q d)
  let s : ℕ := q / p
  have hps : p * s = q := Nat.mul_div_cancel' hpq
  have hds_dvd : q ∣ d * s := by
    obtain ⟨d', hd'⟩ := hpd
    refine ⟨d', ?_⟩
    calc
      d * s = (p * d') * s := by rw [hd']
      _ = (p * s) * d' := by ring
      _ = q * d' := by rw [hps]
  let S := (range q).filter (fun m => (d * m + a).Coprime (d * q))
  let U : ℂ := ∑ m ∈ S, phase ((m : ℝ) * ((b : ℝ) / (q : ℝ)))
  have hcop_shift : ∀ m : ℕ,
      (d * ((m + s) % q) + a).Coprime (d * q) ↔ (d * m + a).Coprime (d * q) := by
    intro m
    let m' := (m + s) % q
    have hdiff : ∃ t : ℕ, m + s = q * t + m' := ⟨(m + s) / q, (Nat.div_add_mod (m + s) q).symm⟩
    obtain ⟨t, ht⟩ := hdiff
    have hrel : d * m + a + d * s = d * q * t + (d * m' + a) := by
      have : d * (m + s) = d * (q * t + m') := congrArg (d * ·) ht
      linarith
    have hprime_iff : ∀ r : ℕ, r.Prime → r ∣ d * q → (r ∣ d * m' + a ↔ r ∣ d * m + a) := by
      intro r hr hrdq
      rcases hr.prime.dvd_mul.mp hrdq with hrd | hrq
      · have h1 : r ∣ d * m' := dvd_mul_of_dvd_left hrd m'
        have h2 : r ∣ d * m := dvd_mul_of_dvd_left hrd m
        constructor
        · intro h; exact dvd_add h2 ((Nat.dvd_add_right h1).mp h)
        · intro h; exact dvd_add h1 ((Nat.dvd_add_right h2).mp h)
      · have h1 : r ∣ d * s := hrq.trans hds_dvd
        have h2 : r ∣ d * q * t := dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hrq d) t
        constructor
        · intro h
          have hsum : r ∣ d * m + a + d * s := by rw [hrel]; exact dvd_add h2 h
          exact (Nat.dvd_add_left h1).mp hsum
        · intro h
          have hsum : r ∣ d * q * t + (d * m' + a) := by rw [← hrel]; exact dvd_add h h1
          exact (Nat.dvd_add_right h2).mp hsum
    have hiff_cop : ∀ u : ℕ, u.Coprime (d * q) ↔ ∀ r : ℕ, r.Prime → r ∣ d * q → ¬ (r ∣ u) := by
      intro u
      constructor
      · intro hc r hr hrdq hru
        exact hr.not_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd hru hrdq)
      · intro hall
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hne
        obtain ⟨r, hr, hrg⟩ := Nat.exists_prime_and_dvd hne
        exact hall r hr (hrg.trans (Nat.gcd_dvd_right _ _)) (hrg.trans (Nat.gcd_dvd_left _ _))
    rw [hiff_cop, hiff_cop]
    exact forall_congr' fun r => forall_congr' fun hr => forall_congr' fun hrdq =>
      not_congr (hprime_iff r hr hrdq)
  have hshift_eq : U = phase ((b : ℝ) / (p : ℝ)) * U := by
    dsimp [U]
    rw [mul_sum]
    symm
    refine Finset.sum_bij (fun m _ => (m + s) % q) ?_ ?_ ?_ ?_
    · intro m hm
      have hcop_m := (mem_filter.mp hm).2
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (by omega)), (hcop_shift m).mpr hcop_m⟩
    · intro m₁ h₁ m₂ h₂ heq
      have hm1 : m₁ < q := mem_range.mp (mem_filter.mp h₁).1
      have hm2 : m₂ < q := mem_range.mp (mem_filter.mp h₂).1
      have h1 : (m₁ + s) % q = (m₂ + s) % q := heq
      have hsub : ((m₁ : ZMod q) + (s : ZMod q)) = ((m₂ : ZMod q) + (s : ZMod q)) := by
        rw [← Nat.cast_add, ← Nat.cast_add, ZMod.natCast_eq_natCast_iff', h1]
      have hmeq : (m₁ : ZMod q) = (m₂ : ZMod q) := add_right_cancel hsub
      have hmod := (ZMod.natCast_eq_natCast_iff' m₁ m₂ q).mp hmeq
      rwa [Nat.mod_eq_of_lt hm1, Nat.mod_eq_of_lt hm2] at hmod
    · intro m' hm'
      have hm'lt : m' < q := mem_range.mp (mem_filter.mp hm').1
      have hm'cop := (mem_filter.mp hm').2
      have hsle : s ≤ q := Nat.div_le_self q p
      let m := (m' + (q - s)) % q
      have hmlt : m < q := Nat.mod_lt _ (by omega)
      have hback : (m + s) % q = m' := by
        dsimp [m]
        rw [Nat.mod_add_mod, add_assoc, Nat.sub_add_cancel hsle, Nat.add_mod_right,
          Nat.mod_eq_of_lt hm'lt]
      refine ⟨m, mem_filter.mpr ⟨mem_range.mpr hmlt, (hcop_shift m).mp (hback ▸ hm'cop)⟩, hback⟩
    · intro m _
      rw [← phase_add]
      let t := (m + s) / q
      have hdiv : m + s = q * t + (m + s) % q := by dsimp [t]; exact (Nat.div_add_mod (m + s) q).symm
      apply phase_eq_of_int_sub (k := ((t * b : ℕ) : ℤ))
      have hmr : (m : ℝ) + (s : ℝ) = (q : ℝ) * (t : ℝ) + (((m + s) % q : ℕ) : ℝ) := by
        exact_mod_cast hdiv
      have hpr : (p : ℝ) * (s : ℝ) = (q : ℝ) := by exact_mod_cast hps
      have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
      have hpne : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
      push_cast; field_simp
      have h1 : (p : ℝ) * (m : ℝ) + (q : ℝ) - (p : ℝ) * (((m + s) % q : ℕ) : ℝ) =
          (p : ℝ) * (q : ℝ) * (t : ℝ) := by nlinarith only [hmr, hpr]
      nlinarith only [h1]
  have hph_ne : phase ((b : ℝ) / (p : ℝ)) ≠ 1 := by
    intro heq
    have hdist : distInt ((b : ℝ) / (p : ℝ)) = 0 := by
      have h1 := norm_phase_sub_one_ge ((b : ℝ) / (p : ℝ))
      have h0 := distInt_nonneg ((b : ℝ) / (p : ℝ))
      rw [heq, sub_self, norm_zero] at h1
      linarith
    unfold distInt at hdist
    rw [abs_eq_zero, sub_eq_zero] at hdist
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hmul : (b : ℝ) = (round ((b : ℝ) / (p : ℝ)) : ℝ) * (p : ℝ) := by
      have h1 := congrArg (· * (p : ℝ)) hdist
      rwa [div_mul_cancel₀ _ hppos.ne'] at h1
    have hint : (b : ℤ) = round ((b : ℝ) / (p : ℝ)) * (p : ℤ) := by exact_mod_cast hmul
    have hpb : p ∣ b := Int.ofNat_dvd.mp ⟨round ((b : ℝ) / (p : ℝ)), by linarith⟩
    exact hpp.not_dvd_one (hb.gcd_eq_one ▸ Nat.dvd_gcd hpb hpq)
  have hmul0 : (1 - phase ((b : ℝ) / (p : ℝ))) * U = 0 := by
    rw [sub_mul, one_mul, ← hshift_eq, sub_self]
  exact (mul_eq_zero.mp hmul0).resolve_left (sub_ne_zero.mpr (Ne.symm hph_ne))

lemma norm_major_coeff_le_of_coprime {d a q b : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q)
    (had : a.Coprime d) (hb : b.Coprime q) (hcop : q.Coprime d) :
    ‖((((d.totient : ℝ) / ((d * q).totient : ℝ) : ℝ) : ℂ) *
      ∑ m ∈ (range q).filter (fun m => (d * m + a).Coprime (d * q)),
        phase ((m : ℝ) * ((b : ℝ) / (q : ℝ))))‖ ≤
      1 / (q.totient : ℝ) := by
  let : NeZero q := ⟨by omega⟩
  have htot : (d * q).totient = d.totient * q.totient := Nat.totient_mul hcop.symm
  have hratio : (d.totient : ℝ) / ((d * q).totient : ℝ) = 1 / (q.totient : ℝ) := by
    rw [htot, Nat.cast_mul]
    have hdphi : (d.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (by omega)).ne'
    field_simp
  rw [hratio, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by
    exact div_pos one_pos (by exact_mod_cast Nat.totient_pos.mpr hq))]
  -- Bijection m ↦ (d * m + a) % q from S onto reducedRes q
  let dInv : ℕ := ((d : ZMod q)⁻¹).val
  have hdInv_mul : (d : ZMod q) * (dInv : ZMod q) = 1 := by
    dsimp [dInv]; rw [ZMod.natCast_zmod_val]; exact ZMod.coe_mul_inv_eq_one d hcop.symm
  have hdInv_cop : dInv.Coprime q := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hpp, hpg⟩ := Nat.exists_prime_and_dvd hne
    have hpdI : p ∣ dInv := hpg.trans (Nat.gcd_dvd_left _ _)
    have hpq : p ∣ q := hpg.trans (Nat.gcd_dvd_right _ _)
    have hmod1 : (d * dInv) % q = 1 % q := by
      rw [← ZMod.natCast_eq_natCast_iff', Nat.cast_mul, Nat.cast_one, hdInv_mul]
    have h1 : (d * dInv) % q = 1 := by
      by_cases hq1 : q = 1
      · subst hq1; exact absurd (Nat.dvd_one.mp hpq) hpp.ne_one
      · rwa [Nat.mod_eq_of_lt (by omega : 1 < q)] at hmod1
    have hp1 : p ∣ 1 := by
      have hdiv := Nat.div_add_mod (d * dInv) q
      rw [h1] at hdiv
      have hpL : p ∣ d * dInv := dvd_mul_of_dvd_right hpdI d
      have hpQ : p ∣ q * (d * dInv / q) := dvd_mul_of_dvd_left hpq _
      exact (Nat.dvd_add_right hpQ).mp (hdiv.symm ▸ hpL)
    exact hpp.not_dvd_one hp1
  have hsum_eq : ∑ m ∈ (range q).filter (fun m => (d * m + a).Coprime (d * q)),
        phase ((m : ℝ) * ((b : ℝ) / (q : ℝ))) =
      phase (-((a * dInv * b : ℕ) : ℝ) / (q : ℝ)) * GoldbachMajorArc.ram q (dInv * b) := by
    unfold GoldbachMajorArc.ram
    rw [mul_sum]
    refine Finset.sum_bij (fun m _ => (d * m + a) % q) ?_ ?_ ?_ ?_
    · intro m hm
      have hcop_dq := (mem_filter.mp hm).2
      have hcop_q : (d * m + a).Coprime q := hcop_dq.coprime_dvd_right (dvd_mul_left q d)
      have hcop_mod : ((d * m + a) % q).Coprime q := by
        rw [Nat.coprime_iff_gcd_eq_one, ← Nat.gcd_rec, Nat.gcd_comm]
        exact hcop_q.gcd_eq_one
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (by omega)), hcop_mod⟩
    · intro m₁ h₁ m₂ h₂ heq
      have hm1 : m₁ < q := mem_range.mp (mem_filter.mp h₁).1
      have hm2 : m₂ < q := mem_range.mp (mem_filter.mp h₂).1
      have hz : ((d * m₁ + a : ℕ) : ZMod q) = ((d * m₂ + a : ℕ) : ZMod q) :=
        (ZMod.natCast_eq_natCast_iff' _ _ q).mpr heq
      push_cast at hz
      have hdm : (d : ZMod q) * (m₁ : ZMod q) = (d : ZMod q) * (m₂ : ZMod q) := add_right_cancel hz
      have hm : (m₁ : ZMod q) = (m₂ : ZMod q) := by
        have := congrArg ((dInv : ZMod q) * ·) hdm
        simp only [← mul_assoc, mul_comm (dInv : ZMod q) (d : ZMod q), hdInv_mul, one_mul] at this
        exact this
      have hmod := (ZMod.natCast_eq_natCast_iff' m₁ m₂ q).mp hm
      rwa [Nat.mod_eq_of_lt hm1, Nat.mod_eq_of_lt hm2] at hmod
    · intro u hu
      have hult : u < q := mem_range.mp (mem_filter.mp hu).1
      have hucop : u.Coprime q := (mem_filter.mp hu).2
      let m : ℕ := (((u : ZMod q) - (a : ZMod q)) * (dInv : ZMod q)).val
      have hmlt : m < q := ZMod.val_lt _
      have hz : ((d * m + a : ℕ) : ZMod q) = (u : ZMod q) := by
        push_cast
        have hmv : (m : ZMod q) = ((u : ZMod q) - (a : ZMod q)) * (dInv : ZMod q) :=
          ZMod.natCast_zmod_val _
        rw [hmv]
        calc
          (d : ZMod q) * (((u : ZMod q) - (a : ZMod q)) * (dInv : ZMod q)) + (a : ZMod q)
              = ((u : ZMod q) - (a : ZMod q)) * ((d : ZMod q) * (dInv : ZMod q)) + (a : ZMod q) := by ring
          _ = (u : ZMod q) := by rw [hdInv_mul]; ring
      have hmod : (d * m + a) % q = u := by
        have := (ZMod.natCast_eq_natCast_iff' (d * m + a) u q).mp hz
        rwa [Nat.mod_eq_of_lt hult] at this
      have hcop_d : (d * m + a).Coprime d := by
        rw [add_comm, mul_comm]; exact (Nat.coprime_add_mul_right_left a d m).mpr had
      have hcop_q : (d * m + a).Coprime q := by
        rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec, hmod]
        exact hucop.gcd_eq_one
      exact ⟨m, mem_filter.mpr ⟨mem_range.mpr hmlt, hcop_d.mul_right hcop_q⟩, hmod⟩
    · intro m _
      change phase ((m : ℝ) * ((b : ℝ) / (q : ℝ))) =
        phase (-((a * dInv * b : ℕ) : ℝ) / (q : ℝ)) *
          phase (((dInv * b : ℕ) : ℝ) * (((d * m + a) % q : ℕ) : ℝ) / (q : ℝ))
      rw [← phase_add]
      let u := (d * m + a) % q
      have hz : (m : ZMod q) = (((u : ZMod q) - (a : ZMod q)) * (dInv : ZMod q)) := by
        have hu_eq : (u : ZMod q) = (d : ZMod q) * (m : ZMod q) + (a : ZMod q) := by
          dsimp [u]; rw [ZMod.natCast_mod]; push_cast; rfl
        rw [hu_eq]
        calc
          (m : ZMod q) = (m : ZMod q) * ((d : ZMod q) * (dInv : ZMod q)) := by rw [hdInv_mul, mul_one]
          _ = ((d : ZMod q) * (m : ZMod q) + (a : ZMod q) - (a : ZMod q)) * (dInv : ZMod q) := by ring
      have hcong : ((m * b : ℕ) : ZMod q) = (((u : ℤ) * (dInv * b : ℕ) - (a * dInv * b : ℕ) : ℤ) : ZMod q) := by
        push_cast; rw [hz]; ring
      have hdvd : (q : ℤ) ∣ (((m * b : ℕ) : ℤ) - ((u : ℤ) * ((dInv * b : ℕ) : ℤ) - ((a * dInv * b : ℕ) : ℤ))) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast at hcong ⊢
        rw [sub_eq_zero]; exact hcong
      obtain ⟨k, hk⟩ := hdvd
      apply phase_eq_of_int_sub (k := k)
      have hkr : ((m * b : ℕ) : ℝ) - ((u : ℝ) * ((dInv * b : ℕ) : ℝ) - ((a * dInv * b : ℕ) : ℝ)) =
          (q : ℝ) * (k : ℝ) := by exact_mod_cast hk
      have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
      push_cast at hkr ⊢
      field_simp
      nlinarith
  rw [hsum_eq, norm_mul, norm_phase, one_mul,
    GoldbachMajorArc.ram_unit q (dInv * b) (hdInv_cop.mul_left hb)]
  calc
    (1 / (q.totient : ℝ)) * ‖GoldbachMajorArc.ram q 1‖
        ≤ (1 / (q.totient : ℝ)) * 1 := mul_le_mul_of_nonneg_left (norm_ram_one_le q) (by positivity)
    _ = 1 / (q.totient : ℝ) := mul_one _

set_option maxHeartbeats 800000 in
lemma nu_fourier_zero {d a : ℕ} (hd : 1 ≤ d) (ha : a < d) (hcop : a.Coprime d)
    {z : ℕ} (hz : 2 ≤ z) (hprimes : ∀ p : ℕ, p.Prime → p ≤ z → p ∣ d)
    {ε : ℝ} (hε : 2 / (z : ℝ) ≤ ε) :
    ∃ N₀ : ℕ, ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ‖PolynomialTransfer.F (fun x => nu d a N x - 1) 0‖ ≤ ε := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd2_nat : 2 ≤ d := Nat.le_of_dvd (by omega) (hprimes 2 Nat.prime_two hz)
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2_nat
  obtain ⟨M_p, hM_p, x_p, hx_p, hprog⟩ :=
    GoldbachMajorArc.prime_progression_error 2 1 (by norm_num) (by norm_num)
  obtain ⟨C_l1, hC_l1, hl1⟩ := log_pow_le_rpow 1 (1 / 4 : ℝ) (by norm_num)
  obtain ⟨K_big, hK_100, hK_d, hK_mp, hK_xp, hK_cl⟩ :
      ∃ K_big : ℝ, 100 ≤ K_big ∧ (d : ℝ) ≤ K_big ∧ 100 * M_p * (d : ℝ) * (z : ℝ) ≤ K_big ∧
        x_p ≤ K_big ∧ 100 * (C_l1 + 1) * (d : ℝ) ^ 2 * (z : ℝ) ≤ K_big := by
    refine ⟨max (max (max 100 (d : ℝ)) (100 * M_p * (d : ℝ) * (z : ℝ)))
      (max x_p (100 * (C_l1 + 1) * (d : ℝ) ^ 2 * (z : ℝ))), ?_, ?_, ?_, ?_, ?_⟩
    · exact le_max_of_le_left (le_max_of_le_left (le_max_left _ _))
    · exact le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
    · exact le_max_of_le_left (le_max_right _ _)
    · exact le_max_of_le_right (le_max_left _ _)
    · exact le_max_of_le_right (le_max_right _ _)
  obtain ⟨N_log, hN_log2, hN_log⟩ := exists_nat_log_ge K_big
  refine ⟨max N_log (max (⌈K_big ^ 8⌉₊ + 100) (d ^ 4 + 100)), ?_⟩
  intro N inst hN
  have hN2 : 2 ≤ N := (hN_log2.trans (le_max_left _ _)).trans hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hlogN_ge : K_big ≤ Real.log (N : ℝ) := hN_log N ((le_max_left _ _).trans hN)
  have hlogN_pos : 100 ≤ Real.log (N : ℝ) := hK_100.trans hlogN_ge
  have hN_ge_K8 : K_big ^ 8 ≤ (N : ℝ) := by
    have h1 : K_big ^ 8 ≤ (⌈K_big ^ 8⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ⌈K_big ^ 8⌉₊ ≤ N :=
      (Nat.le_add_right _ 100).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
    have h3 : (⌈K_big ^ 8⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
    linarith
  have hd_le_N : (d : ℝ) ^ 4 ≤ (N : ℝ) := by
    have h1 : d ^ 4 ≤ N :=
      (Nat.le_add_right _ 100).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
    exact_mod_cast h1
  let M : ℕ := d * N - 1
  have hM1 : M + 1 = d * N := Nat.sub_add_cancel (by nlinarith)
  have hM_ge_N : N ≤ M := by dsimp [M]; nlinarith
  have hMr_ge_N : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge_N
  have hMr_le_dN : (M : ℝ) ≤ (d : ℝ) * (N : ℝ) := by
    exact_mod_cast (Nat.sub_le (d * N) 1)
  have hlogM_ge : Real.log (N : ℝ) ≤ Real.log (M : ℝ) := Real.log_le_log hNpos hMr_ge_N
  rw [PolynomialTransfer.Fzero, Complex.norm_real, Real.norm_eq_abs,
    PolynomialTransfer.Esub, PolynomialTransfer.Econst]
  have hEnu : PolynomialTransfer.E (nu d a N) =
      ((d.totient : ℝ) / ((d : ℝ) * (N : ℝ))) * GoldbachMajorArc.classMass (M + 1) d a := by
    unfold PolynomialTransfer.E nu
    have hbi : ∑ x : ZMod N, GoldbachMajorArc.primeWeight (d * x.val + a) =
        GoldbachMajorArc.classMass (M + 1) d a := by
      have h1 : ∑ x : ZMod N, GoldbachMajorArc.primeWeight (d * x.val + a) =
          ∑ n ∈ range N, GoldbachMajorArc.primeWeight (d * n + a) := by
        refine Finset.sum_bij (fun x _ => x.val) (fun x _ => mem_range.mpr x.val_lt) ?_ ?_ (fun _ _ => rfl)
        · intro x₁ _ x₂ _ heq; exact ZMod.val_injective N heq
        · intro n hn; exact ⟨(n : ZMod N), mem_univ _, ZMod.val_natCast_of_lt (mem_range.mp hn)⟩
      rw [h1, hM1]
      have hfilt : (range N).filter (fun n => n % 1 = 0) = range N := by simp [Nat.mod_one]
      have hap := classMass_ap_eq (d := d) (a := a) (q := 1) (k := N) (m := 0) hd ha le_rfl zero_lt_one
      simpa [hfilt] using hap
    rw [← mul_sum, hbi]; ring
  rw [hEnu]
  have hM_xp : x_p ≤ (M : ℝ) := by
    have hK_le : K_big ≤ K_big ^ 8 := le_self_pow₀ (by linarith) (by decide)
    linarith
  have hd_logM : (d : ℝ) ≤ (Real.log (M : ℝ)) ^ (1 : ℝ) := by
    rw [Real.rpow_one]; exact (hK_d.trans hlogN_ge).trans hlogM_ge
  have hsw := hprog M d a hM_xp (by omega) hd_logM ha hcop
  have h1_eq : (1 : ℝ) = ((d.totient : ℝ) / ((d : ℝ) * (N : ℝ))) *
      (((M : ℝ) / (d.totient : ℝ)) + 1 / (d.totient : ℝ)) := by
    have hphi_ne : (d.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (by omega)).ne'
    have hM_eq : (M : ℝ) + 1 = (d : ℝ) * (N : ℝ) := by exact_mod_cast hM1
    field_simp; linarith
  have hdiff : ((d.totient : ℝ) / ((d : ℝ) * (N : ℝ))) * GoldbachMajorArc.classMass (M + 1) d a - 1 =
      ((d.totient : ℝ) / ((d : ℝ) * (N : ℝ))) *
        ((GoldbachMajorArc.classMass (M + 1) d a - (M : ℝ) / (d.totient : ℝ)) - 1 / (d.totient : ℝ)) := by
    conv_lhs => arg 2; rw [h1_eq]
    ring
  rw [hdiff, abs_mul, abs_of_pos (div_pos (by exact_mod_cast Nat.totient_pos.mpr (by omega)) (by positivity))]
  have htri : |(GoldbachMajorArc.classMass (M + 1) d a - (M : ℝ) / (d.totient : ℝ)) - 1 / (d.totient : ℝ)| ≤
      |GoldbachMajorArc.classMass (M + 1) d a - (M : ℝ) / (d.totient : ℝ)| + 1 := by
    have hphi1 : (1 : ℝ) ≤ (d.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hinv : |1 / (d.totient : ℝ)| ≤ 1 := by
      rw [abs_of_pos (by positivity)]; exact (div_le_one (by positivity)).mpr hphi1
    linarith [abs_sub (GoldbachMajorArc.classMass (M + 1) d a - (M : ℝ) / (d.totient : ℝ)) (1 / (d.totient : ℝ))]
  have hphi_le_d : (d.totient : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.totient_le d
  have hfac_le : (d.totient : ℝ) / ((d : ℝ) * (N : ℝ)) ≤ 1 / (N : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hNpos]; nlinarith
  have hterm1 : (1 / (N : ℝ)) * (M_p * (M : ℝ) * (Real.log (M : ℝ)) ^ (-2 : ℝ)) ≤ 1 / (4 * (z : ℝ)) := by
    have hinv : (Real.log (M : ℝ)) ^ (-2 : ℝ) ≤ 1 / (Real.log (N : ℝ)) ^ 2 := by
      rw [Real.rpow_neg (by linarith), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast, one_div]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hlogM_ge 2)
    have hK_mp' : 100 * M_p * (d : ℝ) * (z : ℝ) ≤ Real.log (N : ℝ) := hK_mp.trans hlogN_ge
    calc
      (1 / (N : ℝ)) * (M_p * (M : ℝ) * (Real.log (M : ℝ)) ^ (-2 : ℝ))
          ≤ (1 / (N : ℝ)) * (M_p * ((d : ℝ) * (N : ℝ)) * (1 / (Real.log (N : ℝ)) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hMr_le_dN hM_p.le) hinv (by positivity) (by positivity)
      _ = M_p * (d : ℝ) / (Real.log (N : ℝ)) ^ 2 := by field_simp
      _ ≤ 1 / (4 * (z : ℝ)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
  have hterm2 : (1 / (N : ℝ)) * ((Nat.log 2 M : ℝ) * Real.log (d : ℝ) + 2 * Real.sqrt (M : ℝ) * Real.log (M : ℝ) + 1) ≤
      1 / (4 * (z : ℝ)) := by
    have hMpos : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le hNpos hMr_ge_N
    have hlog2M : (Nat.log 2 M : ℝ) ≤ 2 * Real.log (M : ℝ) := nat_log2_le_two_log (by omega)
    have hlog_sq : Real.log (M : ℝ) ≤ C_l1 * (M : ℝ) ^ (1 / 4 : ℝ) := by
      simpa using hl1 (M : ℝ) (by exact_mod_cast (by omega : 1 ≤ M))
    have hM_sqrt : Real.sqrt (M : ℝ) * (M : ℝ) ^ (1 / 4 : ℝ) = (M : ℝ) ^ (3 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hMpos]; norm_num
    have hN14 : 100 * (C_l1 + 1) * (d : ℝ) ^ 2 * (z : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
      have h2 : K_big ^ 2 ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
        have := Real.rpow_le_rpow (by positivity) hN_ge_K8 (by norm_num : (0 : ℝ) ≤ 1 / 4)
        rw [← Real.rpow_natCast K_big 8, ← Real.rpow_mul (by linarith)] at this
        norm_num at this; exact this
      have : K_big ≤ K_big ^ 2 := by nlinarith only [hK_100]
      linarith
    have hM34 : (M : ℝ) ^ (3 / 4 : ℝ) ≤ (d : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) := by
      calc
        (M : ℝ) ^ (3 / 4 : ℝ) ≤ ((d : ℝ) * (N : ℝ)) ^ (3 / 4 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hMr_le_dN (by norm_num)
        _ = (d : ℝ) ^ (3 / 4 : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) := Real.mul_rpow hdpos.le hNpos.le
        _ ≤ (d : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          conv_rhs => rw [← Real.rpow_one (d : ℝ)]
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hd) (by norm_num)
    have hd_le_sqrtM : Real.log (d : ℝ) ≤ Real.sqrt (M : ℝ) := by
      have h1' : Real.log (d : ℝ) ≤ (d : ℝ) := (Real.log_le_sub_one_of_pos hdpos).trans (by linarith)
      have h2' : (d : ℝ) ≤ Real.sqrt (M : ℝ) := by
        rw [Real.le_sqrt hdpos.le hMpos.le]
        have : (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by decide)
        linarith
      linarith
    have hsum_num : (Nat.log 2 M : ℝ) * Real.log (d : ℝ) + 2 * Real.sqrt (M : ℝ) * Real.log (M : ℝ) + 1 ≤
        (4 * C_l1 + 1) * (d : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) := by
      have h1 : (Nat.log 2 M : ℝ) * Real.log (d : ℝ) ≤ 2 * C_l1 * (M : ℝ) ^ (3 / 4 : ℝ) := by
        calc
          (Nat.log 2 M : ℝ) * Real.log (d : ℝ) ≤ (2 * Real.log (M : ℝ)) * Real.sqrt (M : ℝ) :=
            mul_le_mul hlog2M hd_le_sqrtM (Real.log_nonneg (by exact_mod_cast hd)) (by positivity)
          _ ≤ (2 * (C_l1 * (M : ℝ) ^ (1 / 4 : ℝ))) * Real.sqrt (M : ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog_sq (by norm_num)) (Real.sqrt_nonneg _)
          _ = 2 * C_l1 * (Real.sqrt (M : ℝ) * (M : ℝ) ^ (1 / 4 : ℝ)) := by ring
          _ = 2 * C_l1 * (M : ℝ) ^ (3 / 4 : ℝ) := by rw [hM_sqrt]
      have h2 : 2 * Real.sqrt (M : ℝ) * Real.log (M : ℝ) ≤ 2 * C_l1 * (M : ℝ) ^ (3 / 4 : ℝ) := by
        calc
          2 * Real.sqrt (M : ℝ) * Real.log (M : ℝ)
              ≤ 2 * Real.sqrt (M : ℝ) * (C_l1 * (M : ℝ) ^ (1 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left hlog_sq (by positivity)
          _ = 2 * C_l1 * (Real.sqrt (M : ℝ) * (M : ℝ) ^ (1 / 4 : ℝ)) := by ring
          _ = 2 * C_l1 * (M : ℝ) ^ (3 / 4 : ℝ) := by rw [hM_sqrt]
      have h3 : (1 : ℝ) ≤ (d : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) := by
        have : (1 : ℝ) ≤ (N : ℝ) ^ (3 / 4 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hM34 (by positivity : (0 : ℝ) ≤ 4 * C_l1)]
    calc
      (1 / (N : ℝ)) * ((Nat.log 2 M : ℝ) * Real.log (d : ℝ) + 2 * Real.sqrt (M : ℝ) * Real.log (M : ℝ) + 1)
          ≤ (1 / (N : ℝ)) * ((4 * C_l1 + 1) * (d : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum_num (by positivity)
      _ = (4 * C_l1 + 1) * (d : ℝ) / (N : ℝ) ^ (1 / 4 : ℝ) := by
        have hNsplit : (N : ℝ) = (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) := by
          rw [← Real.rpow_add hNpos]; norm_num
        conv_lhs => arg 1; arg 2; rw [hNsplit]
        field_simp
      _ ≤ 1 / (4 * (z : ℝ)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hd_sq : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
        have hdz : (d : ℝ) * (z : ℝ) ≤ (d : ℝ) ^ 2 * (z : ℝ) :=
          mul_le_mul_of_nonneg_right hd_sq (Nat.cast_nonneg z)
        have hmul : (4 * C_l1 + 1) * ((d : ℝ) * (z : ℝ)) * 4 ≤
            100 * (C_l1 + 1) * ((d : ℝ) ^ 2 * (z : ℝ)) := by
          have : 0 ≤ (d : ℝ) * (z : ℝ) := by positivity
          nlinarith
        linarith
  calc
    ((d.totient : ℝ) / ((d : ℝ) * (N : ℝ))) *
        |(GoldbachMajorArc.classMass (M + 1) d a - (M : ℝ) / (d.totient : ℝ)) - 1 / (d.totient : ℝ)|
        ≤ (1 / (N : ℝ)) *
          (M_p * (M : ℝ) * (Real.log (M : ℝ)) ^ (-2 : ℝ) + (Nat.log 2 M : ℝ) * Real.log (d : ℝ) +
            2 * Real.sqrt (M : ℝ) * Real.log (M : ℝ) + 1) :=
      mul_le_mul hfac_le (htri.trans (add_le_add_left hsw 1)) (abs_nonneg _) (by positivity)
    _ = (1 / (N : ℝ)) * (M_p * (M : ℝ) * (Real.log (M : ℝ)) ^ (-2 : ℝ)) +
        (1 / (N : ℝ)) * ((Nat.log 2 M : ℝ) * Real.log (d : ℝ) + 2 * Real.sqrt (M : ℝ) * Real.log (M : ℝ) + 1) := by ring
    _ ≤ 1 / (4 * (z : ℝ)) + 1 / (4 * (z : ℝ)) := add_le_add hterm1 hterm2
    _ ≤ 2 / (z : ℝ) := by
      rw [← add_div, div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    _ ≤ ε := hε

set_option maxHeartbeats 1200000 in
lemma nu_fourier_major {d a : ℕ} (hd : 1 ≤ d) (ha : a < d) (hcop : a.Coprime d)
    {z : ℕ} (hz : 2 ≤ z) (hprimes : ∀ p : ℕ, p.Prime → p ≤ z → p ∣ d)
    {ε : ℝ} (hε : 2 / (z : ℝ) ≤ ε) :
    ∃ N₀ : ℕ, ∀ (N : ℕ) [NeZero N], N₀ ≤ N → ∀ (r : ZMod N), r ≠ 0 →
      (∃ q b : ℕ, 1 ≤ q ∧ q ≤ (Nat.log 2 (d * N - 1 + 2)) ^ 20 ∧ b ≤ q ∧ b.Coprime q ∧
        |((N - r.val : ℕ) : ℝ) / (N : ℝ) - (b : ℝ) / (q : ℝ)| ≤
          (2 * (((Nat.log 2 (d * N - 1 + 2)) ^ 20 : ℕ) : ℝ)) / ((q : ℝ) * (N : ℝ))) →
      ‖PolynomialTransfer.F (fun x => nu d a N x - 1) r‖ ≤ ε := by
  have hinvz_pos : (0 : ℝ) < 1 / (z : ℝ) := div_pos one_pos (by positivity)
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd2_nat : 2 ≤ d := Nat.le_of_dvd (by omega) (hprimes 2 Nat.prime_two hz)
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2_nat
  obtain ⟨M_a, hM_a, x_a, hx_a, hall⟩ :=
    GoldbachMajorArc.all_class_error 60 22 (by norm_num) (by norm_num)
  obtain ⟨C_l1, hC_l1, hl1⟩ := log_pow_le_rpow 1 (1 / 4 : ℝ) (by norm_num)
  obtain ⟨C_l3, hC_l3, hl3⟩ := log_pow_le_rpow 41 (1 / 8 : ℝ) (by norm_num)
  obtain ⟨K_big, hK_100, hK_d, hK_420, hK_ma, hK_260, hK_440, hK_xa, hK_cl1, hK_cl3⟩ :
      ∃ K_big : ℝ, 100 ≤ K_big ∧ (d : ℝ) ≤ K_big ∧ (4 : ℝ) ^ 20 * (2 : ℝ) ^ 22 ≤ K_big ∧
        34 * (M_a + 1) * (d : ℝ) * (z : ℝ) ≤ K_big ∧ (2 : ℝ) ^ 60 ≤ K_big ∧ (4 : ℝ) ^ 40 ≤ K_big ∧
        x_a ≤ K_big ∧ 6800 * (C_l1 + 1) ≤ K_big ∧ C_l3 * (d : ℝ) * (z : ℝ) * (4 : ℝ) ^ 40 ≤ K_big := by
    refine ⟨max (max (max 100 (d : ℝ)) (max ((4 : ℝ) ^ 20 * (2 : ℝ) ^ 22) (34 * (M_a + 1) * (d : ℝ) * (z : ℝ))))
      (max (max ((2 : ℝ) ^ 60) ((4 : ℝ) ^ 40)) (max x_a (max (6800 * (C_l1 + 1)) (C_l3 * (d : ℝ) * (z : ℝ) * (4 : ℝ) ^ 40)))),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_max_of_le_left (le_max_of_le_left (le_max_left _ _))
    · exact le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
    · exact le_max_of_le_left (le_max_of_le_right (le_max_left _ _))
    · exact le_max_of_le_left (le_max_of_le_right (le_max_right _ _))
    · exact le_max_of_le_right (le_max_of_le_left (le_max_left _ _))
    · exact le_max_of_le_right (le_max_of_le_left (le_max_right _ _))
    · exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
    · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
    · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))
  obtain ⟨N_log, hN_log2, hN_log⟩ := exists_nat_log_ge K_big
  refine ⟨max N_log (max (⌈K_big ^ 16⌉₊ + 100) (d ^ 4 + 100)), ?_⟩
  intro N inst hN r hr0 hmaj
  have hN2 : 2 ≤ N := (hN_log2.trans (le_max_left _ _)).trans hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hlogN_ge : K_big ≤ Real.log (N : ℝ) := hN_log N ((le_max_left _ _).trans hN)
  have hlogN_pos : 100 ≤ Real.log (N : ℝ) := hK_100.trans hlogN_ge
  have hN_ge_K16 : K_big ^ 16 ≤ (N : ℝ) := by
    have h1 : K_big ^ 16 ≤ (⌈K_big ^ 16⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ⌈K_big ^ 16⌉₊ ≤ N :=
      (Nat.le_add_right _ 100).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
    have h3 : (⌈K_big ^ 16⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
    linarith
  have hN_ge_K8 : K_big ^ 8 ≤ (N : ℝ) :=
    (pow_le_pow_right₀ (by linarith) (by decide : 8 ≤ 16)).trans hN_ge_K16
  have hd_le_N : (d : ℝ) ^ 4 ≤ (N : ℝ) := by
    have h1 : d ^ 4 ≤ N :=
      (Nat.le_add_right _ 100).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
    exact_mod_cast h1
  have hd_le_logN : (d : ℝ) ≤ Real.log (N : ℝ) := hK_d.trans hlogN_ge
  let M : ℕ := d * N - 1
  have hM1 : M + 1 = d * N := Nat.sub_add_cancel (Nat.mul_pos (by omega) (by omega))
  have hM_ge_N : N ≤ M := by
    dsimp [M]; have : 2 * N ≤ d * N := Nat.mul_le_mul_right N hd2_nat; omega
  have hlogM_le : Real.log ((M + 2 : ℕ) : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    have hle : ((M + 2 : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
      have h1 : M + 2 ≤ d * N + 1 := by omega
      have h1r : ((M + 2 : ℕ) : ℝ) ≤ (d : ℝ) * (N : ℝ) + 1 := by exact_mod_cast h1
      have hdn : (d : ℝ) ≤ (N : ℝ) / 2 := by
        have h2d : 2 * (d : ℝ) ≤ (d : ℝ) ^ 4 := by
          have h2 : (4 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith only [hd2]
          have h3 : 4 * (d : ℝ) ≤ (d : ℝ) ^ 3 := by nlinarith only [hd2, h2]
          nlinarith only [hd2, h3]
        linarith
      have hN4 : (4 : ℝ) ≤ (N : ℝ) := by
        have : (100 : ℝ) ≤ K_big ^ 8 := (le_self_pow₀ (by linarith : (1 : ℝ) ≤ K_big) (by decide)).trans' hK_100
        linarith
      nlinarith only [h1r, hdn, hN4]
    have hlog := Real.log_le_log (by positivity) hle
    rw [Real.log_pow] at hlog
    simpa using hlog
  rw [PolynomialTransfer.Fsub, PolynomialTransfer.Fone, ite_eq_right hr0, sub_zero]
  let α : ℝ := ((N - r.val : ℕ) : ℝ) / (N : ℝ)
  have hr_pos : 0 < r.val := Nat.pos_of_ne_zero fun h => hr0 ((ZMod.val_eq_zero r).mp h)
  have hr_lt : r.val < N := r.val_lt
  have hF_eq : PolynomialTransfer.F (nu d a N) r =
      ((1 / (N : ℝ) : ℝ) : ℂ) *
        ∑ n ∈ range N, (((d.totient : ℝ) / (d : ℝ) * GoldbachMajorArc.primeWeight (d * n + a) : ℝ) : ℂ) *
          phase ((n : ℝ) * α) := by
    unfold PolynomialTransfer.F PolynomialTransfer.C nu
    rw [div_eq_mul_inv, mul_comm _ ((N : ℂ)⁻¹), ← one_div]
    push_cast; congr 1
    refine Finset.sum_bij (fun x _ => x.val) (fun x _ => mem_range.mpr x.val_lt) ?_ ?_ ?_
    · intro x₁ _ x₂ _ heq; exact ZMod.val_injective N heq
    · intro n hn; exact ⟨(n : ZMod N), mem_univ _, ZMod.val_natCast_of_lt (mem_range.mp hn)⟩
    · intro x _
      rw [ch_eq_phase]
      congr 1
      apply phase_eq_of_int_sub (k := -(x.val : ℤ))
      dsimp [α]
      rw [Nat.cast_sub hr_lt.le]
      push_cast; field_simp; ring
  rw [hF_eq]
  let Q : ℕ := (Nat.log 2 (M + 2)) ^ 20
  have hQ_pos : 1 ≤ Q := by
    have : 1 ≤ Nat.log 2 (M + 2) := Nat.le_log_of_pow_le (by decide) (by omega)
    exact pow_pos (by omega : 0 < Nat.log 2 (M + 2)) 20
  have hQ_le : (Q : ℝ) ≤ (4 * Real.log (N : ℝ)) ^ 20 := by
    have h1 : (Nat.log 2 (M + 2) : ℝ) ≤ 4 * Real.log (N : ℝ) := by
      have := nat_log2_le_two_log (by omega : 1 ≤ M + 2)
      linarith
    exact_mod_cast (show ((Nat.log 2 (M + 2) : ℝ)) ^ 20 ≤ (4 * Real.log (N : ℝ)) ^ 20 from
      pow_le_pow_left₀ (by positivity) h1 20)
  obtain ⟨q, b, hq1, hqQ, hbq, hbcop, hβ_le⟩ := hmaj
  change q ≤ Q at hqQ
  change |α - (b : ℝ) / (q : ℝ)| ≤ (2 * (Q : ℝ)) / ((q : ℝ) * (N : ℝ)) at hβ_le
  let β : ℝ := α - (b : ℝ) / (q : ℝ)
  let C_main : ℂ := (((d.totient : ℝ) / ((d * q).totient : ℝ) : ℝ) : ℂ) *
    ∑ m ∈ (range q).filter (fun m => (d * m + a).Coprime (d * q)),
      phase ((m : ℝ) * ((b : ℝ) / (q : ℝ)))
  let K_sum : ℂ := ∑ n ∈ range N, phase ((n : ℝ) * β)
  let g_err : ℕ → ℂ := fun n =>
    ((((d.totient : ℝ) / (d : ℝ) * GoldbachMajorArc.primeWeight (d * n + a) : ℝ) : ℂ) *
      phase ((n : ℝ) * ((b : ℝ) / (q : ℝ)))) - C_main
  have hdiff_abel : ∑ n ∈ range N,
        ((((d.totient : ℝ) / (d : ℝ) * GoldbachMajorArc.primeWeight (d * n + a) : ℝ) : ℂ) *
          phase ((n : ℝ) * α)) - C_main * K_sum =
      ∑ n ∈ range N, phase ((n : ℝ) * β) * g_err n := by
    dsimp [K_sum, g_err]
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    have hα_eq : (n : ℝ) * α = (n : ℝ) * ((b : ℝ) / (q : ℝ)) + (n : ℝ) * β := by
      dsimp [β]; ring
    rw [hα_eq, phase_add]; ring
  let D_pref : ℝ := (Q : ℝ) * (M_a + 1) * (d : ℝ) * (N : ℝ) * (Real.log (N : ℝ)) ^ (-60 : ℝ) * (2 : ℝ) ^ 60 +
    (Q : ℝ) * (200 * (C_l1 + 1)) * (d : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ)
  have hpref_bound : ∀ k : ℕ, k ≤ N → ‖∑ n ∈ range k, g_err n‖ ≤ D_pref := by
    intro k hkN
    dsimp only [D_pref]
    have hpref_eq : ∑ n ∈ range k, g_err n =
        (((d.totient : ℝ) / (d : ℝ) : ℝ) : ℂ) *
          ∑ m ∈ range q, (GoldbachMajorArc.classError (d * k) (d * q) (d * m + a) : ℂ) *
            phase ((m : ℝ) * ((b : ℝ) / (q : ℝ))) := by
      dsimp [g_err, C_main]
      rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
      exact ap_major_prefix_eq hd ha hq1
    rw [hpref_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos (by exact_mod_cast Nat.totient_pos.mpr (by omega)) hdpos)]
    have hphi_div : (d.totient : ℝ) / (d : ℝ) ≤ 1 :=
      (div_le_one hdpos).mpr (by exact_mod_cast Nat.totient_le d)
    have htri : ‖∑ m ∈ range q, (GoldbachMajorArc.classError (d * k) (d * q) (d * m + a) : ℂ) *
          phase ((m : ℝ) * ((b : ℝ) / (q : ℝ)))‖ ≤
        ∑ m ∈ range q, |GoldbachMajorArc.classError (d * k) (d * q) (d * m + a)| := by
      refine (norm_sum_le _ _).trans (sum_le_sum fun m _ => ?_)
      rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs]
    by_cases hk_small : ((d * k : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) + 1
    · have hce_le : ∀ m ∈ range q, |GoldbachMajorArc.classError (d * k) (d * q) (d * m + a)| ≤
          (2 * C_l1 + 2) * (d : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) := by
        intro m _
        have hmass_le : GoldbachMajorArc.classMass (d * k) (d * q) (d * m + a) ≤
            ((d * k : ℕ) : ℝ) * Real.log ((d * N : ℕ) : ℝ) := by
          unfold GoldbachMajorArc.classMass
          calc
            ∑ j ∈ (range (d * k)).filter (fun j => j % (d * q) = d * m + a),
                GoldbachMajorArc.primeWeight j
                ≤ ∑ _j ∈ range (d * k), Real.log ((d * N : ℕ) : ℝ) := by
              refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun j _ _ => by
                unfold GoldbachMajorArc.primeWeight
                split_ifs with hp
                · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
                · exact le_rfl)).trans (sum_le_sum fun j hj => ?_)
              unfold GoldbachMajorArc.primeWeight
              split_ifs with hp
              · exact Real.log_le_log (by exact_mod_cast hp.pos)
                  (by exact_mod_cast ((mem_range.mp hj).le.trans (Nat.mul_le_mul_left d hkN)))
              · exact Real.log_nonneg (by exact_mod_cast (Nat.mul_pos (by omega : 0 < d) (by omega : 0 < N)))
            _ = ((d * k : ℕ) : ℝ) * Real.log ((d * N : ℕ) : ℝ) := by simp
        have hmass_nonneg : 0 ≤ GoldbachMajorArc.classMass (d * k) (d * q) (d * m + a) := by
          unfold GoldbachMajorArc.classMass
          exact sum_nonneg fun j _ => by
            unfold GoldbachMajorArc.primeWeight; split_ifs with hp
            · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
            · exact le_rfl
        have hmain_le : (if (d * m + a).Coprime (d * q) then ((d * k : ℕ) : ℝ) / ((d * q).totient : ℝ) else 0) ≤
            ((d * k : ℕ) : ℝ) := by
          split_ifs
          · exact div_le_self (by positivity)
              (by exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos (by omega : 0 < d) (by omega : 0 < q)))
          · positivity
        have habs_le : |GoldbachMajorArc.classError (d * k) (d * q) (d * m + a)| ≤
            ((d * k : ℕ) : ℝ) * Real.log ((d * N : ℕ) : ℝ) + ((d * k : ℕ) : ℝ) := by
          unfold GoldbachMajorArc.classError
          have hmain0 : 0 ≤ (if (d * m + a).Coprime (d * q) then ((d * k : ℕ) : ℝ) / ((d * q).totient : ℝ) else 0) := by
            split_ifs <;> positivity
          rw [abs_le]
          constructor <;> linarith
        have hlog_dN : Real.log ((d * N : ℕ) : ℝ) ≤ 2 * C_l1 * (N : ℝ) ^ (1 / 4 : ℝ) := by
          have h1 : Real.log ((d * N : ℕ) : ℝ) ≤ 2 * Real.log (N : ℝ) :=
            (Real.log_le_log (by positivity) (by exact_mod_cast (by omega : d * N ≤ M + 2))).trans hlogM_le
          have h2 : Real.log (N : ℝ) ≤ C_l1 * (N : ℝ) ^ (1 / 4 : ℝ) := by simpa using hl1 (N : ℝ) hN1
          linarith
        have hdk_le : ((d * k : ℕ) : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
          have h1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by rw [Real.le_sqrt zero_le_one hNpos.le]; linarith
          linarith
        have hprod : Real.sqrt (N : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) = (N : ℝ) ^ (3 / 4 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add hNpos]; norm_num
        have hsq_le : Real.sqrt (N : ℝ) ≤ (N : ℝ) ^ (3 / 4 : ℝ) := by
          rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
        have h1 : ((d * k : ℕ) : ℝ) * Real.log ((d * N : ℕ) : ℝ) ≤ 4 * C_l1 * (N : ℝ) ^ (3 / 4 : ℝ) := by
          calc
            ((d * k : ℕ) : ℝ) * Real.log ((d * N : ℕ) : ℝ)
                ≤ (2 * Real.sqrt (N : ℝ)) * (2 * C_l1 * (N : ℝ) ^ (1 / 4 : ℝ)) :=
              mul_le_mul hdk_le hlog_dN
                (Real.log_nonneg (by exact_mod_cast (Nat.mul_pos (by omega : 0 < d) (by omega : 0 < N)))) (by positivity)
            _ = 4 * C_l1 * (Real.sqrt (N : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ)) := by ring
            _ = 4 * C_l1 * (N : ℝ) ^ (3 / 4 : ℝ) := by rw [hprod]
        have hN34_0 : 0 ≤ (N : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg hNpos.le (3 / 4 : ℝ)
        have hfac : (4 * C_l1 + 2) * (N : ℝ) ^ (3 / 4 : ℝ) ≤
            ((2 * C_l1 + 2) * (d : ℝ)) * (N : ℝ) ^ (3 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right (by nlinarith only [hd2, hC_l1]) hN34_0
        linarith
      have hsum_le : ∑ m ∈ range q, |GoldbachMajorArc.classError (d * k) (d * q) (d * m + a)| ≤
          (Q : ℝ) * ((2 * C_l1 + 2) * (d : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ)) := by
        calc
          ∑ m ∈ range q, |GoldbachMajorArc.classError (d * k) (d * q) (d * m + a)|
              ≤ ∑ _m ∈ range q, (2 * C_l1 + 2) * (d : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) := sum_le_sum hce_le
          _ = (q : ℝ) * ((2 * C_l1 + 2) * (d : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ)) := by
            rw [sum_const, card_range, nsmul_eq_mul]
          _ ≤ (Q : ℝ) * ((2 * C_l1 + 2) * (d : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hqQ) (by positivity)
      have hfirst_nonneg : 0 ≤ (Q : ℝ) * (M_a + 1) * (d : ℝ) * (N : ℝ) *
          (Real.log (N : ℝ)) ^ (-60 : ℝ) * (2 : ℝ) ^ 60 := by positivity
      calc
        ((d.totient : ℝ) / (d : ℝ)) * _ ≤ 1 * ((Q : ℝ) * ((2 * C_l1 + 2) * (d : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ))) :=
          mul_le_mul hphi_div (htri.trans hsum_le) (norm_nonneg _) zero_le_one
        _ ≤ _ := by
          have hpos_fac : 0 ≤ (Q : ℝ) * (d : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) := by positivity
          nlinarith only [hfirst_nonneg, hpos_fac, hC_l1]
    · push Not at hk_small
      let m_idx : ℕ := d * k - 1
      have hdk_pos : 1 ≤ d * k := by
        have : (1 : ℝ) < ((d * k : ℕ) : ℝ) := by linarith [Real.sqrt_nonneg (N : ℝ)]
        exact_mod_cast this.le
      have hmsucc : m_idx + 1 = d * k := Nat.sub_add_cancel hdk_pos
      have hm_ge_sqrt : Real.sqrt (N : ℝ) ≤ (m_idx : ℝ) := by
        have : (m_idx : ℝ) + 1 = ((d * k : ℕ) : ℝ) := by exact_mod_cast hmsucc
        linarith
      have hm_ge_xa : x_a ≤ (m_idx : ℝ) := by
        have h2 : K_big ^ 4 ≤ Real.sqrt (N : ℝ) := by
          rw [Real.le_sqrt (by positivity) hNpos.le]
          have : (K_big ^ 4) ^ 2 = K_big ^ 8 := by ring
          linarith
        have h3 : K_big ≤ K_big ^ 4 := le_self_pow₀ (by linarith) (by decide)
        linarith
      have hlog_m_ge : (1 / 2 : ℝ) * Real.log (N : ℝ) ≤ Real.log (m_idx : ℝ) := by
        have h1 := Real.log_le_log (Real.sqrt_pos.mpr hNpos) hm_ge_sqrt
        rw [Real.log_sqrt hNpos.le] at h1
        linarith
      have hdq_le_log : ((d * q : ℕ) : ℝ) ≤ (Real.log (m_idx : ℝ)) ^ (22 : ℝ) := by
        have hdq1 : ((d * q : ℕ) : ℝ) ≤ (d : ℝ) * (4 * Real.log (N : ℝ)) ^ 20 := by
          rw [Nat.cast_mul]
          exact mul_le_mul_of_nonneg_left ((by exact_mod_cast hqQ : (q : ℝ) ≤ (Q : ℝ)).trans hQ_le) hdpos.le
        have h420 : (4 : ℝ) ^ 20 * (2 : ℝ) ^ 22 ≤ Real.log (N : ℝ) := hK_420.trans hlogN_ge
        have h22 : (Real.log (m_idx : ℝ)) ^ (22 : ℝ) = (Real.log (m_idx : ℝ)) ^ 22 := by
          rw [show (22 : ℝ) = ((22 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        rw [h22]
        calc
          ((d * q : ℕ) : ℝ) ≤ (d : ℝ) * ((4 : ℝ) ^ 20 * (Real.log (N : ℝ)) ^ 20) := by
            simpa only [mul_pow] using hdq1
          _ ≤ Real.log (N : ℝ) * ((4 : ℝ) ^ 20 * (Real.log (N : ℝ)) ^ 20) :=
            mul_le_mul_of_nonneg_right hd_le_logN (by positivity)
          _ = ((4 : ℝ) ^ 20 * (2 : ℝ) ^ 22) * ((1 / 2 : ℝ) * Real.log (N : ℝ)) ^ 21 * (1 / 2 : ℝ) := by ring
          _ ≤ Real.log (N : ℝ) * ((1 / 2 : ℝ) * Real.log (N : ℝ)) ^ 21 * (1 / 2 : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ (by norm_num)
            exact mul_le_mul_of_nonneg_right h420 (by positivity)
          _ = ((1 / 2 : ℝ) * Real.log (N : ℝ)) ^ 22 := by ring
          _ ≤ (Real.log (m_idx : ℝ)) ^ 22 := pow_le_pow_left₀ (by linarith) hlog_m_ge 22
      have hce_all : ∀ m ∈ range q,
          |GoldbachMajorArc.classError (d * k) (d * q) (d * m + a)| ≤
            M_a * (d : ℝ) * (N : ℝ) * (Real.log (N : ℝ)) ^ (-60 : ℝ) * (2 : ℝ) ^ 60 +
            (200 * (C_l1 + 1)) * (d : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) := by
        intro m hm
        have hlt_dq : d * m + a < d * q := by
          have hmq := mem_range.mp hm
          have h1 : d * (m + 1) ≤ d * q := Nat.mul_le_mul_left d hmq
          rw [mul_add, mul_one] at h1; omega
        have hsw_m := hall m_idx (d * q) (d * m + a) hm_ge_xa
          (Nat.mul_pos (by omega : 0 < d) (by omega : 0 < q)) hdq_le_log hlt_dq
        rw [hmsucc] at hsw_m
        have hm_le_dN : (m_idx : ℝ) ≤ (d : ℝ) * (N : ℝ) := by
          have : m_idx ≤ d * N := (Nat.sub_le _ _).trans (Nat.mul_le_mul_left d hkN)
          exact_mod_cast this
        have hinv60 : (Real.log (m_idx : ℝ)) ^ (-60 : ℝ) ≤ (Real.log (N : ℝ)) ^ (-60 : ℝ) * (2 : ℝ) ^ 60 := by
          rw [Real.rpow_neg (by linarith), Real.rpow_neg (by linarith),
            show (60 : ℝ) = ((60 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
          have h1 : ((1 / 2 : ℝ) * Real.log (N : ℝ)) ^ 60 ≤ (Real.log (m_idx : ℝ)) ^ 60 :=
            pow_le_pow_left₀ (by linarith) hlog_m_ge 60
          have h2 : (((1 / 2 : ℝ) * Real.log (N : ℝ)) ^ 60)⁻¹ = ((Real.log (N : ℝ)) ^ 60)⁻¹ * (2 : ℝ) ^ 60 := by
            rw [mul_pow, mul_inv, one_div, inv_pow, inv_inv, mul_comm]
          rw [← h2]
          exact inv_anti₀ (by positivity) h1
        have hmain_m : M_a * (m_idx : ℝ) * (Real.log (m_idx : ℝ)) ^ (-60 : ℝ) ≤
            M_a * (d : ℝ) * (N : ℝ) * (Real.log (N : ℝ)) ^ (-60 : ℝ) * (2 : ℝ) ^ 60 := by
          calc
            M_a * (m_idx : ℝ) * (Real.log (m_idx : ℝ)) ^ (-60 : ℝ)
                ≤ M_a * ((d : ℝ) * (N : ℝ)) * ((Real.log (N : ℝ)) ^ (-60 : ℝ) * (2 : ℝ) ^ 60) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hm_le_dN hM_a.le) hinv60 (by positivity) (by positivity)
            _ = M_a * (d : ℝ) * (N : ℝ) * (Real.log (N : ℝ)) ^ (-60 : ℝ) * (2 : ℝ) ^ 60 := by ring
        have hlog_m_le : Real.log (m_idx : ℝ) ≤ 2 * Real.log (N : ℝ) :=
          (Real.log_le_log (by linarith [Real.sqrt_pos.mpr hNpos])
            (hm_le_dN.trans (by exact_mod_cast (by omega : d * N ≤ M + 2)))).trans hlogM_le
        have hlog_dq_le : Real.log ((d * q : ℕ) : ℝ) ≤ 22 * Real.log (m_idx : ℝ) := by
          have h := Real.log_le_log (by positivity) hdq_le_log
          rw [Real.log_rpow (by linarith)] at h
          have hll : Real.log (Real.log (m_idx : ℝ)) ≤ Real.log (m_idx : ℝ) :=
            (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
          linarith
        have hlog2_m : (Nat.log 2 m_idx : ℝ) ≤ 2 * Real.log (m_idx : ℝ) :=
          nat_log2_le_two_log (by
            have : (1 : ℝ) ≤ (m_idx : ℝ) := by linarith [Real.sqrt_pos.mpr hNpos, hm_ge_xa]
            exact_mod_cast this)
        have hrem_m : (Nat.log 2 m_idx : ℝ) * Real.log ((d * q : ℕ) : ℝ) +
            2 * Real.sqrt (m_idx : ℝ) * Real.log (m_idx : ℝ) + 1 ≤
            (200 * (C_l1 + 1)) * (d : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) := by
          have hln_le : Real.log (N : ℝ) ≤ C_l1 * (N : ℝ) ^ (1 / 4 : ℝ) := by simpa using hl1 (N : ℝ) hN1
          have hln2_le : (Real.log (N : ℝ)) ^ 2 ≤ (N : ℝ) ^ (3 / 4 : ℝ) := by
            have hsq1 : (Real.log (N : ℝ)) ^ 2 ≤ (C_l1 * (N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 :=
              pow_le_pow_left₀ (by linarith) hln_le 2
            have hC2 : C_l1 ^ 2 ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
              have h1 : C_l1 ≤ K_big := by linarith
              have h2 : K_big ^ 2 ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
                have := Real.rpow_le_rpow (by positivity) hN_ge_K8 (by norm_num : (0 : ℝ) ≤ 1 / 4)
                rw [← Real.rpow_natCast K_big 8, ← Real.rpow_mul (by linarith)] at this
                norm_num at this; exact this
              exact (pow_le_pow_left₀ hC_l1.le h1 2).trans h2
            have hpow_eq : ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 * (N : ℝ) ^ (1 / 4 : ℝ) = (N : ℝ) ^ (3 / 4 : ℝ) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]; norm_num
            calc
              (Real.log (N : ℝ)) ^ 2 ≤ C_l1 ^ 2 * ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by simpa only [mul_pow] using hsq1
              _ ≤ (N : ℝ) ^ (1 / 4 : ℝ) * ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 :=
                mul_le_mul_of_nonneg_right hC2 (by positivity)
              _ = (N : ℝ) ^ (3 / 4 : ℝ) := by rw [mul_comm, hpow_eq]
          have hterm_log : (Nat.log 2 m_idx : ℝ) * Real.log ((d * q : ℕ) : ℝ) ≤ 176 * (N : ℝ) ^ (3 / 4 : ℝ) := by
            have h1 : (Nat.log 2 m_idx : ℝ) * Real.log ((d * q : ℕ) : ℝ) ≤
                (2 * (2 * Real.log (N : ℝ))) * (22 * (2 * Real.log (N : ℝ))) :=
              mul_le_mul (hlog2_m.trans (by linarith)) (hlog_dq_le.trans (by linarith))
                (Real.log_nonneg (by exact_mod_cast (Nat.mul_pos (by omega : 0 < d) (by omega : 0 < q)))) (by positivity)
            nlinarith only [h1, hln2_le]
          have hterm_sq : 2 * Real.sqrt (m_idx : ℝ) * Real.log (m_idx : ℝ) ≤ 4 * C_l1 * (d : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) := by
            have hsq_m : Real.sqrt (m_idx : ℝ) ≤ (d : ℝ) * Real.sqrt (N : ℝ) := by
              calc
                Real.sqrt (m_idx : ℝ) ≤ Real.sqrt ((d : ℝ) * (N : ℝ)) := Real.sqrt_le_sqrt hm_le_dN
                _ = Real.sqrt (d : ℝ) * Real.sqrt (N : ℝ) := Real.sqrt_mul hdpos.le _
                _ ≤ (d : ℝ) * Real.sqrt (N : ℝ) := by
                  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
                  rw [Real.sqrt_le_iff]; exact ⟨hdpos.le, by nlinarith only [hd2]⟩
            have hprod : Real.sqrt (N : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) = (N : ℝ) ^ (3 / 4 : ℝ) := by
              rw [Real.sqrt_eq_rpow, ← Real.rpow_add hNpos]; norm_num
            calc
              2 * Real.sqrt (m_idx : ℝ) * Real.log (m_idx : ℝ)
                  ≤ 2 * ((d : ℝ) * Real.sqrt (N : ℝ)) * (2 * (C_l1 * (N : ℝ) ^ (1 / 4 : ℝ))) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hsq_m (by norm_num))
                  (hlog_m_le.trans (by linarith)) (Real.log_nonneg (by linarith [hm_ge_xa])) (by positivity)
              _ = 4 * C_l1 * (d : ℝ) * (Real.sqrt (N : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ)) := by ring
              _ = 4 * C_l1 * (d : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) := by rw [hprod]
          have hN34_1 : (1 : ℝ) ≤ (N : ℝ) ^ (3 / 4 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
          have h176 : 176 * (N : ℝ) ^ (3 / 4 : ℝ) ≤ 176 * (d : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) := by
            nlinarith only [hd2, hN34_1]
          have h1le : (1 : ℝ) ≤ (d : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) := by nlinarith only [hd2, hN34_1]
          have hdN34 : 0 ≤ (d : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) := by positivity
          nlinarith only [hterm_log, hterm_sq, h176, h1le, hdN34, hC_l1]
        linarith
      have hsum_all : ∑ m ∈ range q, |GoldbachMajorArc.classError (d * k) (d * q) (d * m + a)| ≤
          (Q : ℝ) * (M_a * (d : ℝ) * (N : ℝ) * (Real.log (N : ℝ)) ^ (-60 : ℝ) * (2 : ℝ) ^ 60 +
            (200 * (C_l1 + 1)) * (d : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ)) := by
        calc
          ∑ m ∈ range q, |GoldbachMajorArc.classError (d * k) (d * q) (d * m + a)|
              ≤ ∑ _m ∈ range q, _ := sum_le_sum hce_all
          _ = (q : ℝ) * _ := by rw [sum_const, card_range, nsmul_eq_mul]
          _ ≤ (Q : ℝ) * _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hqQ) (by positivity)
      calc
        ((d.totient : ℝ) / (d : ℝ)) * _ ≤ 1 * _ :=
          mul_le_mul hphi_div (htri.trans hsum_all) (norm_nonneg _) zero_le_one
        _ ≤ _ := by
          have h1 : 0 ≤ (Q : ℝ) * (d : ℝ) * (N : ℝ) * (Real.log (N : ℝ)) ^ (-60 : ℝ) * (2 : ℝ) ^ 60 := by positivity
          linarith
  have hsum_split : ∑ n ∈ range N,
        ((((d.totient : ℝ) / (d : ℝ) * GoldbachMajorArc.primeWeight (d * n + a) : ℝ) : ℂ) *
          phase ((n : ℝ) * α)) =
      C_main * K_sum + ∑ n ∈ range N, phase ((n : ℝ) * β) * g_err n := by
    rw [← hdiff_abel]; ring
  rw [hsum_split, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos one_pos hNpos)]
  have habel : ∀ m : ℕ, ∑ i ∈ range m, phase ((i : ℝ) * β) * g_err i =
      phase ((m : ℝ) * β) * (∑ j ∈ range m, g_err j) -
      ∑ i ∈ range m, (phase (((i + 1 : ℕ) : ℝ) * β) - phase ((i : ℝ) * β)) *
        (∑ j ∈ range (i + 1), g_err j) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, ih, sum_range_succ (f := fun i => (phase (((i + 1 : ℕ) : ℝ) * β) - phase ((i : ℝ) * β)) *
        (∑ j ∈ range (i + 1), g_err j)), sum_range_succ (f := g_err)]
      ring
  have hph_step : ‖phase β - 1‖ ≤ 2 * Real.pi * |β| := by
    have hexp : phase β = ((Real.cos (2 * Real.pi * β) : ℝ) : ℂ) +
        ((Real.sin (2 * Real.pi * β) : ℝ) : ℂ) * Complex.I := by
      unfold phase GoldbachMajorArc.phase
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hnsq : ‖phase β - 1‖ ^ 2 = (2 * Real.sin (Real.pi * β)) ^ 2 := by
      rw [Complex.sq_norm, hexp]
      have hsub : (((Real.cos (2 * Real.pi * β) : ℝ) : ℂ) +
          ((Real.sin (2 * Real.pi * β) : ℝ) : ℂ) * Complex.I) - 1 =
          ((Real.cos (2 * Real.pi * β) - 1 : ℝ) : ℂ) +
          ((Real.sin (2 * Real.pi * β) : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [hsub, Complex.normSq_add_mul_I]
      have hsc := Real.sin_sq_add_cos_sq (2 * Real.pi * β)
      have hcos2 : Real.cos (2 * Real.pi * β) = 1 - 2 * Real.sin (Real.pi * β) ^ 2 := by
        have h1 : Real.cos (2 * Real.pi * β) = 2 * Real.cos (Real.pi * β) ^ 2 - 1 := by
          rw [show 2 * Real.pi * β = 2 * (Real.pi * β) by ring, Real.cos_two_mul]
        nlinarith only [h1, Real.sin_sq_add_cos_sq (Real.pi * β)]
      nlinarith only [hsc, hcos2]
    have hsin_le : |Real.sin (Real.pi * β)| ≤ Real.pi * |β| := by
      calc
        |Real.sin (Real.pi * β)| ≤ |Real.pi * β| := Real.abs_sin_le_abs
        _ = Real.pi * |β| := by rw [abs_mul, abs_of_pos Real.pi_pos]
    have hsq_le : ‖phase β - 1‖ ^ 2 ≤ (2 * Real.pi * |β|) ^ 2 := by
      rw [hnsq]
      have h1 : (2 * Real.sin (Real.pi * β)) ^ 2 = (2 * |Real.sin (Real.pi * β)|) ^ 2 := by
        rw [mul_pow, mul_pow, sq_abs]
      rw [h1]
      exact pow_le_pow_left₀ (by positivity) (by linarith) 2
    nlinarith only [hsq_le, norm_nonneg (phase β - 1),
      mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi) (abs_nonneg β)]
  have hstep_i : ∀ i : ℕ, ‖phase (((i + 1 : ℕ) : ℝ) * β) - phase ((i : ℝ) * β)‖ ≤
      2 * Real.pi * |β| := by
    intro i
    have hfac : phase (((i + 1 : ℕ) : ℝ) * β) - phase ((i : ℝ) * β) =
        phase ((i : ℝ) * β) * (phase β - 1) := by
      symm
      rw [mul_sub, mul_one, ← phase_add]
      congr 1; push_cast; ring
    rw [hfac, norm_mul, norm_phase, one_mul]
    exact hph_step
  have herr_norm : ‖∑ n ∈ range N, phase ((n : ℝ) * β) * g_err n‖ ≤ 17 * (Q : ℝ) * D_pref := by
    rw [habel N]
    have hD0 : 0 ≤ D_pref := by dsimp [D_pref]; positivity
    have h1 : ‖phase ((N : ℝ) * β) * ∑ j ∈ range N, g_err j‖ ≤ D_pref := by
      rw [norm_mul, norm_phase, one_mul]; exact hpref_bound N le_rfl
    have h2 : ‖∑ i ∈ range N, (phase (((i + 1 : ℕ) : ℝ) * β) - phase ((i : ℝ) * β)) *
          ∑ j ∈ range (i + 1), g_err j‖ ≤
        (N : ℝ) * (2 * Real.pi * |β| * D_pref) := by
      calc
        _ ≤ ∑ i ∈ range N, ‖(phase (((i + 1 : ℕ) : ℝ) * β) - phase ((i : ℝ) * β)) *
              ∑ j ∈ range (i + 1), g_err j‖ := norm_sum_le _ _
        _ ≤ ∑ _i ∈ range N, (2 * Real.pi * |β| * D_pref) := by
          refine sum_le_sum fun i hi => ?_
          rw [norm_mul]
          exact mul_le_mul (hstep_i i) (hpref_bound (i + 1) (mem_range.mp hi))
            (norm_nonneg _) (by positivity)
        _ = (N : ℝ) * (2 * Real.pi * |β| * D_pref) := by simp
    have hNβ : (N : ℝ) * (2 * Real.pi * |β|) ≤ 16 * (Q : ℝ) := by
      have hβN : |β| ≤ (2 * (Q : ℝ)) / (N : ℝ) := by
        refine hβ_le.trans ?_
        exact div_le_div_of_nonneg_left (by positivity) hNpos
          (by nlinarith only [show (1 : ℝ) ≤ (q : ℝ) by exact_mod_cast hq1, hNpos])
      have hpi4 : Real.pi ≤ 4 := Real.pi_lt_four.le
      calc
        (N : ℝ) * (2 * Real.pi * |β|) ≤ (N : ℝ) * (2 * 4 * ((2 * (Q : ℝ)) / (N : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hNpos.le
          exact mul_le_mul (by linarith) hβN (abs_nonneg _) (by positivity)
        _ = 16 * (Q : ℝ) := by field_simp; ring
    have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ_pos
    calc
      ‖phase ((N : ℝ) * β) * ∑ j ∈ range N, g_err j -
          ∑ i ∈ range N, (phase (((i + 1 : ℕ) : ℝ) * β) - phase ((i : ℝ) * β)) *
            ∑ j ∈ range (i + 1), g_err j‖
          ≤ ‖phase ((N : ℝ) * β) * ∑ j ∈ range N, g_err j‖ +
            ‖∑ i ∈ range N, (phase (((i + 1 : ℕ) : ℝ) * β) - phase ((i : ℝ) * β)) *
              ∑ j ∈ range (i + 1), g_err j‖ := norm_sub_le _ _
      _ ≤ D_pref + (N : ℝ) * (2 * Real.pi * |β| * D_pref) := add_le_add h1 h2
      _ = (1 + (N : ℝ) * (2 * Real.pi * |β|)) * D_pref := by ring
      _ ≤ (17 * (Q : ℝ)) * D_pref := mul_le_mul_of_nonneg_right (by linarith) hD0
  have hQ2_le : (Q : ℝ) ^ 2 ≤ (4 : ℝ) ^ 40 * (Real.log (N : ℝ)) ^ 40 := by
    calc
      (Q : ℝ) ^ 2 ≤ ((4 * Real.log (N : ℝ)) ^ 20) ^ 2 := pow_le_pow_left₀ (by positivity) hQ_le 2
      _ = (4 : ℝ) ^ 40 * (Real.log (N : ℝ)) ^ 40 := by ring
  have herr_le : (1 / (N : ℝ)) * ‖∑ n ∈ range N, phase ((n : ℝ) * β) * g_err n‖ ≤ 1 / (z : ℝ) := by
    have hpart1 : (1 / (N : ℝ)) * (17 * (Q : ℝ) * ((Q : ℝ) * (M_a + 1) * (d : ℝ) * (N : ℝ) *
          (Real.log (N : ℝ)) ^ (-60 : ℝ) * (2 : ℝ) ^ 60)) ≤ 1 / (2 * (z : ℝ)) := by
      have hrw : (1 / (N : ℝ)) * (17 * (Q : ℝ) * ((Q : ℝ) * (M_a + 1) * (d : ℝ) * (N : ℝ) *
            (Real.log (N : ℝ)) ^ (-60 : ℝ) * (2 : ℝ) ^ 60)) =
          17 * (M_a + 1) * (d : ℝ) * (2 : ℝ) ^ 60 * ((Q : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ (-60 : ℝ)) := by
        field_simp
      rw [hrw]
      have hlog_cancel : (Real.log (N : ℝ)) ^ 40 * (Real.log (N : ℝ)) ^ (-60 : ℝ) =
          1 / (Real.log (N : ℝ)) ^ 20 := by
        rw [Real.rpow_neg (by linarith), show (60 : ℝ) = ((60 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast, show (60 : ℕ) = 40 + 20 by norm_num, pow_add]
        have hne : (Real.log (N : ℝ)) ^ 40 ≠ 0 := pow_ne_zero 40 (by linarith)
        field_simp
      have hprod_le : (Q : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ (-60 : ℝ) ≤
          (4 : ℝ) ^ 40 / (Real.log (N : ℝ)) ^ 20 := by
        calc
          (Q : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ (-60 : ℝ)
              ≤ ((4 : ℝ) ^ 40 * (Real.log (N : ℝ)) ^ 40) * (Real.log (N : ℝ)) ^ (-60 : ℝ) :=
            mul_le_mul_of_nonneg_right hQ2_le (by positivity)
          _ = (4 : ℝ) ^ 40 * ((Real.log (N : ℝ)) ^ 40 * (Real.log (N : ℝ)) ^ (-60 : ℝ)) := by ring
          _ = (4 : ℝ) ^ 40 / (Real.log (N : ℝ)) ^ 20 := by rw [hlog_cancel]; ring
      have hA : 34 * (M_a + 1) * (d : ℝ) * (z : ℝ) ≤ Real.log (N : ℝ) := hK_ma.trans hlogN_ge
      have hB : (2 : ℝ) ^ 60 ≤ Real.log (N : ℝ) := hK_260.trans hlogN_ge
      have hC : (4 : ℝ) ^ 40 ≤ Real.log (N : ℝ) := hK_440.trans hlogN_ge
      have hlog3 : (Real.log (N : ℝ)) ^ 3 ≤ (Real.log (N : ℝ)) ^ 20 :=
        pow_le_pow_right₀ (by linarith) (by decide)
      have hnum_le : 17 * (M_a + 1) * (d : ℝ) * (2 : ℝ) ^ 60 * (4 : ℝ) ^ 40 * (2 * (z : ℝ)) ≤
          (Real.log (N : ℝ)) ^ 20 := by
        calc
          17 * (M_a + 1) * (d : ℝ) * (2 : ℝ) ^ 60 * (4 : ℝ) ^ 40 * (2 * (z : ℝ))
              = (34 * (M_a + 1) * (d : ℝ) * (z : ℝ)) * (2 : ℝ) ^ 60 * (4 : ℝ) ^ 40 := by ring
          _ ≤ Real.log (N : ℝ) * Real.log (N : ℝ) * Real.log (N : ℝ) :=
            mul_le_mul (mul_le_mul hA hB (by positivity) (by linarith)) hC (by positivity) (by positivity)
          _ = (Real.log (N : ℝ)) ^ 3 := by ring
          _ ≤ (Real.log (N : ℝ)) ^ 20 := hlog3
      calc
        17 * (M_a + 1) * (d : ℝ) * (2 : ℝ) ^ 60 * ((Q : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ (-60 : ℝ))
            ≤ 17 * (M_a + 1) * (d : ℝ) * (2 : ℝ) ^ 60 * ((4 : ℝ) ^ 40 / (Real.log (N : ℝ)) ^ 20) :=
          mul_le_mul_of_nonneg_left hprod_le (by positivity)
        _ = (17 * (M_a + 1) * (d : ℝ) * (2 : ℝ) ^ 60 * (4 : ℝ) ^ 40) / (Real.log (N : ℝ)) ^ 20 := by ring
        _ ≤ 1 / (2 * (z : ℝ)) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          linarith
    have hpart2 : (1 / (N : ℝ)) * (17 * (Q : ℝ) * ((Q : ℝ) * (200 * (C_l1 + 1)) * (d : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ))) ≤
        1 / (2 * (z : ℝ)) := by
      have hNsplit : (N : ℝ) = (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) := by
        rw [← Real.rpow_add hNpos]; norm_num
      have hN14 : (N : ℝ) ^ (1 / 4 : ℝ) = (N : ℝ) ^ (1 / 8 : ℝ) * (N : ℝ) ^ (1 / 8 : ℝ) := by
        rw [← Real.rpow_add hNpos]; norm_num
      have hQ2_rpow : (Q : ℝ) ^ 2 ≤ (4 : ℝ) ^ 40 * C_l3 * (N : ℝ) ^ (1 / 8 : ℝ) := by
        have h40_41 : (Real.log (N : ℝ)) ^ 40 ≤ (Real.log (N : ℝ)) ^ 41 :=
          pow_le_pow_right₀ (by linarith) (by decide)
        calc
          (Q : ℝ) ^ 2 ≤ (4 : ℝ) ^ 40 * (Real.log (N : ℝ)) ^ 40 := hQ2_le
          _ ≤ (4 : ℝ) ^ 40 * (Real.log (N : ℝ)) ^ 41 := mul_le_mul_of_nonneg_left h40_41 (by positivity)
          _ ≤ (4 : ℝ) ^ 40 * (C_l3 * (N : ℝ) ^ (1 / 8 : ℝ)) := mul_le_mul_of_nonneg_left (hl3 (N : ℝ) hN1) (by positivity)
          _ = (4 : ℝ) ^ 40 * C_l3 * (N : ℝ) ^ (1 / 8 : ℝ) := by ring
      have hK2_N18 : K_big ^ 2 ≤ (N : ℝ) ^ (1 / 8 : ℝ) := by
        have := Real.rpow_le_rpow (by positivity) hN_ge_K16 (by norm_num : (0 : ℝ) ≤ 1 / 8)
        rw [← Real.rpow_natCast K_big 16, ← Real.rpow_mul (by linarith)] at this
        norm_num at this; exact this
      have hnum2 : 3400 * (C_l1 + 1) * (d : ℝ) * ((4 : ℝ) ^ 40 * C_l3) * (2 * (z : ℝ)) ≤
          (N : ℝ) ^ (1 / 8 : ℝ) := by
        calc
          3400 * (C_l1 + 1) * (d : ℝ) * ((4 : ℝ) ^ 40 * C_l3) * (2 * (z : ℝ))
              = (6800 * (C_l1 + 1)) * (C_l3 * (d : ℝ) * (z : ℝ) * (4 : ℝ) ^ 40) := by ring
          _ ≤ K_big * K_big := mul_le_mul hK_cl1 hK_cl3 (by positivity) (by linarith)
          _ = K_big ^ 2 := (sq K_big).symm
          _ ≤ (N : ℝ) ^ (1 / 8 : ℝ) := hK2_N18
      calc
        (1 / (N : ℝ)) * (17 * (Q : ℝ) * ((Q : ℝ) * (200 * (C_l1 + 1)) * (d : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ)))
            = 3400 * (C_l1 + 1) * (d : ℝ) * (Q : ℝ) ^ 2 / (N : ℝ) ^ (1 / 4 : ℝ) := by
          conv_lhs => arg 1; arg 2; rw [hNsplit]
          field_simp; ring
        _ ≤ 3400 * (C_l1 + 1) * (d : ℝ) * ((4 : ℝ) ^ 40 * C_l3 * (N : ℝ) ^ (1 / 8 : ℝ)) / (N : ℝ) ^ (1 / 4 : ℝ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hQ2_rpow (by positivity)
        _ = (3400 * (C_l1 + 1) * (d : ℝ) * ((4 : ℝ) ^ 40 * C_l3)) / (N : ℝ) ^ (1 / 8 : ℝ) := by
          conv_lhs => arg 2; rw [hN14]
          field_simp
        _ ≤ 1 / (2 * (z : ℝ)) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          linarith
    calc
      (1 / (N : ℝ)) * ‖∑ n ∈ range N, phase ((n : ℝ) * β) * g_err n‖
          ≤ (1 / (N : ℝ)) * (17 * (Q : ℝ) * D_pref) := mul_le_mul_of_nonneg_left herr_norm (by positivity)
      _ = (1 / (N : ℝ)) * (17 * (Q : ℝ) * ((Q : ℝ) * (M_a + 1) * (d : ℝ) * (N : ℝ) *
            (Real.log (N : ℝ)) ^ (-60 : ℝ) * (2 : ℝ) ^ 60)) +
          (1 / (N : ℝ)) * (17 * (Q : ℝ) * ((Q : ℝ) * (200 * (C_l1 + 1)) * (d : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ))) := by
        dsimp [D_pref]; ring
      _ ≤ 1 / (2 * (z : ℝ)) + 1 / (2 * (z : ℝ)) := add_le_add hpart1 hpart2
      _ = 1 / (z : ℝ) := by ring
  have hmain_le : (1 / (N : ℝ)) * ‖C_main * K_sum‖ ≤ 1 / (z : ℝ) := by
    by_cases hq_eq1 : q = 1
    · have hK0 : K_sum = 0 := by
        have hK_eq : K_sum = ∑ n ∈ range N, phase (-(n : ℝ) * ((r.val : ℤ) : ℝ) / (N : ℝ)) := by
          dsimp [K_sum]
          refine sum_congr rfl fun n _ => ?_
          apply phase_eq_of_int_sub (k := (n : ℤ) - (n * b : ℤ))
          dsimp [β, α]
          rw [hq_eq1, Nat.cast_one, div_one, Nat.cast_sub hr_lt.le]
          push_cast; field_simp; ring
        have horth := phase_orthog (by omega : 1 ≤ N) (r.val : ℤ)
        have hndvd : ¬ ((N : ℤ) ∣ (r.val : ℤ)) := by
          rw [Int.natCast_dvd_natCast]
          intro hdvd
          have := Nat.le_of_dvd hr_pos hdvd
          omega
        rw [ite_eq_right hndvd] at horth
        rw [hK_eq]
        have hneC : (((1 / (N : ℝ) : ℝ) : ℂ)) ≠ 0 := by
          exact_mod_cast (div_pos one_pos hNpos).ne'
        exact (mul_eq_zero.mp horth).resolve_left hneC
      rw [hK0, mul_zero, norm_zero, mul_zero]
      exact hinvz_pos.le
    · have hq2 : 2 ≤ q := by omega
      by_cases hqcop : q.Coprime d
      · have hC_le : ‖C_main‖ ≤ 1 / (q.totient : ℝ) :=
          norm_major_coeff_le_of_coprime hd hq1 hcop hbcop hqcop
        have hK_le : ‖K_sum‖ ≤ (N : ℝ) := by
          dsimp [K_sum]
          calc
            ‖∑ n ∈ range N, phase ((n : ℝ) * β)‖ ≤ ∑ n ∈ range N, ‖phase ((n : ℝ) * β)‖ :=
              norm_sum_le _ _
            _ = ∑ _n ∈ range N, (1 : ℝ) := sum_congr rfl fun _ _ => norm_phase _
            _ = (N : ℝ) := by simp
        let p := q.minFac
        have hpp : p.Prime := Nat.minFac_prime (by omega)
        have hpq : p ∣ q := Nat.minFac_dvd q
        have hnot_pd : ¬ (p ∣ d) := fun hpd =>
          hpp.not_dvd_one (hqcop.gcd_eq_one ▸ Nat.dvd_gcd hpq hpd)
        have hz_lt_p : z < p := by
          by_contra hle; push Not at hle
          exact hnot_pd (hprimes p hpp hle)
        have hz_le_phiq : z ≤ q.totient := by
          have h1 : z ≤ p.totient := by rw [Nat.totient_prime hpp]; omega
          have h2 : p.totient ≤ q.totient :=
            Nat.le_of_dvd (Nat.totient_pos.mpr (by omega)) (Nat.totient_dvd_of_dvd hpq)
          exact h1.trans h2
        calc
          (1 / (N : ℝ)) * ‖C_main * K_sum‖
              = (1 / (N : ℝ)) * (‖C_main‖ * ‖K_sum‖) := by rw [norm_mul]
          _ ≤ (1 / (N : ℝ)) * ((1 / (q.totient : ℝ)) * (N : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul hC_le hK_le (norm_nonneg _) (by positivity)
          _ = 1 / (q.totient : ℝ) := by field_simp
          _ ≤ 1 / (z : ℝ) :=
            one_div_le_one_div_of_le (by exact_mod_cast (by omega : 0 < z))
              (by exact_mod_cast hz_le_phiq)
      · have hC0 : C_main = 0 := by
          dsimp [C_main]
          rw [major_coeff_eq_zero_of_not_coprime hd hq2 hbcop hqcop, mul_zero]
        rw [hC0, zero_mul, norm_zero, mul_zero]
        exact hinvz_pos.le
  calc
    (1 / (N : ℝ)) * ‖C_main * K_sum + ∑ n ∈ range N, phase ((n : ℝ) * β) * g_err n‖
        ≤ (1 / (N : ℝ)) * (‖C_main * K_sum‖ + ‖∑ n ∈ range N, phase ((n : ℝ) * β) * g_err n‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = (1 / (N : ℝ)) * ‖C_main * K_sum‖ + (1 / (N : ℝ)) * ‖∑ n ∈ range N, phase ((n : ℝ) * β) * g_err n‖ := by ring
    _ ≤ 1 / (z : ℝ) + 1 / (z : ℝ) := add_le_add hmain_le herr_le
    _ = 2 / (z : ℝ) := by ring
    _ ≤ ε := hε

set_option maxHeartbeats 1200000 in
lemma nu_fourier_minor {d a : ℕ} (hd : 1 ≤ d) (ha : a < d) (hcop : a.Coprime d)
    {z : ℕ} (hz : 2 ≤ z) (hprimes : ∀ p : ℕ, p.Prime → p ≤ z → p ∣ d)
    {ε : ℝ} (hε : 2 / (z : ℝ) ≤ ε) :
    ∃ N₀ : ℕ, ∀ (N : ℕ) [NeZero N], N₀ ≤ N → ∀ (r : ZMod N), r ≠ 0 →
      (¬ ∃ q b : ℕ, 1 ≤ q ∧ q ≤ (Nat.log 2 (d * N - 1 + 2)) ^ 20 ∧ b ≤ q ∧ b.Coprime q ∧
        |((N - r.val : ℕ) : ℝ) / (N : ℝ) - (b : ℝ) / (q : ℝ)| ≤
          (2 * (((Nat.log 2 (d * N - 1 + 2)) ^ 20 : ℕ) : ℝ)) / ((q : ℝ) * (N : ℝ))) →
      ‖PolynomialTransfer.F (fun x => nu d a N x - 1) r‖ ≤ ε := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd2_nat : 2 ≤ d := Nat.le_of_dvd (by omega) (hprimes 2 Nat.prime_two hz)
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2_nat
  obtain ⟨N_min, hminor⟩ := GoldbachEstermann.uniformMinorSum 2 (by norm_num)
  obtain ⟨C_l2, hC_l2, hl2⟩ := log_pow_le_rpow 21 (1 / 4 : ℝ) (by norm_num)
  obtain ⟨K_big, hK_100, hK_dz, hK_cl2⟩ :
      ∃ K_big : ℝ, 100 ≤ K_big ∧ 100 * (d : ℝ) * (z : ℝ) ≤ K_big ∧
        2 * (4 : ℝ) ^ 20 * C_l2 ≤ K_big := by
    refine ⟨max (max 100 (100 * (d : ℝ) * (z : ℝ))) (2 * (4 : ℝ) ^ 20 * C_l2), ?_, ?_, ?_⟩
    · exact le_max_of_le_left (le_max_left _ _)
    · exact le_max_of_le_left (le_max_right _ _)
    · exact le_max_right _ _
  obtain ⟨N_log, hN_log2, hN_log⟩ := exists_nat_log_ge K_big
  refine ⟨max N_log (max (⌈K_big ^ 8⌉₊ + 100) (max (d ^ 4 + 100) (N_min + 100))), ?_⟩
  intro N inst hN r hr0 hmaj
  have hN2 : 2 ≤ N := (hN_log2.trans (le_max_left _ _)).trans hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hlogN_ge : K_big ≤ Real.log (N : ℝ) := hN_log N ((le_max_left _ _).trans hN)
  have hlogN_pos : 100 ≤ Real.log (N : ℝ) := hK_100.trans hlogN_ge
  have hN_ge_K8 : K_big ^ 8 ≤ (N : ℝ) := by
    have h1 : K_big ^ 8 ≤ (⌈K_big ^ 8⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ⌈K_big ^ 8⌉₊ ≤ N :=
      (Nat.le_add_right _ 100).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
    have h3 : (⌈K_big ^ 8⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
    linarith
  have hd_le_N : (d : ℝ) ^ 4 ≤ (N : ℝ) := by
    have h1 : d ^ 4 ≤ N :=
      (Nat.le_add_right _ 100).trans ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN)))
    exact_mod_cast h1
  have hN_min : N_min ≤ N :=
    (Nat.le_add_right _ 100).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN)))
  let M : ℕ := d * N - 1
  have hM1 : M + 1 = d * N := Nat.sub_add_cancel (Nat.mul_pos (by omega) (by omega))
  have hM_ge_N : N ≤ M := by
    dsimp [M]; have : 2 * N ≤ d * N := Nat.mul_le_mul_right N hd2_nat; omega
  have hMr_ge_N : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge_N
  have hMpos : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le hNpos hMr_ge_N
  have hMr_le_dN : (M : ℝ) ≤ (d : ℝ) * (N : ℝ) := by exact_mod_cast (Nat.sub_le (d * N) 1)
  have hlogM_ge : Real.log (N : ℝ) ≤ Real.log (M : ℝ) := Real.log_le_log hNpos hMr_ge_N
  have hlogM_le : Real.log ((M + 2 : ℕ) : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    have hle : ((M + 2 : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
      have h1 : M + 2 ≤ d * N + 1 := by omega
      have h1r : ((M + 2 : ℕ) : ℝ) ≤ (d : ℝ) * (N : ℝ) + 1 := by exact_mod_cast h1
      have hdn : (d : ℝ) ≤ (N : ℝ) / 2 := by
        have h2d : 2 * (d : ℝ) ≤ (d : ℝ) ^ 4 := by
          have h2 : (4 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith only [hd2]
          have h3 : 4 * (d : ℝ) ≤ (d : ℝ) ^ 3 := by nlinarith only [hd2, h2]
          nlinarith only [hd2, h3]
        linarith
      have hN4 : (4 : ℝ) ≤ (N : ℝ) := by
        have : (100 : ℝ) ≤ K_big ^ 8 := (le_self_pow₀ (by linarith : (1 : ℝ) ≤ K_big) (by decide)).trans' hK_100
        linarith
      nlinarith only [h1r, hdn, hN4]
    have hlog := Real.log_le_log (by positivity) hle
    rw [Real.log_pow] at hlog
    simpa using hlog
  rw [PolynomialTransfer.Fsub, PolynomialTransfer.Fone, ite_eq_right hr0, sub_zero]
  let α : ℝ := ((N - r.val : ℕ) : ℝ) / (N : ℝ)
  have hr_pos : 0 < r.val := Nat.pos_of_ne_zero fun h => hr0 ((ZMod.val_eq_zero r).mp h)
  have hr_lt : r.val < N := r.val_lt
  have hα_pos : 0 < α := div_pos (by exact_mod_cast (by omega : 0 < N - r.val)) hNpos
  have hα_lt1 : α < 1 := (div_lt_one hNpos).mpr (by exact_mod_cast (by omega : N - r.val < N))
  have hF_eq : PolynomialTransfer.F (nu d a N) r =
      ((1 / (N : ℝ) : ℝ) : ℂ) *
        ∑ n ∈ range N, (((d.totient : ℝ) / (d : ℝ) * GoldbachMajorArc.primeWeight (d * n + a) : ℝ) : ℂ) *
          phase ((n : ℝ) * α) := by
    unfold PolynomialTransfer.F PolynomialTransfer.C nu
    rw [div_eq_mul_inv, mul_comm _ ((N : ℂ)⁻¹), ← one_div]
    push_cast; congr 1
    refine Finset.sum_bij (fun x _ => x.val) (fun x _ => mem_range.mpr x.val_lt) ?_ ?_ ?_
    · intro x₁ _ x₂ _ heq; exact ZMod.val_injective N heq
    · intro n hn; exact ⟨(n : ZMod N), mem_univ _, ZMod.val_natCast_of_lt (mem_range.mp hn)⟩
    · intro x _
      rw [ch_eq_phase]
      congr 1
      apply phase_eq_of_int_sub (k := -(x.val : ℤ))
      dsimp [α]
      rw [Nat.cast_sub hr_lt.le]
      push_cast; field_simp; ring
  rw [hF_eq]
  let Q : ℕ := (Nat.log 2 (M + 2)) ^ 20
  have hQ_le : (Q : ℝ) ≤ (4 * Real.log (N : ℝ)) ^ 20 := by
    have h1 : (Nat.log 2 (M + 2) : ℝ) ≤ 4 * Real.log (N : ℝ) := by
      have := nat_log2_le_two_log (by omega : 1 ≤ M + 2)
      linarith
    exact_mod_cast (show ((Nat.log 2 (M + 2) : ℝ)) ^ 20 ≤ (4 * Real.log (N : ℝ)) ^ 20 from
      pow_le_pow_left₀ (by positivity) h1 20)
  have hminor_j : ∀ j ∈ range d,
      ‖∑ k ∈ range (M + 1), (GoldbachMajorArc.primeWeight k : ℂ) *
          phase ((k : ℝ) * ((α + (j : ℝ)) / (d : ℝ)))‖ ≤
        (M : ℝ) * (Real.log (M : ℝ)) ^ (-2 : ℝ) := by
    intro j hj
    have hjlt : j < d := mem_range.mp hj
    let tj : ℝ := (α + (j : ℝ)) / (d : ℝ)
    have htj_Icc : tj ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (by positivity) hdpos.le
      · rw [div_le_one hdpos]
        have : (j : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast (by omega : j + 1 ≤ d)
        linarith
    have htj_minor : tj ∉ {t : ℝ | ∃ q' a' : ℕ, 1 ≤ q' ∧ q' ≤ (Nat.log 2 (M + 2)) ^ (2 * ⌈(2 : ℝ)⌉₊ + 16) ∧
        a' ≤ q' ∧ Nat.Coprime a' q' ∧
        |t - (a' : ℝ) / q'| ≤ (((Nat.log 2 (M + 2)) ^ (2 * ⌈(2 : ℝ)⌉₊ + 16) : ℕ) : ℝ) / ((q' : ℝ) * (M : ℝ))} := by
      intro hmem
      have hexp20 : 2 * ⌈(2 : ℝ)⌉₊ + 16 = 20 := by
        have : ⌈(2 : ℝ)⌉₊ = 2 := by norm_num
        omega
      simp only [Set.mem_ofPred_eq, hexp20] at hmem
      obtain ⟨q', a', hq'1, hq'Q, ha'q', ha'cop, happrox⟩ := hmem
      change q' ≤ Q at hq'Q
      change |tj - (a' : ℝ) / (q' : ℝ)| ≤ (Q : ℝ) / ((q' : ℝ) * (M : ℝ)) at happrox
      apply hmaj
      have hd_approx : |α - ((d * a' : ℤ) - (j : ℤ) * (q' : ℤ) : ℝ) / (q' : ℝ)| ≤
          ((d : ℝ) * (Q : ℝ)) / ((q' : ℝ) * (M : ℝ)) := by
        have hmul := mul_le_mul_of_nonneg_left happrox hdpos.le
        conv_lhs at hmul => rw [← abs_of_pos hdpos, ← abs_mul]
        have hl : (d : ℝ) * (tj - (a' : ℝ) / (q' : ℝ)) =
            α - ((d * a' : ℤ) - (j : ℤ) * (q' : ℤ) : ℝ) / (q' : ℝ) := by
          dsimp [tj]
          have hq'ne : (q' : ℝ) ≠ 0 := by exact_mod_cast (by omega : q' ≠ 0)
          push_cast; field_simp; ring
        rw [hl] at hmul
        have hr : (d : ℝ) * ((Q : ℝ) / ((q' : ℝ) * (M : ℝ))) = ((d : ℝ) * (Q : ℝ)) / ((q' : ℝ) * (M : ℝ)) := by ring
        rwa [hr] at hmul
      let g := Nat.gcd d q'
      have hgpos : 0 < g := Nat.gcd_pos_of_pos_right d (by omega)
      let dg := d / g
      let q1 := q' / g
      have hq1_pos : 1 ≤ q1 :=
        (Nat.le_div_iff_mul_le hgpos).mpr (by simpa using Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right d q'))
      have hq1_le : q1 ≤ Q := (Nat.div_le_self q' g).trans hq'Q
      let numZ : ℤ := (dg : ℤ) * (a' : ℤ) - (j : ℤ) * (q1 : ℤ)
      have hfrac_eq : ((d * a' : ℤ) - (j : ℤ) * (q' : ℤ) : ℝ) / (q' : ℝ) = (numZ : ℝ) / (q1 : ℝ) := by
        have hd_eq : (d : ℝ) = (g : ℝ) * (dg : ℝ) := by
          dsimp [dg]; exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left d q')).symm
        have hq_eq : (q' : ℝ) = (g : ℝ) * (q1 : ℝ) := by
          dsimp [q1]; exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_right d q')).symm
        have hgne : (g : ℝ) ≠ 0 := by exact_mod_cast hgpos.ne'
        have hq1ne : (q1 : ℝ) ≠ 0 := by exact_mod_cast (by omega : q1 ≠ 0)
        dsimp [numZ]; push_cast; rw [hd_eq, hq_eq]; field_simp
      rw [hfrac_eq] at hd_approx
      have hbound_q1 : ((d : ℝ) * (Q : ℝ)) / ((q' : ℝ) * (M : ℝ)) ≤ (2 * (Q : ℝ)) / ((q1 : ℝ) * (N : ℝ)) := by
        have hq1_le_q' : (q1 : ℝ) ≤ (q' : ℝ) := by exact_mod_cast Nat.div_le_self q' g
        have hM_half : (d : ℝ) * (N : ℝ) / 2 ≤ (M : ℝ) := by
          have : (M : ℝ) + 1 = (d : ℝ) * (N : ℝ) := by exact_mod_cast hM1
          nlinarith only [this, hd2, hN1]
        rw [div_le_div_iff₀ (mul_pos (by exact_mod_cast hq'1) hMpos) (by positivity)]
        rw [show (d : ℝ) * (Q : ℝ) * ((q1 : ℝ) * (N : ℝ)) =
            (2 * (Q : ℝ) * (q1 : ℝ)) * ((d : ℝ) * (N : ℝ) / 2) by ring,
          show 2 * (Q : ℝ) * ((q' : ℝ) * (M : ℝ)) =
            (2 * (Q : ℝ) * (q' : ℝ)) * (M : ℝ) by ring]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hq1_le_q' (by positivity)) hM_half
          (by positivity) (by positivity)
      have happrox_q1 : |α - (numZ : ℝ) / (q1 : ℝ)| ≤ (2 * (Q : ℝ)) / ((q1 : ℝ) * (N : ℝ)) :=
        hd_approx.trans hbound_q1
      have h2QN : (2 * (Q : ℝ)) / (N : ℝ) < 1 := by
        rw [div_lt_one hNpos]
        have h1 : (Q : ℝ) ≤ (4 : ℝ) ^ 20 * (C_l2 * (N : ℝ) ^ (1 / 4 : ℝ)) := by
          have h21 : (Real.log (N : ℝ)) ^ 20 ≤ (Real.log (N : ℝ)) ^ 21 :=
            pow_le_pow_right₀ (by linarith) (by decide)
          calc
            (Q : ℝ) ≤ (4 * Real.log (N : ℝ)) ^ 20 := hQ_le
            _ = (4 : ℝ) ^ 20 * (Real.log (N : ℝ)) ^ 20 := mul_pow _ _ _
            _ ≤ (4 : ℝ) ^ 20 * (Real.log (N : ℝ)) ^ 21 := mul_le_mul_of_nonneg_left h21 (by positivity)
            _ ≤ (4 : ℝ) ^ 20 * (C_l2 * (N : ℝ) ^ (1 / 4 : ℝ)) := mul_le_mul_of_nonneg_left (hl2 (N : ℝ) hN1) (by positivity)
        have h2 : 2 * (4 : ℝ) ^ 20 * C_l2 < (N : ℝ) ^ (3 / 4 : ℝ) := by
          have hN34 : K_big ^ 6 ≤ (N : ℝ) ^ (3 / 4 : ℝ) := by
            have := Real.rpow_le_rpow (by positivity) hN_ge_K8 (by norm_num : (0 : ℝ) ≤ 3 / 4)
            rw [← Real.rpow_natCast K_big 8, ← Real.rpow_mul (by linarith)] at this
            norm_num at this; exact this
          have : K_big < K_big ^ 6 := by
            have h26 : K_big ^ 2 ≤ K_big ^ 6 := pow_le_pow_right₀ (by linarith) (by decide)
            nlinarith only [h26, hK_100]
          linarith
        have hNsplit : (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) = (N : ℝ) := by
          rw [← Real.rpow_add hNpos]; norm_num
        calc
          2 * (Q : ℝ) ≤ 2 * ((4 : ℝ) ^ 20 * (C_l2 * (N : ℝ) ^ (1 / 4 : ℝ))) := by linarith
          _ = (2 * (4 : ℝ) ^ 20 * C_l2) * (N : ℝ) ^ (1 / 4 : ℝ) := by ring
          _ < (N : ℝ) ^ (3 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) :=
            mul_lt_mul_of_pos_right h2 (by positivity)
          _ = (N : ℝ) := by rw [mul_comm, hNsplit]
      have hnum_ge0 : 0 ≤ numZ := by
        by_contra hlt0
        push Not at hlt0
        have hle1 : (numZ : ℝ) ≤ -1 := by exact_mod_cast (by omega : numZ ≤ -1)
        have h1 : 1 / (q1 : ℝ) < α - (numZ : ℝ) / (q1 : ℝ) := by
          have hdiv : (numZ : ℝ) / (q1 : ℝ) ≤ -(1 / (q1 : ℝ)) := by
            rw [← neg_div]; exact div_le_div_of_nonneg_right hle1 (by positivity)
          linarith
        have h2 : (2 * (Q : ℝ)) / ((q1 : ℝ) * (N : ℝ)) < 1 / (q1 : ℝ) := by
          rw [show (2 * (Q : ℝ)) / ((q1 : ℝ) * (N : ℝ)) = ((2 * (Q : ℝ)) / (N : ℝ)) * (1 / (q1 : ℝ)) by ring]
          have hq1inv : 0 < 1 / (q1 : ℝ) := div_pos one_pos (by exact_mod_cast hq1_pos)
          nlinarith only [h2QN, hq1inv]
        have := (abs_le.mp happrox_q1).2
        linarith
      have hnum_le_q1 : numZ ≤ (q1 : ℤ) := by
        by_contra hgt
        push Not at hgt
        have hge1 : (q1 : ℝ) + 1 ≤ (numZ : ℝ) := by exact_mod_cast (by omega : (q1 : ℤ) + 1 ≤ numZ)
        have h1 : 1 / (q1 : ℝ) < (numZ : ℝ) / (q1 : ℝ) - α := by
          have hq1pos : (0 : ℝ) < (q1 : ℝ) := by exact_mod_cast hq1_pos
          have : 1 + 1 / (q1 : ℝ) ≤ (numZ : ℝ) / (q1 : ℝ) := by
            rw [le_div_iff₀ hq1pos]; field_simp; linarith
          linarith
        have h2 : (2 * (Q : ℝ)) / ((q1 : ℝ) * (N : ℝ)) < 1 / (q1 : ℝ) := by
          rw [show (2 * (Q : ℝ)) / ((q1 : ℝ) * (N : ℝ)) = ((2 * (Q : ℝ)) / (N : ℝ)) * (1 / (q1 : ℝ)) by ring]
          have hq1inv : 0 < 1 / (q1 : ℝ) := div_pos one_pos (by exact_mod_cast hq1_pos)
          nlinarith only [h2QN, hq1inv]
        have := (abs_le.mp happrox_q1).1
        linarith
      let kNat : ℕ := numZ.toNat
      have hk_eq : (kNat : ℤ) = numZ := Int.toNat_of_nonneg hnum_ge0
      let g2 := Nat.gcd kNat q1
      have hg2_pos : 0 < g2 := Nat.gcd_pos_of_pos_right kNat (by omega)
      let q0 := q1 / g2
      let b0 := kNat / g2
      have hq0_pos : 1 ≤ q0 :=
        (Nat.le_div_iff_mul_le hg2_pos).mpr (by simpa using Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right kNat q1))
      have hq0_le : q0 ≤ Q := (Nat.div_le_self q1 g2).trans hq1_le
      have hb0_le : b0 ≤ q0 := Nat.div_le_div_right (by omega)
      have hb0_cop : b0.Coprime q0 := Nat.coprime_div_gcd_div_gcd hg2_pos
      have hfrac2 : (numZ : ℝ) / (q1 : ℝ) = (b0 : ℝ) / (q0 : ℝ) := by
        have hk_r : (numZ : ℝ) = (g2 : ℝ) * (b0 : ℝ) := by
          rw [← hk_eq]; exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left kNat q1)).symm
        have hq_r : (q1 : ℝ) = (g2 : ℝ) * (q0 : ℝ) := by
          exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_right kNat q1)).symm
        have hg2ne : (g2 : ℝ) ≠ 0 := by exact_mod_cast hg2_pos.ne'
        have hq0ne : (q0 : ℝ) ≠ 0 := by exact_mod_cast (by omega : q0 ≠ 0)
        rw [hk_r, hq_r]; field_simp
      have happrox0 : |α - (b0 : ℝ) / (q0 : ℝ)| ≤ (2 * (Q : ℝ)) / ((q0 : ℝ) * (N : ℝ)) := by
        rw [← hfrac2]
        refine happrox_q1.trans ?_
        exact div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.div_le_self q1 g2) hNpos.le)
      exact ⟨q0, b0, hq0_pos, hq0_le, hb0_le, hb0_cop, happrox0⟩
    exact (hminor M (hN_min.trans hM_ge_N) tj htj_Icc htj_minor).2
  have hsum_ap : ∑ n ∈ range N, (GoldbachMajorArc.primeWeight (d * n + a) : ℂ) * phase ((n : ℝ) * α) =
      phase (-(a : ℝ) * α / (d : ℝ)) * (((1 / (d : ℝ) : ℝ) : ℂ) *
        ∑ j ∈ range d, phase (-(j : ℝ) * (a : ℝ) / (d : ℝ)) *
          ∑ k ∈ range (M + 1), (GoldbachMajorArc.primeWeight k : ℂ) *
            phase ((k : ℝ) * ((α + (j : ℝ)) / (d : ℝ)))) := by
    have h1 : ∑ n ∈ range N, (GoldbachMajorArc.primeWeight (d * n + a) : ℂ) * phase ((n : ℝ) * α) =
        phase (-(a : ℝ) * α / (d : ℝ)) *
          ∑ k ∈ (range (M + 1)).filter (fun k => k % d = a),
            (GoldbachMajorArc.primeWeight k : ℂ) * phase ((k : ℝ) * α / (d : ℝ)) := by
      rw [mul_sum]
      refine Finset.sum_bij (fun n _ => d * n + a) ?_ ?_ ?_ ?_
      · intro n hn
        have hnk := mem_range.mp hn
        have hdn : d * n + a < d * N := by
          have h1 : d * (n + 1) ≤ d * N := Nat.mul_le_mul_left d hnk
          rw [mul_add, mul_one] at h1; omega
        exact mem_filter.mpr ⟨mem_range.mpr (by rw [hM1]; exact hdn),
          by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt ha]⟩
      · intro n₁ _ n₂ _ heq
        exact Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_right_cancel heq)
      · intro k hk
        have hkm := mem_range.mp (mem_filter.mp hk).1
        have hkd : k % d = a := (mem_filter.mp hk).2
        refine ⟨k / d, mem_range.mpr (by rw [hM1] at hkm; exact (Nat.div_lt_iff_lt_mul (by omega)).mpr (by linarith)), ?_⟩
        rw [← hkd]; exact Nat.div_add_mod k d
      · intro n _
        rw [mul_left_comm, ← phase_add]
        congr 1; congr 1
        push_cast; field_simp; ring
    rw [h1]
    congr 1
    rw [sum_filter]
    have h2 : ∑ k ∈ range (M + 1),
          (if k % d = a then (GoldbachMajorArc.primeWeight k : ℂ) * phase ((k : ℝ) * α / (d : ℝ)) else 0) =
        ∑ k ∈ range (M + 1),
          (((1 / (d : ℝ) : ℝ) : ℂ) * ∑ j ∈ range d, phase (-(j : ℝ) * (((a : ℤ) - (k : ℤ) : ℤ) : ℝ) / (d : ℝ))) *
          ((GoldbachMajorArc.primeWeight k : ℂ) * phase ((k : ℝ) * α / (d : ℝ))) := by
      refine sum_congr rfl fun k _ => ?_
      rw [phase_orthog hd ((a : ℤ) - (k : ℤ))]
      have hiff : (d : ℤ) ∣ ((a : ℤ) - (k : ℤ)) ↔ k % d = a := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero]
        push_cast
        rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, eq_comm]
      by_cases hk : k % d = a
      · rw [ite_eq_left hk, ite_eq_left (hiff.mpr hk), one_mul]
      · rw [ite_eq_right hk, ite_eq_right (fun h => hk (hiff.mp h)), zero_mul]
    rw [h2]
    simp_rw [mul_assoc, ← mul_sum]
    congr 1
    simp_rw [sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    have hph : phase (-(j : ℝ) * (((a : ℤ) - (k : ℤ) : ℤ) : ℝ) / (d : ℝ)) * phase ((k : ℝ) * α / (d : ℝ)) =
        phase (-(j : ℝ) * (a : ℝ) / (d : ℝ)) * phase ((k : ℝ) * ((α + (j : ℝ)) / (d : ℝ))) := by
      rw [← phase_add, ← phase_add]; congr 1; push_cast; ring
    calc
      phase (-(j : ℝ) * (((a : ℤ) - (k : ℤ) : ℤ) : ℝ) / (d : ℝ)) *
          ((GoldbachMajorArc.primeWeight k : ℂ) * phase ((k : ℝ) * α / (d : ℝ)))
          = (GoldbachMajorArc.primeWeight k : ℂ) *
            (phase (-(j : ℝ) * (((a : ℤ) - (k : ℤ) : ℤ) : ℝ) / (d : ℝ)) * phase ((k : ℝ) * α / (d : ℝ))) := by ring
      _ = (GoldbachMajorArc.primeWeight k : ℂ) *
            (phase (-(j : ℝ) * (a : ℝ) / (d : ℝ)) * phase ((k : ℝ) * ((α + (j : ℝ)) / (d : ℝ)))) := by rw [hph]
      _ = phase (-(j : ℝ) * (a : ℝ) / (d : ℝ)) *
            ((GoldbachMajorArc.primeWeight k : ℂ) * phase ((k : ℝ) * ((α + (j : ℝ)) / (d : ℝ)))) := by ring
  have hsum_norm : ‖∑ n ∈ range N, (GoldbachMajorArc.primeWeight (d * n + a) : ℂ) * phase ((n : ℝ) * α)‖ ≤
      (M : ℝ) * (Real.log (M : ℝ)) ^ (-2 : ℝ) := by
    rw [hsum_ap, norm_mul, norm_phase, one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos one_pos hdpos)]
    have htri : ‖∑ j ∈ range d, phase (-(j : ℝ) * (a : ℝ) / (d : ℝ)) *
          ∑ k ∈ range (M + 1), (GoldbachMajorArc.primeWeight k : ℂ) *
            phase ((k : ℝ) * ((α + (j : ℝ)) / (d : ℝ)))‖ ≤
        (d : ℝ) * ((M : ℝ) * (Real.log (M : ℝ)) ^ (-2 : ℝ)) := by
      calc
        _ ≤ ∑ j ∈ range d, ‖phase (-(j : ℝ) * (a : ℝ) / (d : ℝ)) *
              ∑ k ∈ range (M + 1), (GoldbachMajorArc.primeWeight k : ℂ) *
                phase ((k : ℝ) * ((α + (j : ℝ)) / (d : ℝ)))‖ := norm_sum_le _ _
        _ ≤ ∑ _j ∈ range d, (M : ℝ) * (Real.log (M : ℝ)) ^ (-2 : ℝ) := by
          refine sum_le_sum fun j hj => ?_
          rw [norm_mul, norm_phase, one_mul]
          exact hminor_j j hj
        _ = (d : ℝ) * ((M : ℝ) * (Real.log (M : ℝ)) ^ (-2 : ℝ)) := by simp
    calc
      (1 / (d : ℝ)) * _ ≤ (1 / (d : ℝ)) * ((d : ℝ) * ((M : ℝ) * (Real.log (M : ℝ)) ^ (-2 : ℝ))) :=
        mul_le_mul_of_nonneg_left htri (by positivity)
      _ = (M : ℝ) * (Real.log (M : ℝ)) ^ (-2 : ℝ) := by field_simp
  have hfactor_nu : ((1 / (N : ℝ) : ℝ) : ℂ) *
        ∑ n ∈ range N, ((((d.totient : ℝ) / (d : ℝ) * GoldbachMajorArc.primeWeight (d * n + a) : ℝ) : ℂ) *
          phase ((n : ℝ) * α)) =
      (((d.totient : ℝ) / ((d : ℝ) * (N : ℝ)) : ℝ) : ℂ) *
        ∑ n ∈ range N, (GoldbachMajorArc.primeWeight (d * n + a) : ℂ) * phase ((n : ℝ) * α) := by
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun n _ => by push_cast; ring
  rw [hfactor_nu, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos (by exact_mod_cast Nat.totient_pos.mpr (by omega)) (by positivity))]
  have hphi_le_d : (d.totient : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.totient_le d
  have hinv2 : (Real.log (M : ℝ)) ^ (-2 : ℝ) ≤ 1 / (Real.log (N : ℝ)) ^ 2 := by
    rw [Real.rpow_neg (by linarith), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, one_div]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hlogM_ge 2)
  have hK_dz' : 100 * (d : ℝ) * (z : ℝ) ≤ Real.log (N : ℝ) := hK_dz.trans hlogN_ge
  calc
    ((d.totient : ℝ) / ((d : ℝ) * (N : ℝ))) *
        ‖∑ n ∈ range N, (GoldbachMajorArc.primeWeight (d * n + a) : ℂ) * phase ((n : ℝ) * α)‖
        ≤ (1 / (N : ℝ)) * (((d : ℝ) * (N : ℝ)) * (1 / (Real.log (N : ℝ)) ^ 2)) := by
      apply mul_le_mul _ (hsum_norm.trans (mul_le_mul hMr_le_dN hinv2 (by positivity) (by positivity)))
        (norm_nonneg _) (by positivity)
      rw [div_le_div_iff₀ (by positivity) hNpos]; nlinarith only [hphi_le_d, hNpos]
    _ = (d : ℝ) / (Real.log (N : ℝ)) ^ 2 := by field_simp
    _ ≤ 2 / (z : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [hK_dz', hlogN_pos, hdpos, show (0 : ℝ) < (z : ℝ) by positivity]
    _ ≤ ε := hε

theorem nu_fourier_decay {d a : ℕ} (hd : 1 ≤ d) (ha : a < d) (hcop : a.Coprime d)
    {z : ℕ} (hz : 2 ≤ z) (hprimes : ∀ p : ℕ, p.Prime → p ≤ z → p ∣ d)
    {ε : ℝ} (hε : 2 / (z : ℝ) ≤ ε) :
    ∃ N₀ : ℕ, ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∀ r : ZMod N, ‖PolynomialTransfer.F (fun x => nu d a N x - 1) r‖ ≤ ε := by
  obtain ⟨N₁, h1⟩ := nu_fourier_zero hd ha hcop hz hprimes hε
  obtain ⟨N₂, h2⟩ := nu_fourier_major hd ha hcop hz hprimes hε
  obtain ⟨N₃, h3⟩ := nu_fourier_minor hd ha hcop hz hprimes hε
  refine ⟨max N₁ (max N₂ N₃), fun N inst hN r => ?_⟩
  by_cases hr0 : r = 0
  · subst hr0; exact h1 N ((le_max_left _ _).trans hN)
  · by_cases hmaj : ∃ q b : ℕ, 1 ≤ q ∧ q ≤ (Nat.log 2 (d * N - 1 + 2)) ^ 20 ∧ b ≤ q ∧ b.Coprime q ∧
        |((N - r.val : ℕ) : ℝ) / (N : ℝ) - (b : ℝ) / (q : ℝ)| ≤
          (2 * (((Nat.log 2 (d * N - 1 + 2)) ^ 20 : ℕ) : ℝ)) / ((q : ℝ) * (N : ℝ))
    · exact h2 N (((le_max_left _ _).trans (le_max_right _ _)).trans hN) r hr0 hmaj
    · exact h3 N (((le_max_right _ _).trans (le_max_right _ _)).trans hN) r hr0 hmaj

/-! ### Section 5: Alsetri-Shao transference assembly and main theorem -/

open scoped Classical in
set_option maxHeartbeats 1200000 in
lemma dense_weight_lower {A : Set ℕ} (hA : ∀ p ∈ A, Nat.Prime p)
    {d a : ℕ} (hd2 : 2 ≤ d) (ha1 : 1 ≤ a) (had : a < d) (hcop : a.Coprime d)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hdense : ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ N ≥ T,
      (u - ε) * (((Icc 1 N).filter (fun p => Nat.Prime p ∧ p % d = a)).card : ℝ) ≤
        ((((Icc 1 N).filter (fun p => Nat.Prime p ∧ p % d = a)).filter (fun p => p ∈ A)).card : ℝ))
    {α γ : ℝ} (hα0 : 0 < α) (hα_le : α ≤ 1 / 4) (hγ0 : 0 < γ) :
    ∃ N₀ : ℕ, ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      let R : ℕ := ⌊(N : ℝ) ^ (1 / 20 : ℝ)⌋₊
      let M₁ : ℕ := ⌊(1 - α) * ((d * N : ℕ) : ℝ)⌋₊
      let f : ZMod N → ℝ := fun x =>
        if d * x.val + a ∈ A ∧ R < d * x.val + a ∧ d * x.val + a ≤ M₁ then nu d a N x else 0
      (∀ x, 0 ≤ f x) ∧
      (∀ x, f x ≤ nu d a N x) ∧
      (∀ x, f x ≤ 50 * sieveBeta d a R (x.val : ℤ)) ∧
      u - γ - 3 * α ≤ PolynomialTransfer.E f := by
  classical
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hphi_pos : (0 : ℝ) < (d.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  let β : ℝ := min (γ / 16) (1 / 8)
  have hβ_pos : 0 < β := lt_min (by linarith) (by norm_num)
  have hβ_le_γ : β ≤ γ / 16 := min_le_left _ _
  have hβ_le_8 : β ≤ 1 / 8 := min_le_right _ _
  obtain ⟨T_dense, hTd⟩ := hdense β hβ_pos
  obtain ⟨M_p, hM_p, x_p, hx_p, hprog⟩ :=
    GoldbachMajorArc.prime_progression_error 2 1 (by norm_num) (by norm_num)
  obtain ⟨C_l1, hC_l1, hl1⟩ := log_pow_le_rpow 1 (1 / 4 : ℝ) (by norm_num)
  obtain ⟨C_lb, hC_lb, hlb⟩ := log_pow_le_rpow 1 (β / 2) (by linarith)
  -- Large real threshold K_s
  obtain ⟨K_s, hKs_100, hKs_d, hKs_mp, hKs_xp, hKs_cl1, hKs_clb, hKs_α, hKs_Td⟩ :
      ∃ K_s : ℝ, 100 ≤ K_s ∧ (d : ℝ) ^ 2 ≤ K_s ∧ 10 * M_p * (d : ℝ) / β ≤ K_s ∧
        x_p ≤ K_s ∧ 40 * (C_l1 + 1) * (d : ℝ) ^ 2 / β ≤ K_s ∧
        2 * (d : ℝ) * C_lb / β ≤ K_s ∧ 4 / α ≤ K_s ∧ (T_dense : ℝ) ≤ K_s := by
    refine ⟨max (max (max 100 ((d : ℝ) ^ 2)) (max (10 * M_p * (d : ℝ) / β) x_p))
      (max (max (40 * (C_l1 + 1) * (d : ℝ) ^ 2 / β) (2 * (d : ℝ) * C_lb / β)) (max (4 / α) (T_dense : ℝ))),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_max_of_le_left (le_max_of_le_left (le_max_left _ _))
    · exact le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
    · exact le_max_of_le_left (le_max_of_le_right (le_max_left _ _))
    · exact le_max_of_le_left (le_max_of_le_right (le_max_right _ _))
    · exact le_max_of_le_right (le_max_of_le_left (le_max_left _ _))
    · exact le_max_of_le_right (le_max_of_le_left (le_max_right _ _))
    · exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
    · exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  obtain ⟨N_log, hN_log2, hN_log⟩ := exists_nat_log_ge (2 * K_s)
  let N_pow : ℕ := max (⌈K_s ^ (2 / β)⌉₊ + 100) (max (⌈K_s ^ 4⌉₊ + 100) (max ((d ^ 2 + 2) ^ 20) ((2 ^ 25 * d) ^ 4 + 100)))
  refine ⟨max N_log (max N_pow (2 * T_dense + 100)), ?_⟩
  intro N inst hN
  dsimp only
  let R : ℕ := ⌊(N : ℝ) ^ (1 / 20 : ℝ)⌋₊
  let M : ℕ := d * N
  let M₁ : ℕ := ⌊(1 - α) * (M : ℝ)⌋₊
  let f : ZMod N → ℝ := fun x =>
    if d * x.val + a ∈ A ∧ R < d * x.val + a ∧ d * x.val + a ≤ M₁ then nu d a N x else 0
  have hN2 : 2 ≤ N := (hN_log2.trans (le_max_left _ _)).trans hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hMpos : (0 : ℝ) < (M : ℝ) := by dsimp [M]; positivity
  have hM1_le_M : (N : ℝ) ≤ (M : ℝ) := by
    dsimp [M]; push_cast
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
    nlinarith only [hd1, hNpos]
  have hN_pow : N_pow ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hN_Td : 2 * T_dense + 100 ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hR_ge_d2 : d ^ 2 + 2 ≤ R := by
    have h1 : (d ^ 2 + 2) ^ 20 ≤ N :=
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hN_pow
    have h2 : (((d ^ 2 + 2 : ℕ) : ℝ) ^ 20) ≤ (N : ℝ) := by exact_mod_cast h1
    have h3 : ((d ^ 2 + 2 : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) := by
      have := Real.rpow_le_rpow (by positivity) h2 (by norm_num : (0 : ℝ) ≤ 1 / 20)
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        show ((20 : ℕ) : ℝ) * (1 / 20 : ℝ) = 1 by norm_num, Real.rpow_one] at this
      exact this
    exact Nat.le_floor h3
  have hR1 : 1 ≤ R := by omega
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR1
  have hnu_nonneg : ∀ x : ZMod N, 0 ≤ nu d a N x := by
    intro x; unfold nu GoldbachMajorArc.primeWeight
    apply mul_nonneg (by positivity)
    split_ifs with hp
    · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
    · exact le_rfl
  -- Part 1 & Part 2
  have hf0 : ∀ x, 0 ≤ f x := by
    intro x; dsimp [f]; split_ifs
    · exact hnu_nonneg x
    · exact le_rfl
  have hf_le_nu : ∀ x, f x ≤ nu d a N x := by
    intro x; dsimp [f]; split_ifs
    · exact le_rfl
    · exact hnu_nonneg x
  -- Part 3: pointwise majorant f x ≤ 50 * sieveBeta d a R x.val
  have hf_le_beta : ∀ x, f x ≤ 50 * sieveBeta d a R (x.val : ℤ) := by
    intro x
    dsimp [f]
    split_ifs with hcond
    · rcases hcond with ⟨hpA, hpR, hpM1⟩
      let p : ℕ := d * x.val + a
      have hpp : p.Prime := hA p hpA
      have hnatAbs : ((d : ℤ) * (x.val : ℤ) + (a : ℤ)).natAbs = p := by
        have : (d : ℤ) * (x.val : ℤ) + (a : ℤ) = (p : ℤ) := by simp [p]
        rw [this, Int.natAbs_natCast]
      have hbeta_eq : sieveBeta d a R (x.val : ℤ) = G d R :=
        sieveBeta_eq_G_of_prime hR1 (hnatAbs.symm ▸ hpp) (hnatAbs.symm ▸ hpR)
      have hG_lb : ((d.totient : ℝ) / (2 * (d : ℝ))) * Real.log (R : ℝ) ≤ G d R :=
        G_lower_bound d R (by omega) (by omega)
      have hR_half : (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 20 : ℝ) ≤ (R : ℝ) := by
        have hlt : (N : ℝ) ^ (1 / 20 : ℝ) < (R : ℝ) + 1 := Nat.lt_floor_add_one _
        have hR2 : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : 2 ≤ R)
        linarith
      have hN_225 : ((2 : ℝ) ^ 25 * (d : ℝ)) ^ 4 ≤ (N : ℝ) := by
        have h1 : (2 ^ 25 * d) ^ 4 ≤ N :=
          ((Nat.le_add_right _ 100).trans
            ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hN_pow
        exact_mod_cast h1
      have hN14 : (2 : ℝ) ^ 25 * (d : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
        have := Real.rpow_le_rpow (by positivity) hN_225 (by norm_num : (0 : ℝ) ≤ 1 / 4)
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
          show ((4 : ℕ) : ℝ) * (1 / 4 : ℝ) = 1 by norm_num, Real.rpow_one] at this
        exact this
      have hp_le_M : (p : ℝ) ≤ (d : ℝ) * (N : ℝ) := by
        have h1 : p ≤ d * N := by
          have : M₁ ≤ M := by
            dsimp [M₁]
            exact Nat.floor_le_of_le (by nlinarith only [hα0, hMpos])
          exact hpM1.trans this
        exact_mod_cast h1
      have hR25 : (d : ℝ) * (N : ℝ) ≤ (R : ℝ) ^ 25 := by
        have hpow : ((1 / 2 : ℝ) * (N : ℝ) ^ (1 / 20 : ℝ)) ^ 25 ≤ (R : ℝ) ^ 25 :=
          pow_le_pow_left₀ (by positivity) hR_half 25
        have hrhs_eq : ((1 / 2 : ℝ) * (N : ℝ) ^ (1 / 20 : ℝ)) ^ 25 =
            ((N : ℝ) ^ (1 / 4 : ℝ) / (2 : ℝ) ^ 25) * (N : ℝ) := by
          rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (1 / 20 : ℝ)) 25, ← Real.rpow_mul hNpos.le]
          have hexp : (N : ℝ) ^ ((1 / 20 : ℝ) * (25 : ℕ)) = (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) := by
            conv_rhs => arg 2; rw [← Real.rpow_one (N : ℝ)]
            rw [← Real.rpow_add hNpos]; norm_num
          rw [hexp]; ring
        have hdiv : (d : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) / (2 : ℝ) ^ 25 := by
          rw [le_div_iff₀ (by positivity)]; linarith
        calc
          (d : ℝ) * (N : ℝ) ≤ ((N : ℝ) ^ (1 / 4 : ℝ) / (2 : ℝ) ^ 25) * (N : ℝ) :=
            mul_le_mul_of_nonneg_right hdiv hNpos.le
          _ = ((1 / 2 : ℝ) * (N : ℝ) ^ (1 / 20 : ℝ)) ^ 25 := hrhs_eq.symm
          _ ≤ (R : ℝ) ^ 25 := hpow
      have hlog_p : Real.log (p : ℝ) ≤ 25 * Real.log (R : ℝ) := by
        have h1 := Real.log_le_log (by exact_mod_cast hpp.pos) (hp_le_M.trans hR25)
        rw [Real.log_pow] at h1
        simpa using h1
      have hnu_eq : nu d a N x = ((d.totient : ℝ) / (d : ℝ)) * Real.log (p : ℝ) := by
        unfold nu GoldbachMajorArc.primeWeight; simp [p, hpp]
      rw [hnu_eq, hbeta_eq]
      calc
        ((d.totient : ℝ) / (d : ℝ)) * Real.log (p : ℝ)
            ≤ ((d.totient : ℝ) / (d : ℝ)) * (25 * Real.log (R : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog_p (by positivity)
        _ = 50 * (((d.totient : ℝ) / (2 * (d : ℝ))) * Real.log (R : ℝ)) := by ring
        _ ≤ 50 * G d R := mul_le_mul_of_nonneg_left hG_lb (by norm_num)
    · exact mul_nonneg (by norm_num) (sieveBeta_nonneg d a R (x.val : ℤ))
  -- Part 4: average lower bound u - γ - 3 * α ≤ E f
  have hf_avg : u - γ - 3 * α ≤ PolynomialTransfer.E f := by
    by_cases hu_small : u ≤ β
    · have hE0 : 0 ≤ PolynomialTransfer.E f := PolynomialTransfer.Enonneg hf0
      linarith
    · push Not at hu_small
      have hlogN_ge : 2 * K_s ≤ Real.log (N : ℝ) := hN_log N ((le_max_left _ _).trans hN)
      have hlogM_ge : 2 * K_s ≤ Real.log (M : ℝ) := hlogN_ge.trans (Real.log_le_log hNpos hM1_le_M)
      have hN_ge_Ks4 : K_s ^ 4 ≤ (N : ℝ) := by
        have h1 : K_s ^ 4 ≤ (⌈K_s ^ 4⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : ⌈K_s ^ 4⌉₊ ≤ N :=
          ((Nat.le_add_right _ 100).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hN_pow
        have h3 : (⌈K_s ^ 4⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
        linarith
      have hN_ge_Ks_b : K_s ^ (2 / β) ≤ (N : ℝ) := by
        have h1 : K_s ^ (2 / β) ≤ (⌈K_s ^ (2 / β)⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : ⌈K_s ^ (2 / β)⌉₊ ≤ N :=
          ((Nat.le_add_right _ 100).trans (le_max_left _ _)).trans hN_pow
        have h3 : (⌈K_s ^ (2 / β)⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
        linarith
      have hM1_lb : (1 - 2 * α) * (M : ℝ) ≤ (M₁ : ℝ) := by
        have hlt : (1 - α) * (M : ℝ) < (M₁ : ℝ) + 1 := Nat.lt_floor_add_one _
        have h1_le : (1 : ℝ) ≤ α * (M : ℝ) := by
          have hKs1 : 4 / α ≤ (N : ℝ) := by
            have : K_s ≤ K_s ^ 4 := le_self_pow₀ (by linarith) (by decide)
            linarith
          have : 4 ≤ α * (N : ℝ) := by have := (div_le_iff₀ hα0).mp hKs1; linarith
          nlinarith only [this, hM1_le_M, hα0]
        linarith
      have hM1_le_Mr : (M₁ : ℝ) ≤ (M : ℝ) :=
        (Nat.floor_le (by nlinarith only [hα_le, hMpos])).trans (by nlinarith only [hα0, hMpos])
      have hM1_ge_half : (1 / 2 : ℝ) * (M : ℝ) ≤ (M₁ : ℝ) := by
        nlinarith only [hM1_lb, hα_le, hMpos]
      have hM1_pos : (0 : ℝ) < (M₁ : ℝ) := by linarith
      have hM1_ge_Td : T_dense ≤ M₁ := by
        have h1 : (T_dense : ℝ) ≤ (M₁ : ℝ) := by
          have : (T_dense : ℝ) ≤ (N : ℝ) / 2 := by
            have hT2 : 2 * T_dense ≤ N := (Nat.le_add_right _ 100).trans hN_Td
            have hT2r : 2 * (T_dense : ℝ) ≤ (N : ℝ) := by exact_mod_cast hT2
            linarith
          linarith
        exact_mod_cast h1
      have hlogM1_ge : K_s ≤ Real.log (M₁ : ℝ) := by
        have h1 := Real.log_le_log (by positivity) hM1_ge_half
        rw [Real.log_mul (by norm_num) hMpos.ne', one_div, Real.log_inv] at h1
        have hlog2 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          linarith
        linarith
      have hlogM1_pos : 0 < Real.log (M₁ : ℝ) := by linarith
      have hlogM_pos : 0 < Real.log (M : ℝ) := by linarith
      have hlogM1_le : Real.log (M₁ : ℝ) ≤ Real.log (M : ℝ) := Real.log_le_log hM1_pos hM1_le_Mr
      -- Lower bound classMass (M₁ + 1) d a via prime_progression_error 2 1
      have hM1_xp : x_p ≤ (M₁ : ℝ) := by
        have h1 : K_s ≤ (N : ℝ) / 2 := by
          have hKs2 : 2 * K_s ≤ K_s ^ 4 := by
            have h2 : (100 : ℝ) ^ 2 ≤ K_s ^ 2 := by nlinarith only [hKs_100]
            have h3 : (100 : ℝ) ^ 2 * K_s ≤ K_s ^ 3 := by nlinarith only [h2, hKs_100]
            nlinarith only [h3, hKs_100]
          linarith
        linarith
      have hd_logM1 : (d : ℝ) ≤ (Real.log (M₁ : ℝ)) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
        have hd1 : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
          have hd2r : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
          nlinarith only [hd2r]
        linarith
      have hsw := hprog M₁ d a hM1_xp (by omega) hd_logM1 had hcop
      have hcm_lb : (1 - β) * ((M₁ : ℝ) / (d.totient : ℝ)) ≤ GoldbachMajorArc.classMass (M₁ + 1) d a := by
        have herr1 : M_p * (M₁ : ℝ) * (Real.log (M₁ : ℝ)) ^ (-2 : ℝ) ≤ (β / 2) * ((M₁ : ℝ) / (d.totient : ℝ)) := by
          have hinv : (Real.log (M₁ : ℝ)) ^ (-2 : ℝ) = 1 / (Real.log (M₁ : ℝ)) ^ 2 := by
            rw [Real.rpow_neg (by linarith), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
          rw [hinv]
          have hphi_le : (d.totient : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.totient_le d
          have h1 : M_p * (d.totient : ℝ) ≤ (β / 2) * (Real.log (M₁ : ℝ)) ^ 2 := by
            have hmp : 10 * M_p * (d : ℝ) ≤ β * K_s := by have := (div_le_iff₀ hβ_pos).mp hKs_mp; linarith
            have hK2 : K_s ≤ (Real.log (M₁ : ℝ)) ^ 2 := by nlinarith only [hKs_100, hlogM1_ge]
            have hmp2 : M_p * (d.totient : ℝ) ≤ M_p * (d : ℝ) := mul_le_mul_of_nonneg_left hphi_le hM_p.le
            nlinarith only [hmp, hK2, hmp2, hβ_pos, hKs_100]
          have h2 : M_p * (M₁ : ℝ) * (1 / (Real.log (M₁ : ℝ)) ^ 2) =
              ((M_p * (d.totient : ℝ)) / (Real.log (M₁ : ℝ)) ^ 2) * ((M₁ : ℝ) / (d.totient : ℝ)) := by
            field_simp
          rw [h2]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [div_le_iff₀ (pow_pos hlogM1_pos 2)]
          linarith
        have herr2 : (Nat.log 2 M₁ : ℝ) * Real.log (d : ℝ) + 2 * Real.sqrt (M₁ : ℝ) * Real.log (M₁ : ℝ) ≤
            (β / 2) * ((M₁ : ℝ) / (d.totient : ℝ)) := by
          have hM1_1 : (1 : ℝ) ≤ (M₁ : ℝ) := by linarith
          have hlog2 : (Nat.log 2 M₁ : ℝ) ≤ 2 * Real.log (M₁ : ℝ) :=
            nat_log2_le_two_log (by exact_mod_cast hM1_1)
          have hlog_sq : Real.log (M₁ : ℝ) ≤ C_l1 * (M₁ : ℝ) ^ (1 / 4 : ℝ) := by simpa using hl1 (M₁ : ℝ) hM1_1
          have hprod : Real.sqrt (M₁ : ℝ) * (M₁ : ℝ) ^ (1 / 4 : ℝ) = (M₁ : ℝ) ^ (3 / 4 : ℝ) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_add hM1_pos]; norm_num
          have hlogd : Real.log (d : ℝ) ≤ Real.sqrt (M₁ : ℝ) := by
            have h1 : Real.log (d : ℝ) ≤ (d : ℝ) := (Real.log_le_sub_one_of_pos hdpos).trans (by linarith)
            have h2 : (d : ℝ) ≤ Real.sqrt (M₁ : ℝ) := by
              rw [Real.le_sqrt hdpos.le hM1_pos.le]
              have hK2 : K_s ≤ (N : ℝ) / 2 := by
                have : 2 * K_s ≤ K_s ^ 4 := by
                  have hsq : (100 : ℝ) ^ 2 ≤ K_s ^ 2 := by nlinarith only [hKs_100]
                  have hcu : (100 : ℝ) ^ 2 * K_s ≤ K_s ^ 3 := by nlinarith only [hsq, hKs_100]
                  nlinarith only [hcu, hKs_100]
                linarith
              linarith
            linarith
          have hsum_le : (Nat.log 2 M₁ : ℝ) * Real.log (d : ℝ) + 2 * Real.sqrt (M₁ : ℝ) * Real.log (M₁ : ℝ) ≤
              4 * C_l1 * (M₁ : ℝ) ^ (3 / 4 : ℝ) := by
            have ha' : (Nat.log 2 M₁ : ℝ) * Real.log (d : ℝ) ≤ 2 * C_l1 * (M₁ : ℝ) ^ (3 / 4 : ℝ) := by
              calc
                (Nat.log 2 M₁ : ℝ) * Real.log (d : ℝ) ≤ (2 * Real.log (M₁ : ℝ)) * Real.sqrt (M₁ : ℝ) :=
                  mul_le_mul hlog2 hlogd (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ d))) (by positivity)
                _ ≤ (2 * (C_l1 * (M₁ : ℝ) ^ (1 / 4 : ℝ))) * Real.sqrt (M₁ : ℝ) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog_sq (by norm_num)) (Real.sqrt_nonneg _)
                _ = 2 * C_l1 * (Real.sqrt (M₁ : ℝ) * (M₁ : ℝ) ^ (1 / 4 : ℝ)) := by ring
                _ = 2 * C_l1 * (M₁ : ℝ) ^ (3 / 4 : ℝ) := by rw [hprod]
            have hb' : 2 * Real.sqrt (M₁ : ℝ) * Real.log (M₁ : ℝ) ≤ 2 * C_l1 * (M₁ : ℝ) ^ (3 / 4 : ℝ) := by
              calc
                2 * Real.sqrt (M₁ : ℝ) * Real.log (M₁ : ℝ)
                    ≤ 2 * Real.sqrt (M₁ : ℝ) * (C_l1 * (M₁ : ℝ) ^ (1 / 4 : ℝ)) :=
                  mul_le_mul_of_nonneg_left hlog_sq (by positivity)
                _ = 2 * C_l1 * (Real.sqrt (M₁ : ℝ) * (M₁ : ℝ) ^ (1 / 4 : ℝ)) := by ring
                _ = 2 * C_l1 * (M₁ : ℝ) ^ (3 / 4 : ℝ) := by rw [hprod]
            linarith
          have hM1_14 : 8 * C_l1 * (d.totient : ℝ) / β ≤ (M₁ : ℝ) ^ (1 / 4 : ℝ) := by
            have hphi_le : (d.totient : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.totient_le d
            have h1 : K_s ≤ (M₁ : ℝ) ^ (1 / 4 : ℝ) := by
              have hM1_ge_N : (N : ℝ) ≤ (M₁ : ℝ) := by
                have hd2r : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
                have hMN : 2 * (N : ℝ) ≤ (M : ℝ) := by dsimp [M]; push_cast; nlinarith only [hd2r, hNpos]
                linarith
              have hK4 : K_s ^ 4 ≤ (M₁ : ℝ) := hN_ge_Ks4.trans hM1_ge_N
              have := Real.rpow_le_rpow (by positivity) hK4 (by norm_num : (0 : ℝ) ≤ 1 / 4)
              rw [← Real.rpow_natCast K_s 4, ← Real.rpow_mul (by linarith)] at this
              norm_num at this; exact this
            have h2 : 8 * C_l1 * (d.totient : ℝ) / β ≤ 40 * (C_l1 + 1) * (d : ℝ) ^ 2 / β := by
              apply div_le_div_of_nonneg_right _ hβ_pos.le
              have hd_sq : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
                have hd2r : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
                nlinarith only [hd2r]
              nlinarith only [hphi_le, hd_sq, hC_l1, hdpos]
            linarith
          have hM1_split : (M₁ : ℝ) = (M₁ : ℝ) ^ (1 / 4 : ℝ) * (M₁ : ℝ) ^ (3 / 4 : ℝ) := by
            rw [← Real.rpow_add hM1_pos]; norm_num
          have hmul : 4 * C_l1 * (M₁ : ℝ) ^ (3 / 4 : ℝ) ≤ (β / 2) * ((M₁ : ℝ) / (d.totient : ℝ)) := by
            have h3 : 8 * C_l1 * (d.totient : ℝ) ≤ β * (M₁ : ℝ) ^ (1 / 4 : ℝ) := by
              have := (div_le_iff₀ hβ_pos).mp hM1_14; linarith
            have h4 : 8 * C_l1 * (d.totient : ℝ) * (M₁ : ℝ) ^ (3 / 4 : ℝ) ≤
                β * ((M₁ : ℝ) ^ (1 / 4 : ℝ) * (M₁ : ℝ) ^ (3 / 4 : ℝ)) := by
              have := mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hM1_pos.le (3 / 4 : ℝ))
              linarith
            rw [← hM1_split] at h4
            rw [show (β / 2) * ((M₁ : ℝ) / (d.totient : ℝ)) = (β * (M₁ : ℝ)) / (2 * (d.totient : ℝ)) by ring,
              le_div_iff₀ (by positivity)]
            linarith
          linarith
        have hlo := (abs_le.mp hsw).1
        linarith
      -- Relate classMass (M₁ + 1) d a to card of primes in Icc 1 M₁
      let P1 : Finset ℕ := (Icc 1 M₁).filter (fun p => Nat.Prime p ∧ p % d = a)
      have hcm_le_P1 : GoldbachMajorArc.classMass (M₁ + 1) d a ≤ (P1.card : ℝ) * Real.log (M₁ : ℝ) := by
        unfold GoldbachMajorArc.classMass
        have hsub_sum : ∑ k ∈ (range (M₁ + 1)).filter (fun k => k % d = a), GoldbachMajorArc.primeWeight k =
            ∑ p ∈ P1, Real.log (p : ℝ) := by
          rw [← sum_filter_add_sum_filter_not ((range (M₁ + 1)).filter (fun k => k % d = a)) Nat.Prime]
          have hzero : ∑ k ∈ ((range (M₁ + 1)).filter (fun k => k % d = a)).filter (fun k => ¬ Nat.Prime k),
              GoldbachMajorArc.primeWeight k = 0 :=
            sum_eq_zero fun k hk => by unfold GoldbachMajorArc.primeWeight; simp [(mem_filter.mp hk).2]
          rw [hzero, add_zero]
          have hset_eq : ((range (M₁ + 1)).filter (fun k => k % d = a)).filter Nat.Prime = P1 := by
            ext p
            simp only [P1, mem_filter, mem_range, mem_Icc]
            constructor
            · rintro ⟨⟨hp1, hp2⟩, hpp⟩; exact ⟨⟨hpp.one_le, by omega⟩, hpp, hp2⟩
            · rintro ⟨⟨_, hp2⟩, hpp, hp3⟩; exact ⟨⟨by omega, hp3⟩, hpp⟩
          rw [hset_eq]
          exact sum_congr rfl fun p hp => by unfold GoldbachMajorArc.primeWeight; simp [(mem_filter.mp hp).2.1]
        rw [hsub_sum]
        calc
          ∑ p ∈ P1, Real.log (p : ℝ) ≤ ∑ _p ∈ P1, Real.log (M₁ : ℝ) :=
            sum_le_sum fun p hp =>
              Real.log_le_log (by exact_mod_cast (mem_filter.mp hp).2.1.pos)
                (by exact_mod_cast (mem_Icc.mp (mem_filter.mp hp).1).2)
          _ = (P1.card : ℝ) * Real.log (M₁ : ℝ) := by simp
      have hP1_lb : (1 - β) * (1 - 2 * α) * (M : ℝ) / ((d.totient : ℝ) * Real.log (M : ℝ)) ≤ (P1.card : ℝ) := by
        have h1 : (1 - β) * ((M₁ : ℝ) / (d.totient : ℝ)) / Real.log (M₁ : ℝ) ≤ (P1.card : ℝ) := by
          rw [div_le_iff₀ (by linarith)]
          exact hcm_lb.trans hcm_le_P1
        have h2 : (1 - β) * (1 - 2 * α) * (M : ℝ) / ((d.totient : ℝ) * Real.log (M : ℝ)) ≤
            (1 - β) * ((M₁ : ℝ) / (d.totient : ℝ)) / Real.log (M₁ : ℝ) := by
          rw [show (1 - β) * ((M₁ : ℝ) / (d.totient : ℝ)) / Real.log (M₁ : ℝ) =
              ((1 - β) * (M₁ : ℝ)) / ((d.totient : ℝ) * Real.log (M₁ : ℝ)) by ring]
          have hnum : (1 - β) * (1 - 2 * α) * (M : ℝ) ≤ (1 - β) * (M₁ : ℝ) := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hM1_lb (by linarith)
          have hden : (d.totient : ℝ) * Real.log (M₁ : ℝ) ≤ (d.totient : ℝ) * Real.log (M : ℝ) :=
            mul_le_mul_of_nonneg_left hlogM1_le hphi_pos.le
          exact (div_le_div_of_nonneg_right hnum (mul_pos hphi_pos hlogM_pos).le).trans
            (div_le_div_of_nonneg_left (by nlinarith only [hβ_le_8, hM1_pos]) (mul_pos hphi_pos hlogM1_pos) hden)
        exact h2.trans h1
      -- Discard small primes ≤ M₀ := ⌊M ^ (1 - β)⌋₊
      let M₀ : ℕ := ⌊(M : ℝ) ^ (1 - β)⌋₊
      have hR_le_M0 : R ≤ M₀ := by
        have h1 : (R : ℝ) ≤ (M : ℝ) ^ (1 - β) := by
          have hRN : (R : ℝ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) := Nat.floor_le (by positivity)
          have hNM : (N : ℝ) ^ (1 / 20 : ℝ) ≤ (M : ℝ) ^ (1 / 20 : ℝ) :=
            Real.rpow_le_rpow hNpos.le hM1_le_M (by norm_num)
          have hM1' : (1 : ℝ) ≤ (M : ℝ) := by linarith
          have hexp : (M : ℝ) ^ (1 / 20 : ℝ) ≤ (M : ℝ) ^ (1 - β) :=
            Real.rpow_le_rpow_of_exponent_le hM1' (by linarith)
          exact hRN.trans (hNM.trans hexp)
        exact Nat.le_floor h1
      let PA : Finset ℕ := P1.filter (fun p => p ∈ A)
      let S : Finset ℕ := PA.filter (fun p => M₀ < p)
      have hPA_lb : (u - β) * (P1.card : ℝ) ≤ (PA.card : ℝ) := hTd M₁ hM1_ge_Td
      have hS_lb : (u - β) * (P1.card : ℝ) - (M₀ : ℝ) ≤ (S.card : ℝ) := by
        have hsplit : PA.card = S.card + (PA.filter (fun p => ¬ (M₀ < p))).card :=
          (Finset.card_filter_add_card_filter_not _).symm
        have hsmall : (PA.filter (fun p => ¬ (M₀ < p))).card ≤ M₀ := by
          have hsub : PA.filter (fun p => ¬ (M₀ < p)) ⊆ Icc 1 M₀ := by
            intro p hp
            have h1 := mem_Icc.mp (mem_filter.mp (mem_filter.mp (mem_filter.mp hp).1).1).1
            have h2 := (mem_filter.mp hp).2
            exact mem_Icc.mpr ⟨h1.1, by omega⟩
          exact (card_le_card hsub).trans (by simp)
        have hsplit_r : (PA.card : ℝ) = (S.card : ℝ) + ((PA.filter (fun p => ¬ (M₀ < p))).card : ℝ) := by
          exact_mod_cast hsplit
        have hsmall_r : ((PA.filter (fun p => ¬ (M₀ < p))).card : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hsmall
        linarith
      -- Inject S into ZMod N via p ↦ ((p / d : ℕ) : ZMod N)
      let φ : ℕ → ZMod N := fun p => ((p / d : ℕ) : ZMod N)
      have hφ_val : ∀ p ∈ S, (φ p).val = p / d ∧ d * (φ p).val + a = p := by
        intro p hp
        have hpPA := (mem_filter.mp hp).1
        have hpP1 := (mem_filter.mp hpPA).1
        have hple : p ≤ M₁ := (mem_Icc.mp (mem_filter.mp hpP1).1).2
        have hpmod : p % d = a := (mem_filter.mp hpP1).2.2
        have hpM : p < d * N := by
          have hle : p ≤ d * N := hple.trans (by exact_mod_cast hM1_le_Mr)
          by_contra hge
          have heq : p = d * N := by omega
          rw [heq, Nat.mul_mod_right] at hpmod
          omega
        have hdiv_lt : p / d < N := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by linarith)
        have hval : (φ p).val = p / d := ZMod.val_natCast_of_lt hdiv_lt
        refine ⟨hval, ?_⟩
        rw [hval, ← hpmod]; exact Nat.div_add_mod p d
      have hφ_inj : ∀ p₁ ∈ S, ∀ p₂ ∈ S, φ p₁ = φ p₂ → p₁ = p₂ := by
        intro p₁ h₁ p₂ h₂ heq
        have e1 := (hφ_val p₁ h₁).2
        have e2 := (hφ_val p₂ h₂).2
        rw [← e1, ← e2, heq]
      have hf_on_S : ∀ p ∈ S, ((d.totient : ℝ) / (d : ℝ)) * ((1 - β) * Real.log (M : ℝ)) ≤ f (φ p) := by
        intro p hp
        have hpPA := (mem_filter.mp hp).1
        have hpM0 : M₀ < p := (mem_filter.mp hp).2
        have hpA : p ∈ A := (mem_filter.mp hpPA).2
        have hpP1 := (mem_filter.mp hpPA).1
        have hpp : p.Prime := (mem_filter.mp hpP1).2.1
        have hple : p ≤ M₁ := (mem_Icc.mp (mem_filter.mp hpP1).1).2
        have hdp : d * (φ p).val + a = p := (hφ_val p hp).2
        have hpR : R < p := lt_of_le_of_lt hR_le_M0 hpM0
        have hf_eq : f (φ p) = ((d.totient : ℝ) / (d : ℝ)) * Real.log (p : ℝ) := by
          dsimp [f]; rw [hdp, ite_eq_left ⟨hpA, hpR, hple⟩]
          unfold nu GoldbachMajorArc.primeWeight; rw [hdp, ite_eq_left hpp]
        rw [hf_eq]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hM_rpow_lt : (M : ℝ) ^ (1 - β) < (p : ℝ) := by
          have h1 : (M : ℝ) ^ (1 - β) < (M₀ : ℝ) + 1 := Nat.lt_floor_add_one _
          have h2 : (M₀ : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hpM0
          linarith
        have hlog_lb := Real.log_le_log (Real.rpow_pos_of_pos hMpos _) hM_rpow_lt.le
        rwa [Real.log_rpow hMpos] at hlog_lb
      have hEf_ge : ((d.totient : ℝ) * (1 - β) * Real.log (M : ℝ) / (M : ℝ)) * (S.card : ℝ) ≤ PolynomialTransfer.E f := by
        unfold PolynomialTransfer.E
        have hsum_lb : (S.card : ℝ) * (((d.totient : ℝ) / (d : ℝ)) * ((1 - β) * Real.log (M : ℝ))) ≤
            ∑ x : ZMod N, f x := by
          calc
            (S.card : ℝ) * (((d.totient : ℝ) / (d : ℝ)) * ((1 - β) * Real.log (M : ℝ)))
                = ∑ _p ∈ S, ((d.totient : ℝ) / (d : ℝ)) * ((1 - β) * Real.log (M : ℝ)) := by simp
            _ ≤ ∑ p ∈ S, f (φ p) := sum_le_sum hf_on_S
            _ = ∑ x ∈ S.image φ, f x := (sum_image hφ_inj).symm
            _ ≤ ∑ x : ZMod N, f x := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _ => hf0 x)
        have hM_eq : (M : ℝ) = (d : ℝ) * (N : ℝ) := by dsimp [M]; push_cast; rfl
        have hrw : ((d.totient : ℝ) * (1 - β) * Real.log (M : ℝ) / (M : ℝ)) * (S.card : ℝ) =
            ((S.card : ℝ) * (((d.totient : ℝ) / (d : ℝ)) * ((1 - β) * Real.log (M : ℝ)))) / (N : ℝ) := by
          rw [hM_eq]; ring
        rw [hrw]
        exact div_le_div_of_nonneg_right hsum_lb hNpos.le
      have hM0_err : ((d.totient : ℝ) * (1 - β) * Real.log (M : ℝ) / (M : ℝ)) * (M₀ : ℝ) ≤ β := by
        have hM0_le : (M₀ : ℝ) ≤ (M : ℝ) ^ (1 - β) := Nat.floor_le (by positivity)
        have hphi_le : (d.totient : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.totient_le d
        have hlogM_le : Real.log (M : ℝ) ≤ C_lb * (M : ℝ) ^ (β / 2) := by simpa using hlb (M : ℝ) (by linarith)
        have hM_beta : K_s ≤ (M : ℝ) ^ (β / 2) := by
          have h1 : K_s ^ (2 / β) ≤ (M : ℝ) := hN_ge_Ks_b.trans hM1_le_M
          have := Real.rpow_le_rpow (by positivity) h1 (by positivity : (0 : ℝ) ≤ β / 2)
          rw [← Real.rpow_mul (by linarith)] at this
          have hexp : 2 / β * (β / 2) = 1 := by field_simp
          rw [hexp, Real.rpow_one] at this
          exact this
        have hprod_M : (M : ℝ) ^ (β / 2) * (M : ℝ) ^ (1 - β) / (M : ℝ) = 1 / (M : ℝ) ^ (β / 2) := by
          have h1 : (M : ℝ) ^ (β / 2) * (M : ℝ) ^ (1 - β) = (M : ℝ) ^ (1 - β / 2) := by
            rw [← Real.rpow_add hMpos]; congr 1; ring
          have h2 : (M : ℝ) = (M : ℝ) ^ (1 - β / 2) * (M : ℝ) ^ (β / 2) := by
            rw [← Real.rpow_add hMpos]; simp
          rw [h1]; conv_lhs => arg 2; rw [h2]
          have hne : (M : ℝ) ^ (1 - β / 2) ≠ 0 := (Real.rpow_pos_of_pos hMpos _).ne'
          field_simp
        calc
          ((d.totient : ℝ) * (1 - β) * Real.log (M : ℝ) / (M : ℝ)) * (M₀ : ℝ)
              ≤ ((d : ℝ) * 1 * (C_lb * (M : ℝ) ^ (β / 2)) / (M : ℝ)) * (M : ℝ) ^ (1 - β) := by
            apply mul_le_mul _ hM0_le (Nat.cast_nonneg M₀) (by positivity)
            apply div_le_div_of_nonneg_right _ hMpos.le
            exact mul_le_mul (mul_le_mul hphi_le (by linarith) (by linarith) hdpos.le)
              hlogM_le (Real.log_nonneg (by linarith)) (by positivity)
          _ = (d : ℝ) * C_lb * ((M : ℝ) ^ (β / 2) * (M : ℝ) ^ (1 - β) / (M : ℝ)) := by ring
          _ = (d : ℝ) * C_lb / (M : ℝ) ^ (β / 2) := by rw [hprod_M]; ring
          _ ≤ β := by
            rw [div_le_iff₀ (Real.rpow_pos_of_pos hMpos _)]
            have h1 : 2 * (d : ℝ) * C_lb ≤ β * K_s := by
              have := (div_le_iff₀ hβ_pos).mp hKs_clb; linarith
            nlinarith only [h1, hM_beta, hβ_pos, hdpos, hC_lb]
      -- Combine main term and M₀ error
      have hfac_nonneg : 0 ≤ (d.totient : ℝ) * (1 - β) * Real.log (M : ℝ) / (M : ℝ) := by
        have : 0 ≤ 1 - β := by linarith
        have : 0 ≤ Real.log (M : ℝ) := by linarith
        positivity
      have hmain_comb : (1 - β) ^ 2 * (1 - 2 * α) * (u - β) - β ≤ PolynomialTransfer.E f := by
        have h1 : ((d.totient : ℝ) * (1 - β) * Real.log (M : ℝ) / (M : ℝ)) *
              ((u - β) * (P1.card : ℝ) - (M₀ : ℝ)) ≤ PolynomialTransfer.E f :=
          (mul_le_mul_of_nonneg_left hS_lb hfac_nonneg).trans hEf_ge
        have h2 : (1 - β) ^ 2 * (1 - 2 * α) * (u - β) ≤
            ((d.totient : ℝ) * (1 - β) * Real.log (M : ℝ) / (M : ℝ)) * ((u - β) * (P1.card : ℝ)) := by
          have hcancel : (1 - β) ^ 2 * (1 - 2 * α) * (u - β) =
              ((d.totient : ℝ) * (1 - β) * Real.log (M : ℝ) / (M : ℝ)) *
                ((u - β) * ((1 - β) * (1 - 2 * α) * (M : ℝ) / ((d.totient : ℝ) * Real.log (M : ℝ)))) := by
            have hlogM_ne : Real.log (M : ℝ) ≠ 0 := by linarith
            field_simp
          rw [hcancel]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP1_lb (by linarith)) hfac_nonneg
        have hdist : ((d.totient : ℝ) * (1 - β) * Real.log (M : ℝ) / (M : ℝ)) *
              ((u - β) * (P1.card : ℝ) - (M₀ : ℝ)) =
            ((d.totient : ℝ) * (1 - β) * Real.log (M : ℝ) / (M : ℝ)) * ((u - β) * (P1.card : ℝ)) -
            ((d.totient : ℝ) * (1 - β) * Real.log (M : ℝ) / (M : ℝ)) * (M₀ : ℝ) := by ring
        linarith
      have hfinal_alg : u - γ - 3 * α ≤ (1 - β) ^ 2 * (1 - 2 * α) * (u - β) - β := by
        have hub1 : 0 ≤ u - β := by linarith
        have hub2 : u - β ≤ 1 := by linarith
        have h1 : 1 - 2 * β ≤ (1 - β) ^ 2 := by nlinarith only [sq_nonneg β]
        have h2 : 1 - 2 * β - 2 * α ≤ (1 - β) ^ 2 * (1 - 2 * α) := by
          nlinarith only [h1, hβ_pos, hβ_le_8, hα0, hα_le]
        have h3 : (1 - 2 * β - 2 * α) * (u - β) ≤ (1 - β) ^ 2 * (1 - 2 * α) * (u - β) :=
          mul_le_mul_of_nonneg_right h2 hub1
        have h4 : (u - β) - 2 * β - 2 * α ≤ (1 - 2 * β - 2 * α) * (u - β) := by
          nlinarith only [hub1, hub2, hβ_pos, hα0]
        linarith
      exact hfinal_alg.trans hmain_comb
  exact ⟨hf0, hf_le_nu, hf_le_beta, hf_avg⟩

lemma geometric_cover_bound (P : ℕ → Prop) [DecidablePred P]
    {M_thresh : ℕ} {α C : ℝ} (hα0 : 0 < α) (hα_le : α ≤ 1 / 2) (hC0 : 0 ≤ C)
    (hstep : ∀ M : ℕ, M_thresh ≤ M →
      (((Ioc ⌊(1 - α) * (M : ℝ)⌋₊ M).filter P).card : ℝ) ≤ C * α * (M : ℝ)) :
    ∀ X : ℕ, (((Icc 1 X).filter P).card : ℝ) ≤ (M_thresh : ℝ) + 2 * C * (X : ℝ) := by
  intro X
  induction X using Nat.strong_induction_on with
  | ind X ih =>
    by_cases hX : X < M_thresh
    · have hcard : ((Icc 1 X).filter P).card ≤ X := by
        calc
          ((Icc 1 X).filter P).card ≤ (Icc 1 X).card := card_le_card (filter_subset _ _)
          _ = X := by simp
      have hcard_r : (((Icc 1 X).filter P).card : ℝ) ≤ (X : ℝ) := by exact_mod_cast hcard
      have hXM : (X : ℝ) ≤ (M_thresh : ℝ) := by exact_mod_cast hX.le
      nlinarith only [hcard_r, hXM, hC0, Nat.cast_nonneg (α := ℝ) X]
    · push Not at hX
      by_cases hX0 : X = 0
      · subst hX0; simp
      · have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
        let X₁ : ℕ := ⌊(1 - α) * (X : ℝ)⌋₊
        have hX1_lt : X₁ < X := by
          dsimp [X₁]
          exact (Nat.floor_lt (by nlinarith only [hα_le, hXpos])).mpr (by nlinarith only [hα0, hXpos])
        have hsub : (Icc 1 X).filter P ⊆ (Icc 1 X₁).filter P ∪ (Ioc X₁ X).filter P := by
          intro n hn
          have h1 := mem_Icc.mp (mem_filter.mp hn).1
          have hP := (mem_filter.mp hn).2
          by_cases hle : n ≤ X₁
          · exact mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨h1.1, hle⟩, hP⟩)
          · exact mem_union_right _ (mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, h1.2⟩, hP⟩)
        have hcard : ((Icc 1 X).filter P).card ≤
            ((Icc 1 X₁).filter P).card + ((Ioc X₁ X).filter P).card :=
          (card_le_card hsub).trans (card_union_le _ _)
        have hcard_r : (((Icc 1 X).filter P).card : ℝ) ≤
            (((Icc 1 X₁).filter P).card : ℝ) + (((Ioc X₁ X).filter P).card : ℝ) := by
          exact_mod_cast hcard
        have hih := ih X₁ hX1_lt
        have hst := hstep X hX
        have hX1_le : (X₁ : ℝ) ≤ (1 - α) * (X : ℝ) := Nat.floor_le (by nlinarith only [hα_le, hXpos])
        have hmul : 2 * C * (X₁ : ℝ) ≤ 2 * C * ((1 - α) * (X : ℝ)) :=
          mul_le_mul_of_nonneg_left hX1_le (by linarith)
        have htail : 0 ≤ C * α * (X : ℝ) := by positivity
        linarith

open scoped Classical in
set_option maxHeartbeats 1200000 in
lemma interval_exceptional_bound {A B : Set ℕ} (hA : ∀ p ∈ A, Nat.Prime p) (hB : ∀ p ∈ B, Nat.Prime p)
    {W b : ℕ} (hW : 0 < W) (hb : b < W)
    {δ : ℝ} (hδ : 0 < δ)
    (hcompat : ∀ d : ℕ, 0 < d → 2 * W ∣ d → ∀ r : ℕ, r < d → Even r → r % W = b →
      ∃ a c : ℕ, a < d ∧ c < d ∧ a.Coprime d ∧ c.Coprime d ∧ (a + c) % d = r ∧
        ∃ u v : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ 0 ≤ v ∧ v ≤ 1 ∧ 1 + δ ≤ u + v ∧
          (∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ N ≥ T,
            (u - ε) * (((Icc 1 N).filter (fun p => Nat.Prime p ∧ p % d = a)).card : ℝ) ≤
              ((((Icc 1 N).filter (fun p => Nat.Prime p ∧ p % d = a)).filter (fun p => p ∈ A)).card : ℝ)) ∧
          (∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ N ≥ T,
            (v - ε) * (((Icc 1 N).filter (fun p => Nat.Prime p ∧ p % d = c)).card : ℝ) ≤
              ((((Icc 1 N).filter (fun p => Nat.Prime p ∧ p % d = c)).filter (fun p => p ∈ B)).card : ℝ)))
    {η : ℝ} (hη : 0 < η) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 / 4 ∧ ∃ M_thresh : ℕ, ∀ M : ℕ, M_thresh ≤ M →
      (((Ioc ⌊(1 - α) * (M : ℝ)⌋₊ M).filter
          (fun n => Even n ∧ n % W = b ∧ ¬ ∃ p ∈ A, ∃ q ∈ B, p + q = n)).card : ℝ) ≤
        (η / (4 * (W : ℝ))) * α * (M : ℝ) := by
  classical
  let δ' : ℝ := min 1 δ / 2
  have hδ'_pos : 0 < δ' := by dsimp [δ']; exact div_pos (lt_min one_pos hδ) (by norm_num)
  have hδ'_le1 : δ' ≤ 1 := by dsimp [δ']; linarith [min_le_left (1 : ℝ) δ]
  have h2δ'_le : 2 * δ' ≤ δ := by dsimp [δ']; linarith [min_le_right (1 : ℝ) δ]
  let α : ℝ := δ' / 32
  have hα_pos : 0 < α := by dsimp [α]; linarith
  have hα_le4 : α ≤ 1 / 4 := by dsimp [α]; linarith
  let η' : ℝ := min 1 (η * α / 6)
  have hη'_pos : 0 < η' := lt_min one_pos (by positivity)
  have hη'_le1 : η' ≤ 1 := min_le_left _ _
  have hη'_le : η' ≤ η * α / 6 := min_le_right _ _
  obtain ⟨M_abs, hM_abs, hlp⟩ := sieveBeta_extension_lp
  obtain ⟨c_tr, K_tr, hc_tr, hK_tr, htrans⟩ :=
    PolynomialTransfer.mainBound (p := 15 / 4) (M := M_abs) (by norm_num) (by norm_num) hM_abs
  let ε_dec : ℝ := c_tr * (δ' * η') ^ K_tr
  have hε_dec_pos : 0 < ε_dec := mul_pos hc_tr (Real.rpow_pos_of_pos (mul_pos hδ'_pos hη'_pos) _)
  let z : ℕ := max 2 (⌈4 / ε_dec⌉₊ + 1)
  have hz2 : 2 ≤ z := le_max_left _ _
  have h2z_le : 2 / (z : ℝ) ≤ ε_dec := by
    have hz_ge : 4 / ε_dec ≤ (z : ℝ) := by
      have h1 : 4 / ε_dec ≤ (⌈4 / ε_dec⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈4 / ε_dec⌉₊ : ℝ) ≤ (z : ℝ) := by
        exact_mod_cast (Nat.le_add_right _ 1).trans (le_max_right 2 _)
      linarith
    rw [div_le_iff₀ (by exact_mod_cast (by omega : 0 < z))]
    have hmul : 4 ≤ ε_dec * (z : ℝ) := by
      have := (div_le_iff₀ hε_dec_pos).mp hz_ge
      linarith
    linarith
  let Pz : Finset ℕ := (Icc 2 z).filter Nat.Prime
  let d : ℕ := 2 * W * ∏ p ∈ Pz, p
  have hprod_pos : 1 ≤ ∏ p ∈ Pz, p :=
    Nat.succ_le_of_lt (prod_pos fun p hp => (mem_filter.mp (show p ∈ (Icc 2 z).filter Nat.Prime from hp)).2.pos)
  have hd2 : 2 ≤ d := by dsimp [d]; nlinarith only [hW, hprod_pos]
  have hd_pos : 0 < d := by omega
  have h2W_dvd : 2 * W ∣ d := dvd_mul_right (2 * W) _
  have hW_dvd : W ∣ d := (dvd_mul_left W 2).trans h2W_dvd
  have h2_dvd : 2 ∣ d := (dvd_mul_right 2 W).trans h2W_dvd
  have hprimes_d : ∀ p : ℕ, p.Prime → p ≤ z → p ∣ d := by
    intro p hpp hpz
    have hmem : p ∈ Pz := mem_filter.mpr ⟨mem_Icc.mpr ⟨hpp.two_le, hpz⟩, hpp⟩
    exact (Finset.dvd_prod_of_mem id hmem).trans (dvd_mul_left _ (2 * W))
  let R_classes : Finset ℕ := (range d).filter (fun r => Even r ∧ r % W = b)
  -- Per-class bound for each r ∈ R_classes
  have hper_r : ∀ r ∈ R_classes, ∃ M_r : ℕ, ∀ M : ℕ, M_r ≤ M →
      (((Ioc ⌊(1 - α) * (M : ℝ)⌋₊ M).filter
          (fun m => m % d = r ∧ ¬ ∃ p ∈ A, ∃ q ∈ B, p + q = m)).card : ℝ) ≤
        η' * ((3 / 2 : ℝ) * ((M : ℝ) / (d : ℝ))) := by
    intro r hr
    have hr_lt : r < d := mem_range.mp (mem_filter.mp hr).1
    have hr_even : Even r := (mem_filter.mp hr).2.1
    have hr_mod : r % W = b := (mem_filter.mp hr).2.2
    obtain ⟨a, c, ha_lt, hc_lt, ha_cop, hc_cop, hac_mod, u, v, hu0, hu1, hv0, hv1, huv, hdu, hdv⟩ :=
      hcompat d hd_pos h2W_dvd r hr_lt hr_even hr_mod
    have ha1 : 1 ≤ a := by
      by_contra h0; have ha0 : a = 0 := by omega
      subst ha0; rw [Nat.coprime_zero_left] at ha_cop; omega
    have hc1 : 1 ≤ c := by
      by_contra h0; have hc0 : c = 0 := by omega
      subst hc0; rw [Nat.coprime_zero_left] at hc_cop; omega
    obtain ⟨N_u, hNu⟩ := dense_weight_lower hA hd2 ha1 ha_lt ha_cop hu0 hu1 hdu hα_pos hα_le4 (by linarith : 0 < δ' / 8)
    obtain ⟨N_v, hNv⟩ := dense_weight_lower hB hd2 hc1 hc_lt hc_cop hv0 hv1 hdv hα_pos hα_le4 (by linarith : 0 < δ' / 8)
    obtain ⟨N_fa, hNfa⟩ := nu_fourier_decay (by omega) ha_lt ha_cop hz2 hprimes_d h2z_le
    obtain ⟨N_fc, hNfc⟩ := nu_fourier_decay (by omega) hc_lt hc_cop hz2 hprimes_d h2z_le
    let N_min_r : ℕ := max (max N_u N_v) (max (max N_fa N_fc) (max (d + 10) (⌈4 / α⌉₊ + 10)))
    refine ⟨d * N_min_r + 4 * d, ?_⟩
    intro M hM
    let N : ℕ := M / d + 1
    let : NeZero N := ⟨Nat.succ_ne_zero _⟩
    have hN_ge : N_min_r ≤ N := by
      dsimp [N]
      have : N_min_r ≤ M / d := (Nat.le_div_iff_mul_le hd_pos).mpr (by nlinarith only [hM, hd_pos])
      omega
    have hN_u : N_u ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN_ge
    have hN_v : N_v ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN_ge
    have hN_fa : N_fa ≤ N := ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hN_ge
    have hN_fc : N_fc ≤ N := ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hN_ge
    have hd_le_N : d ≤ N :=
      (Nat.le_add_right d 10).trans
        (((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hN_ge)
    have hN_α : 4 / α ≤ (N : ℝ) := by
      have h1 : 4 / α ≤ (⌈4 / α⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ⌈4 / α⌉₊ ≤ N :=
        (Nat.le_add_right _ 10).trans
          (((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hN_ge)
      have h3 : (⌈4 / α⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
      linarith
    let R : ℕ := ⌊(N : ℝ) ^ (1 / 20 : ℝ)⌋₊
    let M₁ : ℕ := ⌊(1 - α) * ((d * N : ℕ) : ℝ)⌋₊
    let f : ZMod N → ℝ := fun x =>
      if d * x.val + a ∈ A ∧ R < d * x.val + a ∧ d * x.val + a ≤ M₁ then nu d a N x else 0
    let g : ZMod N → ℝ := fun x =>
      if d * x.val + c ∈ B ∧ R < d * x.val + c ∧ d * x.val + c ≤ M₁ then nu d c N x else 0
    obtain ⟨hf0, hf_nu, hf_beta, hf_avg⟩ := hNu N hN_u
    obtain ⟨hg0, hg_nu, hg_beta, hg_avg⟩ := hNv N hN_v
    have hsum_avg : 1 + δ' ≤ PolynomialTransfer.E f + PolynomialTransfer.E g := by
      have h6α : 6 * α = 3 * δ' / 16 := by dsimp [α]; ring
      linarith
    have hff : ∑ r' : ZMod N, ‖PolynomialTransfer.F f r'‖ ^ (15 / 4 : ℝ) ≤ M_abs ^ (15 / 4 : ℝ) :=
      hlp d a N ha1 ha_lt hd_le_N ha_cop f hf0 hf_beta
    have hfg : ∑ r' : ZMod N, ‖PolynomialTransfer.F g r'‖ ^ (15 / 4 : ℝ) ≤ M_abs ^ (15 / 4 : ℝ) :=
      hlp d c N hc1 hc_lt hd_le_N hc_cop g hg0 hg_beta
    have hdec : ∀ r' : ZMod N,
        ‖PolynomialTransfer.F (fun x => nu d a N x - 1) r'‖ ≤ c_tr * (δ' * η') ^ K_tr ∧
        ‖PolynomialTransfer.F (fun x => nu d c N x - 1) r'‖ ≤ c_tr * (δ' * η') ^ K_tr :=
      fun r' => ⟨hNfa N hN_fa r', hNfc N hN_fc r'⟩
    have hbad := htrans δ' η' hδ'_pos hδ'_le1 hη'_pos hη'_le1 N f g (nu d a N) (nu d c N)
      (fun x => ⟨hf0 x, hf_nu x, hg0 x, hg_nu x⟩) hsum_avg hff hfg hdec
    -- Inject the missed integers in Ioc ⌊(1 - α) M⌋₊ M with m % d = r into the bad ZMod N set
    let Er : Finset ℕ := (Ioc ⌊(1 - α) * (M : ℝ)⌋₊ M).filter
      (fun m => m % d = r ∧ ¬ ∃ p ∈ A, ∃ q ∈ B, p + q = m)
    let Bad : Finset (ZMod N) := univ.filter (fun n => PolynomialTransfer.conv f g n < δ' ^ 3 / 1000)
    let ψ : ℕ → ZMod N := fun m => (((m - (a + c)) / d : ℕ) : ZMod N)
    have hM_lt_dN : M < d * N := by
      dsimp [N]; rw [mul_add, mul_one, mul_comm d (M / d)]; exact Nat.lt_div_mul_add hd_pos
    have hdN_le_Md : d * N ≤ M + d := by
      dsimp [N]; rw [mul_add, mul_one]
      have := Nat.mul_div_le M d; omega
    have hψ_prop : ∀ m ∈ Er, a + c ≤ m ∧ (m - (a + c)) / d < N ∧
        d * (ψ m).val + (a + c) = m := by
      intro m hm
      have hIoc := mem_Ioc.mp (mem_filter.mp hm).1
      have hmod : m % d = r := (mem_filter.mp hm).2.1
      have h1a : (1 - α) * (M : ℝ) < (m : ℝ) := by
        have h1 : (1 - α) * (M : ℝ) < (⌊(1 - α) * (M : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
        have h2 : (⌊(1 - α) * (M : ℝ)⌋₊ : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hIoc.1
        linarith
      have hac_le : a + c ≤ m := by
        have hM4d : 4 * d ≤ M := by omega
        have hmr : (2 * d : ℝ) ≤ (m : ℝ) := by
          have hM4dr : (4 * d : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM4d
          nlinarith only [h1a, hα_le4, hM4dr]
        have h2d_le : 2 * d ≤ m := by exact_mod_cast hmr
        omega
      have hdvd : d ∣ (m - (a + c)) := by
        have h1 : (m - (a + c)) % d = 0 := by
          rw [← Nat.dvd_iff_mod_eq_zero]
          have heq : (m : ℤ) - ((a + c : ℕ) : ℤ) = ((m - (a + c) : ℕ) : ℤ) := by omega
          rw [← Int.natCast_dvd_natCast, ← heq, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero,
            Int.cast_natCast, Int.cast_natCast, ZMod.natCast_eq_natCast_iff', hmod, hac_mod]
        exact Nat.dvd_of_mod_eq_zero h1
      have hdiv_lt : (m - (a + c)) / d < N := by
        apply (Nat.div_lt_iff_lt_mul hd_pos).mpr
        have : m - (a + c) ≤ M := (Nat.sub_le m _).trans hIoc.2
        linarith
      have hval : (ψ m).val = (m - (a + c)) / d := ZMod.val_natCast_of_lt hdiv_lt
      refine ⟨hac_le, hdiv_lt, ?_⟩
      rw [hval, Nat.mul_div_cancel' hdvd, Nat.sub_add_cancel hac_le]
    have hψ_maps : ∀ m ∈ Er, ψ m ∈ Bad := by
      intro m hm
      have hIoc := mem_Ioc.mp (mem_filter.mp hm).1
      have hmiss : ¬ ∃ p ∈ A, ∃ q ∈ B, p + q = m := (mem_filter.mp hm).2.2
      have hprop := hψ_prop m hm
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      by_contra hnot
      push Not at hnot
      have hpos_conv : 0 < PolynomialTransfer.conv f g (ψ m) :=
        lt_of_lt_of_le (by positivity) hnot
      unfold PolynomialTransfer.conv PolynomialTransfer.E at hpos_conv
      have hsum_pos : 0 < ∑ x : ZMod N, f x * g (ψ m - x) :=
        (div_pos_iff_of_pos_right (by exact_mod_cast NeZero.pos N)).mp hpos_conv
      have hex : ∃ x : ZMod N, 0 < f x * g (ψ m - x) := by
        by_contra hall
        push Not at hall
        have hle0 : ∑ x : ZMod N, f x * g (ψ m - x) ≤ 0 :=
          sum_nonpos fun x _ => hall x
        linarith
      obtain ⟨x, hx_pos⟩ := hex
      have hfx_ne : f x ≠ 0 := fun h => by rw [h, zero_mul] at hx_pos; exact lt_irrefl 0 hx_pos
      have hgy_ne : g (ψ m - x) ≠ 0 := fun h => by rw [h, mul_zero] at hx_pos; exact lt_irrefl 0 hx_pos
      have hfx_cond : d * x.val + a ∈ A ∧ R < d * x.val + a ∧ d * x.val + a ≤ M₁ := by
        by_contra hc; exact hfx_ne (by dsimp [f]; rw [ite_eq_right hc])
      have hgy_cond : d * (ψ m - x).val + c ∈ B ∧ R < d * (ψ m - x).val + c ∧ d * (ψ m - x).val + c ≤ M₁ := by
        by_contra hc; exact hgy_ne (by dsimp [g]; rw [ite_eq_right hc])
      -- No wrap-around in ZMod N: x.val + (ψ m - x).val = (ψ m).val
      let p : ℕ := d * x.val + a
      let q : ℕ := d * (ψ m - x).val + c
      have hmodN : (x.val + (ψ m - x).val) % N = (ψ m).val := by
        have h1 : ((x.val + (ψ m - x).val : ℕ) : ZMod N) = ψ m := by
          push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]; ring
        have h2 := (ZMod.natCast_eq_natCast_iff' (x.val + (ψ m - x).val) (ψ m).val N).mp
          (by rwa [ZMod.natCast_zmod_val])
        rwa [Nat.mod_eq_of_lt (ψ m).val_lt] at h2
      have hsum_val : x.val + (ψ m - x).val = (ψ m).val ∨ x.val + (ψ m - x).val = (ψ m).val + N := by
        have hlt1 : x.val < N := x.val_lt
        have hlt2 : (ψ m - x).val < N := (ψ m - x).val_lt
        have hdiv := Nat.div_add_mod (x.val + (ψ m - x).val) N
        rw [hmodN] at hdiv
        have hq_le : (x.val + (ψ m - x).val) / N ≤ 1 := by
          have : x.val + (ψ m - x).val < 2 * N := by omega
          exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (NeZero.pos N)).mpr (by linarith))
        interval_cases ((x.val + (ψ m - x).val) / N) <;> [left; right] <;> omega
      rcases hsum_val with hnowrap | hwrap
      · apply hmiss
        refine ⟨p, hfx_cond.1, q, hgy_cond.1, ?_⟩
        dsimp [p, q]
        have h3 := hprop.2.2
        calc
          d * x.val + a + (d * (ψ m - x).val + c)
              = d * (x.val + (ψ m - x).val) + (a + c) := by ring
          _ = d * (ψ m).val + (a + c) := by rw [hnowrap]
          _ = m := h3
      · exfalso
        have hpq_eq : p + q = m + d * N := by
          dsimp [p, q]
          have h3 := hprop.2.2
          calc
            d * x.val + a + (d * (ψ m - x).val + c)
                = d * (x.val + (ψ m - x).val) + (a + c) := by ring
            _ = d * ((ψ m).val + N) + (a + c) := by rw [hwrap]
            _ = (d * (ψ m).val + (a + c)) + d * N := by ring
            _ = m + d * N := by rw [h3]
        have hpq_le : ((p + q : ℕ) : ℝ) ≤ 2 * (1 - α) * ((d * N : ℕ) : ℝ) := by
          have hM1_r : (M₁ : ℝ) ≤ (1 - α) * ((d * N : ℕ) : ℝ) :=
            Nat.floor_le (by nlinarith only [hα_le4, Nat.cast_nonneg (α := ℝ) (d * N)])
          have hp_r : (p : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hfx_cond.2.2
          have hq_r : (q : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hgy_cond.2.2
          rw [Nat.cast_add]; linarith
        have hm_gt : (1 - α) * (M : ℝ) < (m : ℝ) := by
          have h1 : (1 - α) * (M : ℝ) < (⌊(1 - α) * (M : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
          have h2 : (⌊(1 - α) * (M : ℝ)⌋₊ : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hIoc.1
          linarith
        have hM_ge_dN : ((d * N : ℕ) : ℝ) - (d : ℝ) ≤ (M : ℝ) := by
          have : ((d * N : ℕ) : ℝ) ≤ (M : ℝ) + (d : ℝ) := by exact_mod_cast hdN_le_Md
          linarith
        have hαdN : (d : ℝ) ≤ α * ((d * N : ℕ) : ℝ) := by
          have h1 : 4 ≤ α * (N : ℝ) := by have := (div_le_iff₀ hα_pos).mp hN_α; linarith
          have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
          push_cast
          nlinarith only [h1, hdpos]
        have hm_dN_gt : 2 * (1 - α) * ((d * N : ℕ) : ℝ) < ((m + d * N : ℕ) : ℝ) := by
          push_cast at hpq_le hM_ge_dN hαdN ⊢
          nlinarith only [hm_gt, hM_ge_dN, hαdN, hα_pos, hα_le4]
        rw [hpq_eq] at hpq_le
        linarith
    have hψ_inj : ∀ m₁ ∈ Er, ∀ m₂ ∈ Er, ψ m₁ = ψ m₂ → m₁ = m₂ := by
      intro m₁ h₁ m₂ h₂ heq
      have e1 := (hψ_prop m₁ h₁).2.2
      have e2 := (hψ_prop m₂ h₂).2.2
      rw [← e1, ← e2, heq]
    have hEr_le : (Er.card : ℝ) ≤ η' * (N : ℝ) := by
      have hc : Er.card ≤ Bad.card := by
        rw [← card_image_of_injOn hψ_inj]
        exact card_le_card fun x hx => by obtain ⟨m, hm, rfl⟩ := mem_image.mp hx; exact hψ_maps m hm
      exact (by exact_mod_cast hc : (Er.card : ℝ) ≤ (Bad.card : ℝ)).trans hbad
    have hN_le : (N : ℝ) ≤ (3 / 2 : ℝ) * ((M : ℝ) / (d : ℝ)) := by
      have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
      have h1 : (N : ℝ) ≤ (M : ℝ) / (d : ℝ) + 1 := by
        dsimp [N]; push_cast
        have hdiv : ((M / d : ℕ) : ℝ) * (d : ℝ) ≤ (M : ℝ) := by
          exact_mod_cast Nat.div_mul_le_self M d
        have : ((M / d : ℕ) : ℝ) ≤ (M : ℝ) / (d : ℝ) := (le_div_iff₀ hdpos).mpr hdiv
        linarith
      have h2 : (2 * d : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 2 * d ≤ M)
      have h3 : (2 : ℝ) ≤ (M : ℝ) / (d : ℝ) := (le_div_iff₀ hdpos).mpr (by linarith)
      linarith
    exact hEr_le.trans (mul_le_mul_of_nonneg_left hN_le hη'_pos.le)
  -- Choose uniform threshold M_thresh across the finite set R_classes
  choose M_of_r hM_of_r using fun r : {r // r ∈ R_classes} => hper_r r.1 r.2
  let M_thresh : ℕ := R_classes.attach.sup M_of_r
  refine ⟨α, hα_pos, hα_le4, M_thresh, ?_⟩
  intro M hM
  let Eall : Finset ℕ := (Ioc ⌊(1 - α) * (M : ℝ)⌋₊ M).filter
    (fun n => Even n ∧ n % W = b ∧ ¬ ∃ p ∈ A, ∃ q ∈ B, p + q = n)
  have hmaps : ∀ n ∈ Eall, n % d ∈ R_classes := by
    intro n hn
    have hcond := (mem_filter.mp hn).2
    refine mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt n hd_pos), ?_, ?_⟩
    · rw [Nat.even_iff, Nat.mod_mod_of_dvd n h2_dvd]
      exact Nat.even_iff.mp hcond.1
    · rw [Nat.mod_mod_of_dvd n hW_dvd]; exact hcond.2.1
  have hcard_sum : (Eall.card : ℝ) = ∑ r ∈ R_classes, ((Eall.filter (fun n => n % d = r)).card : ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise hmaps)
  have hR_card : (R_classes.card : ℝ) ≤ (d : ℝ) / (W : ℝ) := by
    have hdiv_eq : W * (d / W) = d := Nat.mul_div_cancel' hW_dvd
    have hinj : ∀ r₁ ∈ R_classes, ∀ r₂ ∈ R_classes, r₁ / W = r₂ / W → r₁ = r₂ := by
      intro r₁ h₁ r₂ h₂ heq
      have hm1 : r₁ % W = b := (mem_filter.mp h₁).2.2
      have hm2 : r₂ % W = b := (mem_filter.mp h₂).2.2
      calc
        r₁ = W * (r₁ / W) + r₁ % W := (Nat.div_add_mod r₁ W).symm
        _ = W * (r₂ / W) + r₂ % W := by rw [heq, hm1, hm2]
        _ = r₂ := Nat.div_add_mod r₂ W
    have hmaps_W : ∀ r ∈ R_classes, r / W ∈ range (d / W) := by
      intro r hr
      have hrlt : r < d := mem_range.mp (mem_filter.mp hr).1
      exact mem_range.mpr ((Nat.div_lt_iff_lt_mul hW).mpr (by linarith))
    have hc : R_classes.card ≤ d / W := by
      rw [← card_image_of_injOn hinj, ← card_range (d / W)]
      exact card_le_card fun x hx => by obtain ⟨r, hr, rfl⟩ := mem_image.mp hx; exact hmaps_W r hr
    have hcr : (R_classes.card : ℝ) ≤ ((d / W : ℕ) : ℝ) := by exact_mod_cast hc
    have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
    have hdWr : ((d / W : ℕ) : ℝ) = (d : ℝ) / (W : ℝ) := by
      rw [eq_div_iff hWpos.ne']; exact_mod_cast (by linarith : (d / W) * W = d)
    linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
  calc
    (Eall.card : ℝ) = ∑ r ∈ R_classes, ((Eall.filter (fun n => n % d = r)).card : ℝ) := hcard_sum
    _ ≤ ∑ _r ∈ R_classes, (η' * ((3 / 2 : ℝ) * ((M : ℝ) / (d : ℝ)))) := by
      refine sum_le_sum fun r hr => ?_
      have hMr : M_of_r ⟨r, hr⟩ ≤ M := (Finset.le_sup (f := M_of_r) (mem_attach R_classes ⟨r, hr⟩)).trans hM
      have hsub : Eall.filter (fun n => n % d = r) ⊆
          (Ioc ⌊(1 - α) * (M : ℝ)⌋₊ M).filter (fun m => m % d = r ∧ ¬ ∃ p ∈ A, ∃ q ∈ B, p + q = m) := by
        intro n hn
        have h1 := (mem_filter.mp hn).1
        have h2 := (mem_filter.mp hn).2
        exact mem_filter.mpr ⟨(mem_filter.mp h1).1, h2, (mem_filter.mp h1).2.2.2⟩
      exact (by exact_mod_cast card_le_card hsub : ((Eall.filter (fun n => n % d = r)).card : ℝ) ≤ _).trans
        (hM_of_r ⟨r, hr⟩ M hMr)
    _ = (R_classes.card : ℝ) * (η' * ((3 / 2 : ℝ) * ((M : ℝ) / (d : ℝ)))) := by simp
    _ ≤ ((d : ℝ) / (W : ℝ)) * ((η * α / 6) * ((3 / 2 : ℝ) * ((M : ℝ) / (d : ℝ)))) := by
      apply mul_le_mul hR_card (mul_le_mul_of_nonneg_right hη'_le (by positivity))
        (by positivity) (by positivity)
    _ = (η / (4 * (W : ℝ))) * α * (M : ℝ) := by field_simp; ring

end
end PrimeLocalCompatibleColors

theorem Conjectures.Goldbach.PrimeLocalCompatibleColors :
by
  classical
  let primes := fun N q a : ℕ => (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ p % q = a)
  let dense := fun (A : Set ℕ) (d a : ℕ) (t : ℝ) => ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ N ≥ T, (t - ε) * ((primes N d a).card : ℝ) ≤ (((primes N d a).filter (fun p => p ∈ A)).card : ℝ)
  exact ∀ A B : Set ℕ, (∀ p ∈ A, Nat.Prime p) → (∀ p ∈ B, Nat.Prime p) →
    ∀ W b : ℕ, 0 < W → b < W → (∃ δ : ℝ, 0 < δ ∧ ∀ d : ℕ, 0 < d → 2 * W ∣ d → ∀ r : ℕ, r < d → Even r → r % W = b →
      ∃ a c : ℕ, a < d ∧ c < d ∧ a.Coprime d ∧ c.Coprime d ∧ (a + c) % d = r ∧ ∃ u v : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ 0 ≤ v ∧ v ≤ 1 ∧ 1 + δ ≤ u + v ∧ dense A d a u ∧ dense B d c v) →
    ∀ η : ℝ, 0 < η → ∃ T : ℕ, ∀ X ≥ T, (((Finset.Icc 1 X).filter (fun n => Even n ∧ n % W = b ∧ ¬ ∃ p ∈ A, ∃ q ∈ B, p + q = n)).card : ℝ) ≤ η * (X : ℝ) / (W : ℝ) := by
  classical
  dsimp only
  intro A B hA hB W b hW hb hcompat η hη
  obtain ⟨δ, hδ, hcomp⟩ := hcompat
  obtain ⟨α, hα0, hα4, M_thresh, hstep⟩ :=
    PrimeLocalCompatibleColors.interval_exceptional_bound hA hB hW hb hδ hcomp hη
  have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  have hcov := PrimeLocalCompatibleColors.geometric_cover_bound
    (fun n => Even n ∧ n % W = b ∧ ¬ ∃ p ∈ A, ∃ q ∈ B, p + q = n)
    hα0 (by linarith) (by positivity) hstep
  refine ⟨⌈2 * (W : ℝ) * (M_thresh : ℝ) / η⌉₊, ?_⟩
  intro X hX
  have h1 := hcov X
  have hX_ge : 2 * (W : ℝ) * (M_thresh : ℝ) / η ≤ (X : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hX)
  have hMt_le : (M_thresh : ℝ) ≤ (η / (2 * (W : ℝ))) * (X : ℝ) := by
    have hmul : 2 * (W : ℝ) * (M_thresh : ℝ) ≤ η * (X : ℝ) := by
      have := (div_le_iff₀ hη).mp hX_ge; linarith
    rw [show (η / (2 * (W : ℝ))) * (X : ℝ) = (η * (X : ℝ)) / (2 * (W : ℝ)) by ring,
      le_div_iff₀ (by positivity)]
    linarith
  calc
    (((Finset.Icc 1 X).filter (fun n => Even n ∧ n % W = b ∧ ¬ ∃ p ∈ A, ∃ q ∈ B, p + q = n)).card : ℝ)
        ≤ (M_thresh : ℝ) + 2 * (η / (4 * (W : ℝ))) * (X : ℝ) := h1
    _ ≤ (η / (2 * (W : ℝ))) * (X : ℝ) + 2 * (η / (4 * (W : ℝ))) * (X : ℝ) := by linarith
    _ = η * (X : ℝ) / (W : ℝ) := by ring
