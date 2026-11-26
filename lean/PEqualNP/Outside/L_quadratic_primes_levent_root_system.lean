import Mathlib

private theorem cosine_orthogonality :
    let angle := fun p k : ℕ => fun t : ℝ => 2 * Real.pi * k * t / p;
    ∀ p n r : ℕ, 0 < p →
      (∑ k ∈ Finset.range p, Real.cos (angle p k ((n : ℝ) - r))) =
        if n % p = r % p then (p : ℝ) else 0 := by
  intro angle p n r hp
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have htp : (2 : ℝ) * Real.pi ≠ 0 := Real.two_pi_pos.ne'
  -- the basic angle: the k-th angle is its k-th multiple
  let θ : ℝ := 2 * Real.pi * ((n : ℝ) - r) / p
  have hθ : θ = 2 * Real.pi * ((n : ℝ) - (r : ℝ)) / (p : ℝ) := rfl
  have hangle : ∀ k : ℕ, angle p k ((n : ℝ) - r) = (k : ℝ) * θ := by
    intro k
    show 2 * Real.pi * (k : ℝ) * ((n : ℝ) - (r : ℝ)) / (p : ℝ) = (k : ℝ) * θ
    rw [hθ]
    field_simp [hpR] <;> ring
  -- the rotation factor, and its powers as exponentials of the multiples
  let z : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  have hz : z = Complex.exp ((θ : ℂ) * Complex.I) := rfl
  have hpow : ∀ k : ℕ, z ^ k = Complex.exp (((k : ℝ) * θ : ℂ) * Complex.I) := by
    intro k
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    simp only [Complex.ofReal_natCast]
    ring
  -- the k-th cosine is the real part of the k-th power
  have hcos : ∀ k : ℕ, (z ^ k).re = Real.cos (angle p k ((n : ℝ) - r)) := by
    intro k
    rw [hpow, Complex.exp_re, hangle]
    have h1 : (((k : ℝ) * θ : ℂ) * Complex.I).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]
    have h2 : (((k : ℝ) * θ : ℂ) * Complex.I).im = (k : ℝ) * θ := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]
    rw [h1, h2, Real.exp_zero, one_mul]
  -- a cosine one-liner: the exponential is one exactly at the whole turns
  have hre : ∀ x : ℝ, (Complex.exp ((x : ℂ) * Complex.I)).re = Real.cos x := by
    intro x
    rw [Complex.exp_re]
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Real.exp_zero]
  have hexp : ∀ x : ℝ,
      Complex.exp ((x : ℂ) * Complex.I) = 1 ↔ ∃ m : ℤ, x = (m : ℝ) * (2 * Real.pi) := by
    intro x
    constructor
    · intro h
      have hc : Real.cos x = 1 := by
        rw [← hre x]
        exact congrArg Complex.re h
      obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff x).mp hc
      exact ⟨m, hm.symm⟩
    · rintro ⟨m, rfl⟩
      rw [Complex.exp_eq_one_iff]
      refine ⟨m, ?_⟩
      rw [Complex.ext_iff]
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_mul,
        Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_intCast]
  -- so the rotation factor is one precisely when p divides the difference
  have hdvd : ((p : ℤ) ∣ (n : ℤ) - (r : ℤ)) ↔ n % p = r % p := by
    rw [← Int.modEq_iff_dvd, ← Int.modEq_comm, Int.natCast_modEq_iff]
    exact Iff.rfl
  have hz1 : z = 1 ↔ n % p = r % p := by
    rw [hz, hexp θ, hθ, ← hdvd]
    constructor
    · rintro ⟨m, hm⟩
      have h2 : 2 * Real.pi * ((n : ℝ) - (r : ℝ)) = 2 * Real.pi * ((m : ℝ) * (p : ℝ)) := by
        calc 2 * Real.pi * ((n : ℝ) - (r : ℝ))
            = (2 * Real.pi * ((n : ℝ) - (r : ℝ)) / (p : ℝ)) * (p : ℝ) := by field_simp [hpR]
          _ = ((m : ℝ) * (2 * Real.pi)) * (p : ℝ) := by rw [hm]
          _ = 2 * Real.pi * ((m : ℝ) * (p : ℝ)) := by ring
      have h3 : (n : ℝ) - (r : ℝ) = (p : ℝ) * (m : ℝ) := by
        rw [mul_comm]
        exact mul_left_cancel₀ htp h2
      exact ⟨m, by exact_mod_cast h3⟩
    · rintro ⟨m, hm⟩
      refine ⟨m, ?_⟩
      have h2 : (n : ℝ) - (r : ℝ) = (p : ℝ) * (m : ℝ) := by exact_mod_cast hm
      rw [h2]
      field_simp [hpR] <;> ring
  -- the geometric sum: going once around the circle closes it up
  have hpt : (p : ℝ) * θ = 2 * Real.pi * ((n : ℝ) - (r : ℝ)) := by
    rw [hθ]
    field_simp [hpR] <;> ring
  have hzp : z ^ p = 1 := by
    rw [hpow p, ← Complex.ofReal_mul, hexp]
    refine ⟨(n : ℤ) - (r : ℤ), ?_⟩
    rw [hpt]
    norm_cast <;> ring
  have hsum : (∑ k ∈ Finset.range p, z ^ k) = if z = 1 then (p : ℂ) else 0 := by
    by_cases h : z = 1
    · rw [if_pos h, h]
      exact one_geom_sum p
    · rw [if_neg h]
      have hS : (∑ k ∈ Finset.range p, z ^ k) * (z - 1) = 0 := by
        rw [geom_sum_mul, hzp, sub_self]
      rcases mul_eq_zero.mp hS with h' | h'
      · exact h'
      · exact absurd h' (sub_ne_zero.mpr h)
  -- real parts commute with the sum, and the two cases give p and zero
  have hlin : (∑ k ∈ Finset.range p, z ^ k).re = ∑ k ∈ Finset.range p, (z ^ k).re := by
    simp
  have hmain : ∑ k ∈ Finset.range p, (z ^ k).re =
      (if n % p = r % p then (p : ℝ) else 0) := by
    by_cases h : n % p = r % p
    · have hc : z = 1 := hz1.mpr h
      rw [if_pos h, ← hlin, hsum, if_pos hc, Complex.natCast_re]
    · have hc : ¬ (z = 1) := fun hc' => h (hz1.mp hc')
      rw [if_neg h, ← hlin, hsum, if_neg hc, Complex.zero_re]
  exact (Finset.sum_congr rfl (fun k _ => (hcos k).symm)).trans hmain

private theorem count_roots (a p : ℕ) (hp : 0 < p) (s : Finset ℕ) :
    (((s.filter (fun n => p ∣ n ^ 2 + a)).card : ℕ) : ℝ) =
      ∑ r ∈ (Finset.range p).filter (fun r => p ∣ r ^ 2 + a),
        ∑ n ∈ s, if n % p = r % p then (1 : ℝ) else 0 := by
  rw [Finset.sum_comm]
  have hr (n : ℕ) : p ∣ (n % p) ^ 2 + a ↔ p ∣ n ^ 2 + a := by
    simp only [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, Nat.mod_mod]
  calc
    _ = ∑ n ∈ s, if p ∣ n ^ 2 + a then (1 : ℝ) else 0 := by simp [Finset.sum_filter]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hdiv : p ∣ n ^ 2 + a
      · rw [if_pos hdiv]
        rw [Finset.sum_eq_single (n % p)]
        · simp [Nat.mod_mod]
        · intro r hr hne
          have hrlt := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
          have : n % p ≠ r % p := by simpa [Nat.mod_eq_of_lt hrlt] using hne.symm
          simp [this]
        · intro hnot
          exfalso
          apply hnot
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hp), (hr n).mpr hdiv⟩
      · rw [if_neg hdiv]
        symm
        apply Finset.sum_eq_zero
        intro r hrmem
        have hrlt := Finset.mem_range.mp (Finset.mem_filter.mp hrmem).1
        have hrroot := (Finset.mem_filter.mp hrmem).2
        have hne : n % p ≠ r % p := by
          intro heq
          apply hdiv
          apply (hr n).mp
          simpa [heq, Nat.mod_eq_of_lt hrlt] using hrroot
        simp [hne]

private theorem frequency_decomposition (a p : ℕ) (hp : 0 < p) (s : Finset ℕ) :
    ((s.filter (fun n => p ∣ n ^ 2 + a)).card : ℝ) =
      ∑ k ∈ Finset.range p, (∑ r ∈ (Finset.range p).filter (fun r => p ∣ r ^ 2 + a),
        ∑ n ∈ s, Real.cos (2 * Real.pi * k * ((n : ℝ) - r) / p)) / p := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hortho := cosine_orthogonality
  dsimp only at hortho
  have hpoint (n r : ℕ) : (if n % p = r % p then (1 : ℝ) else 0) =
      (∑ k ∈ Finset.range p, Real.cos (2 * Real.pi * k * ((n : ℝ) - r) / p)) / p := by
    rw [hortho p n r hp]
    split_ifs <;> simp [hpR]
  rw [count_roots a p hp s]
  simp_rw [hpoint, ← Finset.sum_div]
  apply congrArg (fun z : ℝ => z / p)
  calc
    _ = ∑ r ∈ (Finset.range p).filter (fun r => p ∣ r ^ 2 + a),
        ∑ k ∈ Finset.range p, ∑ n ∈ s, Real.cos (2 * Real.pi * k * ((n : ℝ) - r) / p) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

private theorem split_frequencies (p : ℕ) (hp : 0 < p) (c : ℕ → ℝ) :
    (∑ k ∈ Finset.range p, c k) = c 0 +
      (∑ k ∈ (Finset.Ico 1 p).filter (fun k => min k (p-k) ≤ Nat.sqrt p), c k) +
      ∑ k ∈ (Finset.Ico 1 p).filter (fun k => Nat.sqrt p < min k (p-k)), c k := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range p) (fun k => k = 0) c
  have hzero : (Finset.range p).filter (fun k => k = 0) = {0} := by ext k; simp [hp]
  have hpositive : (Finset.range p).filter (fun k => ¬ k = 0) = Finset.Ico 1 p := by ext k; simp; omega
  rw [hzero, hpositive] at hsplit
  have hrest := Finset.sum_filter_add_sum_filter_not (Finset.Ico 1 p)
    (fun k => min k (p-k) ≤ Nat.sqrt p) c
  simp only [Finset.sum_singleton] at hsplit
  simp only [not_le] at hrest
  linarith

private theorem count_decomposition (a p : ℕ) (hp : 0 < p) (s : Finset ℕ) :
    let roots := (Finset.range p).filter (fun r => p ∣ r ^ 2 + a)
    let c := fun k : ℕ => (∑ r ∈ roots, ∑ n ∈ s, Real.cos (2 * Real.pi * k * ((n : ℝ) - r) / p)) / p
    ((s.filter (fun n => p ∣ n ^ 2 + a)).card : ℝ) =
      (s.card : ℝ) * (roots.card : ℝ) / p +
      (∑ k ∈ (Finset.Ico 1 p).filter (fun k => min k (p-k) ≤ Nat.sqrt p), c k) +
      ∑ k ∈ (Finset.Ico 1 p).filter (fun k => Nat.sqrt p < min k (p-k)), c k := by
  intro roots c
  have hzero : c 0 = (s.card : ℝ) * (roots.card : ℝ) / p := by
    dsimp only [c]
    simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, Real.cos_zero, Finset.sum_const_zero,
      Finset.sum_const, nsmul_eq_mul]
    ring
  calc
    _ = ∑ k ∈ Finset.range p, c k := frequency_decomposition a p hp s
    _ = _ := by rw [split_frequencies p hp c, hzero]

theorem PEqualNP.Outside.L_quadratic_primes_levent_root_system :
    let block := fun x : ℕ => Finset.Ioc x (2*x); let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a); let primes := fun x : ℕ => (Finset.Ioc x ((2*x)^2+1)).filter (fun p => Nat.Prime p ∧ p^100000 ≤ (2*x)^132301); let window := fun x p : ℕ => (block x).filter (fun n => p^100000 ≤ n^132301); let countHits := fun a x p : ℕ => ((window x p).filter (fun n => p ∣ n^2+a)).card; let inc := fun a x : ℕ => ∑ p ∈ primes x, (countHits a x p : ℝ) * Real.log (p : ℝ); let model := fun a x : ℕ => ∑ p ∈ primes x, ((window x p).card : ℝ) * ((roots a p).card : ℝ) / p * Real.log (p : ℝ); let angle := fun p k : ℕ => fun t : ℝ => 2 * Real.pi * k * t / p; let coef := fun a x p k : ℕ => (∑ r ∈ roots a p, ∑ n ∈ window x p, Real.cos (angle p k ((n : ℝ) - r))) / p; let freqs := fun (p : ℕ) (low : Bool) => (Finset.Ico 1 p).filter (fun k => if low then min k (p-k) ≤ Nat.sqrt p else Nat.sqrt p < min k (p-k)); let part := fun (a x p : ℕ) (low : Bool) => (∑ k ∈ freqs p low, coef a x p k) * Real.log (p : ℝ); let modes := fun (a x : ℕ) (low : Bool) => ∑ p ∈ primes x, part a x p low; ∀ x : ℕ, inc 1 x = model 1 x + modes 1 x true + modes 1 x false := by
  intro block roots primes window countHits inc model angle coef freqs part modes x
  change (∑ p ∈ primes x, (countHits 1 x p : ℝ) * Real.log (p : ℝ)) =
      (∑ p ∈ primes x, ((window x p).card : ℝ) * ((roots 1 p).card : ℝ) / p * Real.log (p : ℝ)) +
      (∑ p ∈ primes x, (∑ k ∈ freqs p true, coef 1 x p k) * Real.log (p : ℝ)) +
      ∑ p ∈ primes x, (∑ k ∈ freqs p false, coef 1 x p k) * Real.log (p : ℝ)
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hp_pos : 0 < p := (Finset.mem_filter.mp hp).2.1.pos
  have h := count_decomposition 1 p hp_pos (window x p)
  change (countHits 1 x p : ℝ) = ((window x p).card : ℝ) * ((roots 1 p).card : ℝ) / p +
      (∑ k ∈ freqs p true, coef 1 x p k) + ∑ k ∈ freqs p false, coef 1 x p k at h
  rw [h]
  ring
