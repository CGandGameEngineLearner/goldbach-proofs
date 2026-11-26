import Mathlib

theorem PEqualNP.Outside.L_goldbach_factor_band_unfold :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let Λ := ArithmeticFunction.vonMangoldt; ∀ (n U L R : ℕ) (t : ℝ), let M := fun a : ℕ => ∑ d ∈ (Nat.divisors a).filter (fun d => U < d), μ d; let T := fun m : ℕ => ∑ a ∈ (Nat.divisors m).filter (fun a => L < a ∧ a ≤ R ∧ U < m/a), M a * Λ (m/a); (∑ m ∈ Finset.range (n+1), (T m : ℂ) * E ((m:ℝ)*t)) = ∑ a ∈ Finset.Ioc L (min R n), ∑ b ∈ Finset.Ioc U (n/a), ((M a * Λ b : ℝ):ℂ) * E ((a*b:ℕ)*t) := by
  intro E μ Λ n U L R t M T
  have hT : ∀ m : ℕ, (T m : ℂ) = ∑ a ∈ (Nat.divisors m).filter (fun a => L < a ∧ a ≤ R ∧ U < m / a), ((M a * Λ (m / a) : ℝ) : ℂ) := by
    intro m
    dsimp only [T]
    rw [Complex.ofReal_sum]
  have hL : (∑ m ∈ Finset.range (n+1), (T m : ℂ) * E ((m:ℝ)*t))
      = ∑ p ∈ (Finset.range (n+1)).sigma (fun m => (Nat.divisors m).filter (fun a => L < a ∧ a ≤ R ∧ U < m / a)),
          ((M p.2 * Λ (p.1 / p.2) : ℝ) : ℂ) * E ((p.1 : ℝ) * t) := by
    rw [← Finset.sum_sigma' (Finset.range (n+1)) (fun m => (Nat.divisors m).filter (fun a => L < a ∧ a ≤ R ∧ U < m / a)) (fun m a => ((M a * Λ (m / a) : ℝ) : ℂ) * E ((m : ℝ) * t))]
    exact Finset.sum_congr rfl (fun m hm => by rw [hT m, Finset.sum_mul])
  have hR : (∑ a ∈ Finset.Ioc L (min R n), ∑ b ∈ Finset.Ioc U (n/a), ((M a * Λ b : ℝ):ℂ) * E ((a*b:ℕ)*t))
      = ∑ q ∈ (Finset.Ioc L (min R n)).sigma (fun a => Finset.Ioc U (n/a)),
          ((M q.1 * Λ q.2 : ℝ) : ℂ) * E ((q.1 * q.2 : ℕ) * t) := by
    rw [← Finset.sum_sigma' (Finset.Ioc L (min R n)) (fun a => Finset.Ioc U (n/a)) (fun a b => ((M a * Λ b : ℝ) : ℂ) * E ((a*b:ℕ)*t))]
  have hdiv : ∀ p ∈ (Finset.range (n+1)).sigma (fun m => (Nat.divisors m).filter (fun a => L < a ∧ a ≤ R ∧ U < m / a)), p.2 ∣ p.1 := by
    intro p hp
    obtain ⟨hmem, hmem2⟩ := Finset.mem_sigma.mp hp
    exact (Nat.mem_divisors.mp (Finset.mem_filter.mp hmem2).1).1
  have key : (∑ p ∈ (Finset.range (n+1)).sigma (fun m => (Nat.divisors m).filter (fun a => L < a ∧ a ≤ R ∧ U < m / a)),
        ((M p.2 * Λ (p.1 / p.2) : ℝ) : ℂ) * E ((p.1 : ℝ) * t))
      = ∑ q ∈ (Finset.Ioc L (min R n)).sigma (fun a => Finset.Ioc U (n/a)),
        ((M q.1 * Λ q.2 : ℝ) : ℂ) * E ((q.1 * q.2 : ℕ) * t) := by
    refine Finset.sum_bij' (fun p hp => (⟨p.2, p.1 / p.2⟩ : Sigma fun _ => ℕ))
      (fun q hq => (⟨q.1 * q.2, q.1⟩ : Sigma fun _ => ℕ)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨hmem, hmem2⟩ := Finset.mem_sigma.mp hp
      obtain ⟨hdivp, hcond⟩ := Finset.mem_filter.mp hmem2
      obtain ⟨hd, hm0⟩ := Nat.mem_divisors.mp hdivp
      obtain ⟨hL1, hR1, hU1⟩ := hcond
      have hmpos : 0 < p.1 := Nat.pos_of_ne_zero hm0
      have hle : p.2 ≤ p.1 := Nat.le_of_dvd hmpos hd
      have hmn : p.1 ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem)
      refine Finset.mem_sigma.mpr ⟨Finset.mem_Ioc.mpr ⟨hL1, le_min hR1 (le_trans hle hmn)⟩, ?_⟩
      exact Finset.mem_Ioc.mpr ⟨hU1, Nat.div_le_div_right hmn⟩
    · intro q hq
      obtain ⟨hmem, hmem2⟩ := Finset.mem_sigma.mp hq
      obtain ⟨hL1, hR1⟩ := Finset.mem_Ioc.mp hmem
      obtain ⟨hU1, hU2⟩ := Finset.mem_Ioc.mp hmem2
      have hq1pos : 0 < q.1 := by omega
      have hq2pos : 0 < q.2 := by omega
      have hpos : 0 < q.1 * q.2 := Nat.mul_pos hq1pos hq2pos
      refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
      · refine Finset.mem_range.mpr ?_
        have hle : q.2 * q.1 ≤ n := (Nat.le_div_iff_mul_le hq1pos).mp hU2
        have hle' : q.1 * q.2 ≤ n := by rw [mul_comm q.1 q.2]; exact hle
        exact Nat.lt_succ_iff.mpr hle'
      · refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_mul_right q.1 q.2, ne_of_gt hpos⟩, ?_⟩
        refine ⟨hL1, le_trans hR1 (min_le_left _ _), ?_⟩
        rw [mul_comm q.1 q.2, Nat.mul_div_left q.2 hq1pos]
        exact hU1
    · intro p hp
      have hd : p.2 ∣ p.1 := hdiv p hp
      have hmul : p.2 * (p.1 / p.2) = p.1 := Nat.mul_div_cancel' hd
      cases p with
      | mk m a => simp only [hmul]
    · intro q hq
      obtain ⟨hmem, hmem2⟩ := Finset.mem_sigma.mp hq
      have hq1pos : 0 < q.1 := by
        have := (Finset.mem_Ioc.mp hmem).1
        omega
      have hdivq : q.1 * q.2 / q.1 = q.2 := by
        rw [mul_comm q.1 q.2, Nat.mul_div_left q.2 hq1pos]
      cases q with
      | mk a b => simp only [hdivq]
    · intro p hp
      obtain ⟨hmem, hmem2⟩ := Finset.mem_sigma.mp hp
      have hd : p.2 ∣ p.1 := (Nat.mem_divisors.mp (Finset.mem_filter.mp hmem2).1).1
      have hmul : p.2 * (p.1 / p.2) = p.1 := Nat.mul_div_cancel' hd
      simp only [hmul]
  rw [hL, key]
  exact hR.symm
