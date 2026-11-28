import Mathlib

/-! The Chebyshev sum in one residue class is nondecreasing. Across one grid
cell the main term increases by at most 175000, independently of the modulus.
The last cell is clipped at the upper endpoint. Both numerical premises use
the same nodes, including both endpoints. Bennett, Martin, O'Bryant and
Rechnitzer, Explicit bounds for primes in arithmetic progressions, Theorem 1.9,
gives the tighter paper estimate 174500 throughout this particular window. -/

-- child 1 zh: 在每个模数的网格节点上，证明等差数列上的冯·曼戈尔特函数之和超过主项至多 180000。
-- child 1 en: At every modulus-dependent grid node, the progression sum exceeds its main term by at most 180000.
-- child 2 zh: 在同一网格节点上，证明等差数列上的冯·曼戈尔特函数之和低于主项至多 180000。
-- child 2 en: At every grid node, the progression sum falls below its main term by at most 180000.
theorem Conjectures.Cuts.Cut7a3cd005bede4837e4b5d9e3
    (hUpper : ∀ (q a j : ℕ), 3 ≤ q → q ≤ 105 → a < q → a.Coprime q →
      let u := min (10^10 : ℕ) (8000000000 + (175000 * q.totient) * j)
      (∑ k ∈ Finset.range (u + 1) with k % q = a % q, ArithmeticFunction.vonMangoldt k) -
        (u : ℝ) / q.totient ≤ 180000)
    (hLower : ∀ (q a j : ℕ), 3 ≤ q → q ≤ 105 → a < q → a.Coprime q →
      let u := min (10^10 : ℕ) (8000000000 + (175000 * q.totient) * j)
      (u : ℝ) / q.totient -
        (∑ k ∈ Finset.range (u + 1) with k % q = a % q, ArithmeticFunction.vonMangoldt k) ≤ 180000) :
    ∀ (x1 x2 x3 : ℕ), (3 : ℕ) ≤ x1 → x1 ≤ (105 : ℕ) → x2 < x1 → x2.Coprime x1 → (8000000000 : ℕ) ≤ x3 → x3 ≤ (10 : ℕ) ^ (10 : ℕ) → |∑ x10 ∈ Finset.range (x3 + (1 : ℕ)) with x10 % x1 = x2 % x1, ArithmeticFunction.vonMangoldt x10 - ↑x3 / ↑x1.totient| ≤ (4 : ℝ) * √↑x3 + Real.log ↑x3 := by
  intro q a n hq hqMax ha hcop hn hlast
  let d := 175000 * q.totient
  let grid (j : ℕ) := min (10^10 : ℕ) (8000000000 + d * j)
  let j := (n - 8000000000) / d
  have hphi : 0 < q.totient := Nat.totient_pos.mpr (by omega)
  have hd : 0 < d := Nat.mul_pos (by decide) hphi
  have hdiv : (n - 8000000000) % d + d * j = n - 8000000000 := Nat.mod_add_div _ _
  have hrem := Nat.mod_lt (n - 8000000000) hd
  have hbase : 8000000000 + d * j ≤ n := by omega
  have hj : grid j = 8000000000 + d * j := min_eq_right (hbase.trans hlast)
  have hleft : grid j ≤ n := by rwa [hj]
  have hstep : n ≤ grid j + d := by rw [hj]; omega
  have hright : n ≤ grid (j + 1) := by
    apply le_min hlast
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hstep' : grid (j + 1) ≤ n + d := by
    refine (min_le_right _ _).trans ?_
    rw [Nat.mul_add, Nat.mul_one]
    omega
  let psi (x : ℕ) : ℝ :=
    ∑ k ∈ Finset.range (x + 1) with k % q = a % q, ArithmeticFunction.vonMangoldt k
  have hmono : Monotone psi := by
    intro x y hxy
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset_filter _ (Finset.range_mono (Nat.succ_le_succ hxy))
    · intro k _ _
      exact ArithmeticFunction.vonMangoldt_nonneg
  have hphiR : (0 : ℝ) < q.totient := by exact_mod_cast hphi
  have hmain {x y : ℕ} (h : x ≤ y + d) :
      (x : ℝ) / q.totient ≤ (y : ℝ) / q.totient + 175000 := by
    change x ≤ y + 175000 * q.totient at h
    have hx : (x : ℝ) ≤ y + 175000 * (q.totient : ℝ) := by exact_mod_cast h
    calc
      _ ≤ ((y : ℝ) + 175000 * (q.totient : ℝ)) / q.totient :=
        div_le_div_of_nonneg_right hx hphiR.le
      _ = _ := by rw [add_div]; simp [hphiR.ne']
  have hup : psi (grid (j + 1)) - (grid (j + 1) : ℝ) / q.totient ≤ 180000 :=
    hUpper q a (j + 1) hq hqMax ha hcop
  have hlo : (grid j : ℝ) / q.totient - psi (grid j) ≤ 180000 :=
    hLower q a j hq hqMax ha hcop
  have hentire : |psi n - (n : ℝ) / q.totient| ≤ 355000 := by
    apply abs_le.mpr
    constructor
    · linarith only [hlo, hmono hleft, hmain hstep]
    · linarith only [hup, hmono hright, hmain hstep']
  refine hentire.trans ?_
  have hnR : (8000000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hroot : (89000 : ℝ) ≤ Real.sqrt n := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    linarith
  linarith only [hroot, Real.log_natCast_nonneg n]
