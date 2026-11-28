import Mathlib

set_option maxRecDepth 4096
set_option exponentiation.threshold 2000

namespace DyadicFlipEntropy

private def weight (n k : ℕ) := 17^k * 183^(n-k) * n.choose k

private theorem adjacent (n k : ℕ) (hk : k<n) :
    weight n (k+1)*(183*(k+1)) = weight n k*(17*(n-k)) := by
  have he : n-k = n-(k+1)+1 := by omega
  unfold weight
  calc
    _ = 17^k * 17 * (183^(n-(k+1))*183) * (n.choose (k+1)*(k+1)) := by rw [pow_succ]; ring
    _ = _ := by rw [Nat.choose_succ_right_eq, ← pow_succ 183, ← he]; ring

private theorem maximal (t k : ℕ) (hk : k ≤ 1000*t) :
    weight (1000*t) k ≤ weight (1000*t) (85*t) := by
  let n := 1000*t
  let m := 85*t
  have inc (j : ℕ) (hj : j < m) : weight n j ≤ weight n (j+1) := by
    have jn : j<n := by dsimp [n,m] at *; omega
    have ratio : 183*(j+1) ≤ 17*(n-j) := by dsimp [n,m] at *; omega
    apply le_of_mul_le_mul_right (a:=183*(j+1)) _ (by positivity)
    rw [adjacent n j jn]
    exact Nat.mul_le_mul_left _ ratio
  have dec (j : ℕ) (hj : m≤j) (jn : j<n) : weight n (j+1) ≤ weight n j := by
    have ratio : 17*(n-j) ≤ 183*(j+1) := by dsimp [n,m] at *; omega
    apply le_of_mul_le_mul_right (a:=183*(j+1)) _ (by positivity)
    rw [adjacent n j jn]
    exact Nat.mul_le_mul_left _ ratio
  change weight n k ≤ weight n m
  by_cases km : k≤ m
  · have climb : ∀ d j : ℕ, j+d=m → weight n j ≤ weight n m := by
      intro d
      induction d with
      | zero => intro j h; simpa using le_of_eq (congrArg (weight n) (by simpa using h : j=m))
      | succ d ih =>
        intro j hj
        exact (inc j (by omega)).trans (ih (j+1) (by omega))
    exact climb (m-k) k (by omega)
  · have descend : ∀ d : ℕ, m+d ≤ n → weight n (m+d) ≤ weight n m := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
        intro hj
        exact (dec (m+d) (by omega) (by omega)).trans (ih (by omega))
    have e : m+(k-m)=k := by omega
    have hlim : m+(k-m) ≤ n := by simpa only [e] using hk
    simpa only [e] using descend (k-m) hlim

end DyadicFlipEntropy

open DyadicFlipEntropy in
theorem Conjectures.Cuts.Taskb02f1cb99d942089048bdeec :
    ∀ t : ℕ, 2^(419*t) ≤ (1000*t+1)*(1000*t).choose (85*t) := by
  intro t
  have total : 200^(1000*t) ≤ (1000*t+1)*weight (1000*t) (85*t) := by
    calc
      _ = ∑ j ∈ Finset.range (1000*t+1), weight (1000*t) j := by
        simpa [weight] using (add_pow (17:ℕ) 183 (1000*t))
      _ ≤ ∑ _j ∈ Finset.range (1000*t+1), weight (1000*t) (85*t) :=
        Finset.sum_le_sum (fun j hj => maximal t j (by have := Finset.mem_range.mp hj; omega))
      _ = _ := by simp
  have num : (2:ℕ)^419 * (17^85*183^915) ≤ 200^1000 := by decide
  have est := (Nat.pow_le_pow_left num t).trans (by simpa only [pow_mul] using total)
  have p : 0 < (17^85 * 183^915 : ℕ)^t := by positivity
  apply le_of_mul_le_mul_right (a:=(17^85 * 183^915 : ℕ)^t) _ p
  have sub : 1000*t-85*t = 915*t := by omega
  unfold weight at est
  rw [sub] at est
  simpa only [mul_pow, ← pow_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using est
