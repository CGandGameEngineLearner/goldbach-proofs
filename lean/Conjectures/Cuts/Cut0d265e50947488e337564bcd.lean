import Mathlib

-- child 1 zh: 在正共振次弧上，模 30 轮筛权的带符号长间距自相关绝对值为 O(n/(log n)²)。
-- child 1 en: Bound the absolute signed long-lag masked correlation of the mod-30 wheel by C n/(log n)^2.
-- child 2 zh: 对 d 整除 30，将截断于 k<n 的各剩余类的带符号长间距相关求和，绝对值至多为 Cd n/(log n)²。
-- child 2 en: Bound the aggregate signed masked long-lag correlation of the d residue classes cut off at k<n by C d n/(log n)^2, uniformly for divisors of 30.
-- child 3 zh: 对任何有限间距集和实权，精确地把模 30 均值项展开成模 1、3、5、15 的截断剩余类自相关。
-- child 3 en: For arbitrary finite lags and real test weights, resolve the weighted mod-30 mean exactly into the truncated residue-class correlations at moduli 1, 3, 5 and 15.

theorem Conjectures.Cuts.Cut0d265e50947488e337564bcd
    (h₁ : by
  classical
  let Qn : ℕ → ℕ := fun n => (Nat.log 2 (n + 2)) ^ 2
  let arcs : ℕ → Set ℝ := fun n => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qn n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ (Qn n : ℝ) / ((q : ℝ) * (n : ℝ))}
  let L : ℕ → ℕ := fun n => max 1 (Nat.log 2 n / 2)
  let K : ℕ → ℝ → ℝ := fun n t => (∑ j ∈ Finset.range (L n), Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) / (L n : ℝ)
  let B : ℕ → Set ℝ := fun n => {t : ℝ | t ∉ arcs n ∧ (1 : ℝ) / 2 < K n t}
  let V : ℕ → ℕ → ℝ := fun n h => intervalIntegral ((B n).indicator (fun t => Real.cos (2 * Real.pi * (h : ℝ) * t))) (0 : ℝ) 1 MeasureTheory.volume
  let A : ℕ → ℕ → (ℕ → ℝ) → ℝ := fun n h a => ∑ k ∈ Finset.range (n + 1 - h), a k * a (k + h)
  let model : ℕ → ℝ := fun k => if Nat.Coprime k 30 then (30 : ℝ) / 8 else 0
  let J := fun (n : ℕ) (a : ℕ → ℝ) => 2*∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h
  exact ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ n ≥ N, |J n model| ≤ C*((n:ℝ)/(Real.log (n:ℝ))^2))
    (h₂ : by
  classical
  let Qn : ℕ → ℕ := fun n => (Nat.log 2 (n + 2)) ^ 2
  let arcs : ℕ → Set ℝ := fun n => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qn n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ (Qn n : ℝ) / ((q : ℝ) * (n : ℝ))}
  let L : ℕ → ℕ := fun n => max 1 (Nat.log 2 n / 2)
  let K : ℕ → ℝ → ℝ := fun n t => (∑ j ∈ Finset.range (L n), Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) / (L n : ℝ)
  let B : ℕ → Set ℝ := fun n => {t : ℝ | t ∉ arcs n ∧ (1 : ℝ) / 2 < K n t}
  let V : ℕ → ℕ → ℝ := fun n h => intervalIntegral ((B n).indicator (fun t => Real.cos (2 * Real.pi * (h : ℝ) * t))) (0 : ℝ) 1 MeasureTheory.volume
  let A : ℕ → ℕ → (ℕ → ℝ) → ℝ := fun n h a => ∑ k ∈ Finset.range (n + 1 - h), a k * a (k + h)
  let J := fun (n : ℕ) (a : ℕ → ℝ) => 2*∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h
  let D := fun n d : ℕ => ∑ r ∈ Finset.range d, J n (fun k => if k<n ∧ k%d=r then 1 else 0)
  exact ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ d : ℕ, d ∣ 30 → |D n d| ≤ (d:ℝ)*(C*((n:ℝ)/(Real.log (n:ℝ))^2)))
    (h₃ : by
  classical
  let A : ℕ → ℕ → (ℕ → ℝ) → ℝ := fun n h a => ∑ k ∈ Finset.range (n + 1 - h), a k * a (k + h)
  let rho : ℕ → ℝ := fun h => (2 : ℝ) ^ (if 3 ∣ h then 1 else 0) * (3 * (if 5 ∣ h then (0 : ℝ) else 1) + 4 * (if 5 ∣ h then (1 : ℝ) else 0))
  exact ∀ (n : ℕ) (H : Finset ℕ) (v : ℕ → ℝ), (∀ h ∈ H, h ≤ n) →
    let R := fun d : ℕ => ∑ r ∈ Finset.range d, 2*∑ h ∈ H,
      A n h (fun k => if k<n ∧ k%d=r then 1 else 0) * v h
    2*(∑ h ∈ H, (((n:ℝ)-h)*((15:ℝ)/32)*rho h)*v h) =
      (15/32:ℝ)*(3*R 1+3*R 3+R 5+R 15)) :
(by
  classical
  let Qn : ℕ → ℕ := fun n => (Nat.log 2 (n + 2)) ^ 2
  let arcs : ℕ → Set ℝ := fun n => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qn n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ (Qn n : ℝ) / ((q : ℝ) * (n : ℝ))}
  let L : ℕ → ℕ := fun n => max 1 (Nat.log 2 n / 2)
  let K : ℕ → ℝ → ℝ := fun n t => (∑ j ∈ Finset.range (L n), Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) / (L n : ℝ)
  let B : ℕ → Set ℝ := fun n => {t : ℝ | t ∉ arcs n ∧ (1 : ℝ) / 2 < K n t}
  let V : ℕ → ℕ → ℝ := fun n h => intervalIntegral ((B n).indicator (fun t => Real.cos (2 * Real.pi * (h : ℝ) * t))) (0 : ℝ) 1 MeasureTheory.volume
  let A : ℕ → ℕ → (ℕ → ℝ) → ℝ := fun n h a => ∑ k ∈ Finset.range (n + 1 - h), a k * a (k + h)
  let model : ℕ → ℝ := fun k => if Nat.Coprime k 30 then (30 : ℝ) / 8 else 0
  let rho : ℕ → ℝ := fun h => (2 : ℝ) ^ (if 3 ∣ h then 1 else 0) * (3 * (if 5 ∣ h then (0 : ℝ) else 1) + 4 * (if 5 ∣ h then (1 : ℝ) else 0))
  let Q : ℕ → ℝ := fun n => 2 * (∑ h ∈ Finset.Icc ((L n) ^ 2 + 1) n, ((n - h : ℝ) * ((15 : ℝ) / 32) * rho h - A n h model) * V n h)
  exact ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → Even n → |Q n| ≤ C * (n : ℝ) / (Real.log (n : ℝ))^2) := by
  classical
  obtain ⟨a,ha,A₀,hA⟩ := h₁
  obtain ⟨b,hb,B₀,hB⟩ := h₂
  refine ⟨a+15*b, by positivity, max 2 (max A₀ B₀), le_max_left .., ?_⟩
  intro n hn _
  let Qn : ℕ → ℕ := fun n => (Nat.log 2 (n + 2)) ^ 2
  let arcs : ℕ → Set ℝ := fun n => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qn n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ (Qn n : ℝ) / ((q : ℝ) * (n : ℝ))}
  let L : ℕ → ℕ := fun n => max 1 (Nat.log 2 n / 2)
  let K : ℕ → ℝ → ℝ := fun n t => (∑ j ∈ Finset.range (L n), Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) / (L n : ℝ)
  let B : ℕ → Set ℝ := fun n => {t : ℝ | t ∉ arcs n ∧ (1 : ℝ) / 2 < K n t}
  let V : ℕ → ℕ → ℝ := fun n h => intervalIntegral ((B n).indicator (fun t => Real.cos (2 * Real.pi * (h : ℝ) * t))) (0 : ℝ) 1 MeasureTheory.volume
  let A : ℕ → ℕ → (ℕ → ℝ) → ℝ := fun n h a => ∑ k ∈ Finset.range (n + 1 - h), a k * a (k + h)
  let model : ℕ → ℝ := fun k => if Nat.Coprime k 30 then (30 : ℝ) / 8 else 0
  let rho : ℕ → ℝ := fun h => (2 : ℝ) ^ (if 3 ∣ h then 1 else 0) * (3 * (if 5 ∣ h then (0 : ℝ) else 1) + 4 * (if 5 ∣ h then (1 : ℝ) else 0))
  let Q : ℕ → ℝ := fun n => 2 * (∑ h ∈ Finset.Icc ((L n) ^ 2 + 1) n, ((n - h : ℝ) * ((15 : ℝ) / 32) * rho h - A n h model) * V n h)
  let J := fun (n : ℕ) (a : ℕ → ℝ) => 2*∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h
  let D := fun n d : ℕ => ∑ r ∈ Finset.range d, J n (fun k => if k<n ∧ k%d=r then 1 else 0)
  let t := ((n:ℝ)/(Real.log (n:ℝ))^2)
  have na : A₀ ≤ n := by omega
  have nb : B₀ ≤ n := by omega
  have hw : |J n model| ≤ a*t := hA n na
  have hd (d : ℕ) (h : d ∣ 30) : |D n d| ≤ (d:ℝ)*(b*t) := hB n nb d h
  let H := Finset.Icc ((L n)^2+1) n
  have eq := h₃ n H (V n) (fun h hh => (Finset.mem_Icc.mp hh).2)
  change 2*(∑ h ∈ H, (((n:ℝ)-h)*(15/32)*rho h)*V n h) = (15/32)*(3*D n 1+3*D n 3+D n 5+D n 15) at eq
  have he : Q n = (15/32:ℝ)*(3*D n 1+3*D n 3+D n 5+D n 15)-J n model := by
    rw [← eq]
    change 2*(∑ h ∈ H, (_-_)*V n h) = 2*(∑ h ∈ H, _)-2*(∑ h ∈ H, _)
    simp only [sub_mul, Finset.sum_sub_distrib, mul_sub]
  have h1 := abs_le.mp (hd 1 (by decide))
  have h3 := abs_le.mp (hd 3 (by decide))
  have h5 := abs_le.mp (hd 5 (by decide))
  have h15 := abs_le.mp (hd 15 (by decide))
  norm_num at h1 h3 h5 h15
  rcases abs_le.mp hw with ⟨hw₁,hw₂⟩
  change |Q n| ≤ (a+15*b)*(n:ℝ)/(Real.log (n:ℝ))^2
  rw [mul_div_assoc]
  change |Q n| ≤ (a+15*b)*t
  rw [he, abs_le]
  constructor <;> linarith [h1.1,h1.2,h3.1,h3.2,h5.1,h5.2,h15.1,h15.2]
