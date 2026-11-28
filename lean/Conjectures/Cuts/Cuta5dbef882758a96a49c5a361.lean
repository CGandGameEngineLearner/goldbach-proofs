import Mathlib

-- child 1 zh: 模 30 轮筛权在正共振次弧上的能量至多为 Cn/(log n)²。
-- child 1 en: Bound the masked energy of the mod-30 wheel by C n/(log n)^2.
-- child 2 zh: 对每个 d 整除 30，将截断在 k<n 的各剩余类指数和的掩膜能量相加，所得至多为 Cd n/(log n)²。
-- child 2 en: Sum the masked energies of the d residue classes cut off at k<n, uniformly for d dividing 30, with bound C d n/(log n)^2.
-- child 3 zh: 把长间距修正写成模 1、3、5、15 剩余类能量与轮筛能量的带符号组合，并对删去的短间距及对角项证明 O(n/(log n)²) 误差。
-- child 3 en: Approximate the long-lag correction by the signed residue and wheel energies with an O(n/(log n)^2) bound for truncated short lags and the diagonal.

theorem Conjectures.Cuts.Cuta5dbef882758a96a49c5a361
    (h₁ : by
  classical
  let Qn : ℕ → ℕ := fun n => (Nat.log 2 (n + 2)) ^ 2
  let arcs : ℕ → Set ℝ := fun n => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qn n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ (Qn n : ℝ) / ((q : ℝ) * (n : ℝ))}
  let L : ℕ → ℕ := fun n => max 1 (Nat.log 2 n / 2)
  let K : ℕ → ℝ → ℝ := fun n t => (∑ j ∈ Finset.range (L n), Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) / (L n : ℝ)
  let B : ℕ → Set ℝ := fun n => {t : ℝ | t ∉ arcs n ∧ (1 : ℝ) / 2 < K n t}
  let E := fun x : ℝ => Complex.exp (((2*Real.pi*x : ℝ):ℂ)*Complex.I)
  let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t =>
    ‖∑ k ∈ Finset.range (n+1), (a k : ℂ)*E ((k:ℝ)*t)‖^2)) (0:ℝ) 1 MeasureTheory.volume
  let model : ℕ → ℝ := fun k => if Nat.Coprime k 30 then (30 : ℝ) / 8 else 0
  exact ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ n ≥ N, |U n model| ≤ C*((n:ℝ)/(Real.log (n:ℝ))^2))
    (h₂ : by
  classical
  let Qn : ℕ → ℕ := fun n => (Nat.log 2 (n + 2)) ^ 2
  let arcs : ℕ → Set ℝ := fun n => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qn n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ (Qn n : ℝ) / ((q : ℝ) * (n : ℝ))}
  let L : ℕ → ℕ := fun n => max 1 (Nat.log 2 n / 2)
  let K : ℕ → ℝ → ℝ := fun n t => (∑ j ∈ Finset.range (L n), Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) / (L n : ℝ)
  let B : ℕ → Set ℝ := fun n => {t : ℝ | t ∉ arcs n ∧ (1 : ℝ) / 2 < K n t}
  let E := fun x : ℝ => Complex.exp (((2*Real.pi*x : ℝ):ℂ)*Complex.I)
  let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t =>
    ‖∑ k ∈ Finset.range (n+1), (a k : ℂ)*E ((k:ℝ)*t)‖^2)) (0:ℝ) 1 MeasureTheory.volume
  let D := fun n d : ℕ => ∑ r ∈ Finset.range d, U n (fun k => if k<n ∧ k%d=r then 1 else 0)
  exact ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ d : ℕ, d ∣ 30 → |D n d| ≤ (d:ℝ)*(C*((n:ℝ)/(Real.log (n:ℝ))^2)))
    (h₃ : by
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
  let E := fun x : ℝ => Complex.exp (((2*Real.pi*x : ℝ):ℂ)*Complex.I)
  let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t =>
    ‖∑ k ∈ Finset.range (n+1), (a k : ℂ)*E ((k:ℝ)*t)‖^2)) (0:ℝ) 1 MeasureTheory.volume
  let D := fun n d : ℕ => ∑ r ∈ Finset.range d, U n (fun k => if k<n ∧ k%d=r then 1 else 0)
  exact ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ n ≥ N, |Q n - ((15/32:ℝ)*(3*D n 1+3*D n 3+D n 5+D n 15)-U n model)| ≤ C*((n:ℝ)/(Real.log (n:ℝ))^2)) :
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
  obtain ⟨c,hc,C₀,hC⟩ := h₃
  refine ⟨a+15*b+c, by positivity, max 2 (max A₀ (max B₀ C₀)), le_max_left .., ?_⟩
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
  let E := fun x : ℝ => Complex.exp (((2*Real.pi*x : ℝ):ℂ)*Complex.I)
  let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t =>
    ‖∑ k ∈ Finset.range (n+1), (a k : ℂ)*E ((k:ℝ)*t)‖^2)) (0:ℝ) 1 MeasureTheory.volume
  let D := fun n d : ℕ => ∑ r ∈ Finset.range d, U n (fun k => if k<n ∧ k%d=r then 1 else 0)
  let t := ((n:ℝ)/(Real.log (n:ℝ))^2)
  have na : A₀ ≤ n := by omega
  have nb : B₀ ≤ n := by omega
  have nc : C₀ ≤ n := by omega
  have hw : |U n model| ≤ a*t := hA n na
  have hd (d : ℕ) (h : d ∣ 30) : |D n d| ≤ (d:ℝ)*(b*t) := hB n nb d h
  have he : |Q n - ((15/32:ℝ)*(3*D n 1+3*D n 3+D n 5+D n 15)-U n model)| ≤ c*t := hC n nc
  have h1 := abs_le.mp (hd 1 (by decide))
  have h3 := abs_le.mp (hd 3 (by decide))
  have h5 := abs_le.mp (hd 5 (by decide))
  have h15 := abs_le.mp (hd 15 (by decide))
  norm_num at h1 h3 h5 h15
  rcases abs_le.mp hw with ⟨hw₁,hw₂⟩
  rcases abs_le.mp he with ⟨he₁,he₂⟩
  change |Q n| ≤ (a+15*b+c)*(n:ℝ)/(Real.log (n:ℝ))^2
  rw [mul_div_assoc]
  change |Q n| ≤ (a+15*b+c)*t
  rw [abs_le]
  constructor <;> linarith [h1.1,h1.2,h3.1,h3.2,h5.1,h5.2,h15.1,h15.2]
