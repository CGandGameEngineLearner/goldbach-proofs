import Mathlib

-- child 1 en: Bound the sum of squared deviations of Mangoldt masses from their mean within each residue class modulo p, uniformly for all initial segments X ≤ N.
-- child 1 zh: 对所有前缀 X ≤ N，控制冯·曼戈尔特权重在模 p 的每个剩余类内向模 p² 提升时的离均平方和。
-- child 2 en: Bound any exact rational Fourier coefficient at a reduced numerator modulo p² by p times the square root of the within-class variance.
-- child 2 zh: 对任意实权，用 p 倍类内方差的平方根控制既约分子、分母 p² 处的精确有理傅里叶系数。
-- child 3 en: Transfer a Fourier bound valid at every cutoff to a perturbed frequency, with loss at most 1 + 2πN|e|.
-- child 3 zh: 将所有前缀傅里叶和的一致上界转移到扰动频率，损失因子至多为 1 + 2πN|e|。

theorem Conjectures.Cuts.Cutfa97685df70e500953a725f5
    (hVar : let V := fun (w : ℕ → ℝ) (X p : ℕ) =>
      let row := fun (c j : ℕ) => ∑ m ∈ (Finset.range X).filter (fun (m : ℕ) => m % (p^2) = c + p*j), w m
      ∑ c ∈ Finset.range p, ∑ j ∈ Finset.range p,
        (row c j - (∑ k ∈ Finset.range p, row c k) / (p:ℝ))^2
    ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N p : ℕ, N₀ ≤ N → 2 ≤ N → p.Prime →
      (p^2)^2 ≤ N → N ≤ 4*(p^2)^2 → ∀ X ≤ N,
        V (fun m => ArithmeticFunction.vonMangoldt m) X p ≤ (N:ℝ)^(1+δ))
    (hOrth : let S := fun (w : ℕ → ℝ) (X : ℕ) (x : ℝ) => ∑ m ∈ Finset.range X, (w m : ℂ) * Complex.exp (((2 * Real.pi * (m : ℝ) * x : ℝ) : ℂ) * Complex.I)
    let V := fun (w : ℕ → ℝ) (X p : ℕ) =>
      let row := fun (c j : ℕ) => ∑ m ∈ (Finset.range X).filter (fun (m : ℕ) => m % (p^2) = c + p*j), w m
      ∑ c ∈ Finset.range p, ∑ j ∈ Finset.range p,
        (row c j - (∑ k ∈ Finset.range p, row c k) / (p:ℝ))^2
    ∀ (w : ℕ → ℝ) (X p : ℕ) (a : ℤ), p.Prime → a.natAbs.Coprime (p^2) →
      ‖S w X ((a:ℝ)/((p^2:ℕ):ℝ))‖ ≤ (p:ℝ)*Real.sqrt (V w X p))
    (hAbel : let S := fun (w : ℕ → ℝ) (X : ℕ) (x : ℝ) => ∑ m ∈ Finset.range X, (w m : ℂ) * Complex.exp (((2 * Real.pi * (m : ℝ) * x : ℝ) : ℂ) * Complex.I)
    ∀ (w : ℕ → ℝ) (N : ℕ) (x e B : ℝ), 0 ≤ B →
      (∀ X ≤ N, ‖S w X x‖ ≤ B) →
      ‖S w N (x+e)‖ ≤ (1 + 2*Real.pi*(N:ℝ)*|e|)*B) : (let S := fun (N : ℕ) (x : ℝ) => ∑ m ∈ Finset.range N, ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * Complex.exp (((2*Real.pi*(m : ℝ)*x : ℝ) : ℂ)*Complex.I); ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N p : ℕ, N₀ ≤ N → 2 ≤ N → Nat.Prime p → let q := p^2; q^2 ≤ N → N ≤ 4*q^2 → ∀ a : ℤ, Nat.Coprime a.natAbs q → ∀ e : ℝ, |e| ≤ 1/((q : ℝ)*Real.sqrt (N : ℝ)) → ‖S N ((a : ℝ)/(q : ℝ)+e)‖ ≤ (N : ℝ)^((3 : ℝ)/4+η)) := by
  have budget (η : ℝ) (hη : 0 < η) : ∃ T : ℕ, ∀ N p : ℕ, T ≤ N → 2 ≤ N →
      (p^2)^2 ≤ N → N ≤ 4*(p^2)^2 → ∀ e : ℝ,
      |e| ≤ 1/(((p^2 : ℕ):ℝ)*Real.sqrt (N:ℝ)) →
      (1+2*Real.pi*(N:ℝ)*|e|)*(p:ℝ)*Real.sqrt ((N:ℝ)^(1+η)) ≤
        (N:ℝ)^((3:ℝ)/4+η) := by
    have grows : Filter.Tendsto (fun n : ℕ => (n:ℝ)^(η/2)) Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop (show 0 < η/2 by linarith)).comp tendsto_natCast_atTop_atTop
    obtain ⟨T,hT⟩ := Filter.eventually_atTop.mp (grows.eventually_ge_atTop (1+4*Real.pi))
    refine ⟨T,?_⟩
    intro N p hN hN₂ hlo hhi e he
    have npos : 0 < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
    have ppos : 0 < (p:ℝ) := by
      exact_mod_cast (show 0 < p by by_contra! hp; simp [Nat.eq_zero_of_le_zero hp] at hhi; omega)
    have low : (p:ℝ)^4 ≤ N := by
      exact_mod_cast (show p^4 ≤ N by simpa only [← pow_mul] using hlo)
    have high : (N:ℝ) ≤ 4*((p:ℝ)^2)^2 := by exact_mod_cast hhi
    have root : Real.sqrt (N:ℝ) ≤ 2*(p:ℝ)^2 :=
      (Real.sqrt_le_iff).mpr ⟨by positivity, by nlinarith only [high]⟩
    push_cast at he
    have perturb := (le_div_iff₀ (show 0 < (p:ℝ)^2*Real.sqrt (N:ℝ) by positivity)).mp he
    have phase : (N:ℝ)*|e| ≤ 2 := by
      calc
        _ = Real.sqrt (N:ℝ)*(Real.sqrt (N:ℝ)*|e|) := by
          rw [← mul_assoc, Real.mul_self_sqrt npos.le]
        _ ≤ (2*(p:ℝ)^2)*(Real.sqrt (N:ℝ)*|e|) :=
          mul_le_mul_of_nonneg_right root (by positivity)
        _ ≤ 2 := by linarith only [perturb]
    have pref : 1+2*Real.pi*(N:ℝ)*|e| ≤ (N:ℝ)^(η/2) := by
      refine le_trans ?_ (hT N hN)
      linarith only [mul_le_mul_of_nonneg_left phase (show 0 ≤ 2*Real.pi by positivity)]
    have pbound : (p:ℝ) ≤ (N:ℝ)^(1/4:ℝ) := by
      rw [one_div, Real.le_rpow_inv_iff_of_pos ppos.le npos.le (by norm_num)]
      simpa using low
    calc
      _ ≤ (N:ℝ)^(η/2)*(N:ℝ)^(1/4:ℝ)*Real.sqrt ((N:ℝ)^(1+η)) := by gcongr
      _ = _ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul npos.le, ← Real.rpow_add npos, ← Real.rpow_add npos]
        congr 1
        ring
  classical
  intro S η hη
  obtain ⟨N₁, h₁⟩ := hVar η hη
  obtain ⟨N₂, h₂⟩ := budget η hη
  refine ⟨max N₁ N₂, ?_⟩
  intro N p hN hN2 hp q hlo hhi a ha e he
  have hvar := h₁ N p ((le_max_left _ _).trans hN) hN2 hp hlo hhi
  let V (X : ℕ) :=
    let row := fun (c j : ℕ) => ∑ m ∈ (Finset.range X).filter (fun (m : ℕ) => m % (p^2) = c+p*j),
      ArithmeticFunction.vonMangoldt m
    ∑ c ∈ Finset.range p, ∑ j ∈ Finset.range p,
      (row c j - (∑ k ∈ Finset.range p, row c k) / (p:ℝ))^2
  let B := (p:ℝ) * Real.sqrt ((N:ℝ)^(1+η))
  have hpartial (X : ℕ) (hX : X ≤ N) : ‖S X ((a:ℝ)/(q:ℝ))‖ ≤ B := by
    have hj : ‖S X ((a:ℝ)/(q:ℝ))‖ ≤ (p:ℝ)*Real.sqrt (V X) :=
      hOrth (fun m => ArithmeticFunction.vonMangoldt m) X p a hp ha
    exact hj.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hvar X hX)) (by positivity))
  have step := hAbel (fun m => ArithmeticFunction.vonMangoldt m) N ((a:ℝ)/(q:ℝ)) e B
    (by dsimp only [B]; positivity) hpartial
  apply step.trans
  change (1+2*Real.pi*(N:ℝ)*|e|) * ((p:ℝ)*Real.sqrt ((N:ℝ)^(1+η))) ≤ _
  rw [← mul_assoc]
  exact h₂ N p ((le_max_right _ _).trans hN) hN2 hlo hhi e he
