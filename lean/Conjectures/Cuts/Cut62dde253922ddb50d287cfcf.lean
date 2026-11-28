import Mathlib

-- child 1 en: For arbitrary real weights, the squared deviations among the p lifts are exactly the squared residue masses at modulus p² minus one pth of those at modulus p.
-- child 1 zh: 对任意实权，模 p 类内向模 p² 提升的离均平方和等于两级剩余类质量平方和之差，其中模 p 项乘以 1/p。
-- child 2 en: Express the sum of squared residue masses as the diagonal sum of squares plus twice the sum of correlations at positive shifts divisible by the modulus.
-- child 2 zh: 将剩余类质量平方和写成对角平方和，加上模数正倍数位移处相关和的两倍。
-- child 3 en: Bound the signed difference of the Mangoldt correlations at positive p²-multiple shifts and the p-multiple average, uniformly at every permitted cutoff.
-- child 3 zh: 对每个允许的截断点，控制冯·曼戈尔特权重在 p² 正倍数位移与 p 正倍数位移平均之间的有符号相关差。

theorem Conjectures.Cuts.Cut62dde253922ddb50d287cfcf
    (hLayers : let V := fun (w : ℕ → ℝ) (X p : ℕ) =>
      let row := fun (c j : ℕ) => ∑ m ∈ (Finset.range X).filter (fun (m : ℕ) => m % (p^2) = c+p*j), w m
      ∑ c ∈ Finset.range p, ∑ j ∈ Finset.range p,
        (row c j - (∑ k ∈ Finset.range p, row c k)/(p:ℝ))^2
    let A := fun (w : ℕ → ℝ) (X d : ℕ) =>
      ∑ c ∈ Finset.range d, (∑ m ∈ (Finset.range X).filter (fun (m : ℕ) => m % d = c), w m)^2
    ∀ (w : ℕ → ℝ) (X p : ℕ), 0 < p → V w X p = A w X (p^2) - A w X p/(p:ℝ))
    (hLags : let A := fun (w : ℕ → ℝ) (X d : ℕ) =>
      ∑ c ∈ Finset.range d, (∑ m ∈ (Finset.range X).filter (fun (m : ℕ) => m % d = c), w m)^2
    let G := fun (w : ℕ → ℝ) (X d : ℕ) =>
      ∑ j ∈ Finset.Icc 1 ((X-1)/d), ∑ m ∈ Finset.range (X-d*j), w m * w (m+d*j)
    ∀ (w : ℕ → ℝ) (X d : ℕ), 0 < d →
      A w X d = (∑ m ∈ Finset.range X, (w m)^2) + 2*G w X d)
    (hSigned : let G := fun (w : ℕ → ℝ) (X d : ℕ) =>
      ∑ j ∈ Finset.Icc 1 ((X-1)/d), ∑ m ∈ Finset.range (X-d*j), w m * w (m+d*j)
    ∀ δ : ℝ, 0 < δ → ∃ T : ℕ, ∀ N p : ℕ, T ≤ N → 2 ≤ N → p.Prime →
      (p^2)^2 ≤ N → N ≤ 4*(p^2)^2 → ∀ X ≤ N,
      G (fun m => ArithmeticFunction.vonMangoldt m) X (p^2) -
      G (fun m => ArithmeticFunction.vonMangoldt m) X p / (p:ℝ) ≤ (N:ℝ)^(1+δ)) : (have x1 : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun (x1 : ℕ → ℝ) (x2 x3 : ℕ) =>   have x4 : ℕ → ℕ → ℝ := fun (x4 x5 : ℕ) => ∑ x6 ∈ Finset.range x2 with x6 % x3 ^ (2 : ℕ) = x4 + x3 * x5, x1 x6;   ∑ x5 ∈ Finset.range x3, ∑ x6 ∈ Finset.range x3, (x4 x5 x6 - (∑ x7 ∈ Finset.range x3, x4 x5 x7) / ↑x3) ^ (2 : ℕ); ∀ (x2 : ℝ), (0 : ℝ) < x2 → ∃ (x4 : ℕ), ∀ (x5 x6 : ℕ), x4 ≤ x5 → (2 : ℕ) ≤ x5 → Nat.Prime x6 → (x6 ^ (2 : ℕ)) ^ (2 : ℕ) ≤ x5 → x5 ≤ (4 : ℕ) * (x6 ^ (2 : ℕ)) ^ (2 : ℕ) → ∀ x12 ≤ x5, x1 (fun (x14 : ℕ) => ArithmeticFunction.vonMangoldt x14) x12 x6 ≤ ↑x5 ^ ((1 : ℝ) + x2)) := by
  have diag_bound (δ : ℝ) (hδ : 0 < δ) : ∃ T : ℕ, ∀ N : ℕ, T ≤ N → 2 ≤ N →
      ∀ X ≤ N, (∑ m ∈ Finset.range X, (ArithmeticFunction.vonMangoldt m)^2) ≤
        (N:ℝ)^(1+δ) := by
    have hl : ∀ᶠ n : ℕ in Filter.atTop, ‖Real.log (n:ℝ)‖ ≤ 1 * ‖(n:ℝ)^(δ/2)‖ :=
      tendsto_natCast_atTop_atTop.eventually
        ((isLittleO_log_rpow_atTop (show 0 < δ/2 by linarith)).bound zero_lt_one)
    obtain ⟨T,hT⟩ := Filter.eventually_atTop.mp hl
    refine ⟨T,?_⟩
    intro N hTN hN X hX
    have npos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have none : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have hlog : Real.log (N:ℝ) ≤ (N:ℝ)^(δ/2) := by
      have h := hT N hTN
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg none),
        abs_of_nonneg (Real.rpow_nonneg npos.le _), one_mul] using h
    have term (m : ℕ) (hm : m ∈ Finset.range X) :
        ArithmeticFunction.vonMangoldt m ≤ (N:ℝ)^(δ/2) := by
      rcases Nat.eq_zero_or_pos m with rfl|hm'
      · simpa using (Real.rpow_nonneg npos.le (δ/2))
      · exact ArithmeticFunction.vonMangoldt_le_log.trans
          ((Real.log_le_log (by exact_mod_cast hm') (by exact_mod_cast (Finset.mem_range.mp hm).le.trans hX)).trans hlog)
    calc
      _ ≤ ∑ _m ∈ Finset.range X, ((N:ℝ)^(δ/2))^2 :=
        Finset.sum_le_sum fun m hm => pow_le_pow_left₀ ArithmeticFunction.vonMangoldt_nonneg (term m hm) 2
      _ = (X:ℝ)*((N:ℝ)^(δ/2))^2 := by simp
      _ ≤ (N:ℝ)*((N:ℝ)^(δ/2))^2 := mul_le_mul_of_nonneg_right (by exact_mod_cast hX) (sq_nonneg _)
      _ = _ := by
        rw [← Real.rpow_natCast ((N:ℝ)^(δ/2)) 2, ← Real.rpow_mul npos.le, Real.rpow_add npos, Real.rpow_one]
        norm_num
  have absorb (δ : ℝ) (hδ : 0 < δ) : ∃ T : ℕ, ∀ N : ℕ, T ≤ N → 2 ≤ N →
      (N:ℝ)^(1+δ/2) + 2*(N:ℝ)^(1+δ/2) ≤ (N:ℝ)^(1+δ) := by
    have grows : Filter.Tendsto (fun n : ℕ => (n:ℝ)^(δ/2)) Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop (show 0 < δ/2 by linarith)).comp tendsto_natCast_atTop_atTop
    obtain ⟨T,hT⟩ := Filter.eventually_atTop.mp (grows.eventually_ge_atTop 3)
    refine ⟨T,fun N ht hN => ?_⟩
    have hn : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    calc
      _ = (N:ℝ)^(1+δ/2)*3 := by ring
      _ ≤ (N:ℝ)^(1+δ/2)*(N:ℝ)^(δ/2) :=
        mul_le_mul_of_nonneg_left (hT N ht) (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  intro V η hη
  have hhalf : 0 < η/2 := by linarith
  obtain ⟨T₁,hS⟩ := hSigned (η/2) hhalf
  obtain ⟨T₂,hD⟩ := diag_bound (η/2) hhalf
  obtain ⟨T₃,hA⟩ := absorb η hη
  refine ⟨max (max T₁ T₂) T₃, ?_⟩
  intro N p hN hN2 hp hlo hhi X hX
  have t₁ : T₁ ≤ N := (le_max_left T₁ T₂).trans ((le_max_left _ _).trans hN)
  have t₂ : T₂ ≤ N := (le_max_right T₁ T₂).trans ((le_max_left _ _).trans hN)
  have t₃ : T₃ ≤ N := (le_max_right _ _).trans hN
  let w : ℕ → ℝ := fun m => ArithmeticFunction.vonMangoldt m
  let D := ∑ m ∈ Finset.range X, (w m)^2
  let A (d : ℕ) := ∑ c ∈ Finset.range d, (∑ m ∈ (Finset.range X).filter (fun m : ℕ => m % d = c), w m)^2
  let G (d : ℕ) := ∑ j ∈ Finset.Icc 1 ((X-1)/d), ∑ m ∈ Finset.range (X-d*j), w m * w (m+d*j)
  let Q := (N:ℝ)^(1+η/2)
  have layers : V w X p = A (p^2) - A p/(p:ℝ) := hLayers w X p hp.pos
  have narrow : A (p^2) = D + 2*G (p^2) := hLags w X (p^2) (pow_pos hp.pos _)
  have wide : A p = D + 2*G p := hLags w X p hp.pos
  have hsig : G (p^2)-G p/(p:ℝ) ≤ Q := hS N p t₁ hN2 hp hlo hhi X hX
  have hd : D ≤ Q := hD N t₂ hN2 X hX
  have hd0 : 0 ≤ D := Finset.sum_nonneg fun m _ => sq_nonneg _
  change V w X p ≤ _
  rw [layers,narrow,wide,add_div,mul_div_assoc]
  calc
    _ ≤ Q + 2*Q := by linarith only [hsig,hd,div_nonneg hd0 (Nat.cast_nonneg p)]
    _ ≤ _ := hA N t₃ hN2
