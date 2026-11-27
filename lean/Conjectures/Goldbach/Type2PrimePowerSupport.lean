import Mathlib

private theorem sqrt_sum (n B : ℕ) :
    (∑ i ∈ Finset.range B, ((n/(i+1)).sqrt:ℝ)) ≤ 2*Real.sqrt n*Real.sqrt B := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Finset.sum_range_succ]
    have s : 0 < Real.sqrt (B.succ:ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hdiv : (((n/(B+1)).sqrt:ℕ):ℝ) ≤ Real.sqrt n / Real.sqrt (B.succ:ℝ) := by
      rw [← Real.sqrt_div (Nat.cast_nonneg n)]
      exact Real.nat_sqrt_le_real_sqrt.trans (Real.sqrt_le_sqrt Nat.cast_div_le)
    have step : 1 / Real.sqrt (B.succ:ℝ) ≤ 2*(Real.sqrt (B.succ:ℝ)-Real.sqrt B) := by
      apply (div_le_iff₀ s).mpr
      have h1 := Real.sq_sqrt (Nat.cast_nonneg B.succ : (0:ℝ) ≤ B.succ)
      have h0 := Real.sq_sqrt (Nat.cast_nonneg B : (0:ℝ) ≤ B)
      push_cast at h1 ⊢
      nlinarith only [h1,h0,sq_nonneg (Real.sqrt ((B:ℝ)+1)-Real.sqrt B)]
    have h := mul_le_mul_of_nonneg_left step (Real.sqrt_nonneg n)
    rw [mul_one_div] at h
    linarith only [add_le_add ih (hdiv.trans h)]

theorem Conjectures.Goldbach.Type2PrimePowerSupport :
    ∀ n U B : ℕ, let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0;
    let coeff := fun (v : ℕ → ℝ) (m : ℕ) => ∑ a ∈ m.divisors.filter (fun a => U < a ∧ a ≤ B ∧ U < m / a), (∑ d ∈ a.divisors.filter (fun d => U < d), ((ArithmeticFunction.moebius d : ℤ) : ℝ)) * v (m / a);
    (((Finset.range (n + 1)).filter (fun m => coeff ArithmeticFunction.vonMangoldt m ≠ coeff w m)).card : ℝ) ≤ 2 * Real.sqrt n * Real.sqrt B * (Nat.log 2 n : ℝ) := by
  intro n U B w coeff
  classical
  let L := Nat.log 2 n
  let S (i : ℕ) := ((Finset.Icc 1 (n/(i+1)).sqrt) ×ˢ (Finset.Icc 1 L)).image
    (fun z : ℕ × ℕ => (i+1)*z.1^z.2)
  let T := (Finset.range (n+1)).filter (fun m => coeff ArithmeticFunction.vonMangoldt m ≠ coeff w m)
  have sub : T ⊆ (Finset.range B).biUnion S := by
    intro m hm
    obtain ⟨hm, hne⟩ := Finset.mem_filter.mp hm
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hex : ∃ a ∈ m.divisors.filter (fun a => U < a ∧ a ≤ B ∧ U < m/a),
        ArithmeticFunction.vonMangoldt (m/a) ≠ w (m/a) := by
      by_contra! hh
      apply hne
      apply Finset.sum_congr rfl
      intro a ha
      rw [hh a ha]
    obtain ⟨a, ha, hΔ⟩ := hex
    obtain ⟨hd,_,haB,_⟩ := Finset.mem_filter.mp ha
    have ha := Nat.pos_of_mem_divisors hd
    have hmul := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    have hnp : ¬ (m/a).Prime := by
      intro h
      exact hΔ (by simp [w,h,ArithmeticFunction.vonMangoldt_apply_prime h])
    have hΛ : ArithmeticFunction.vonMangoldt (m/a) ≠ 0 := by simpa [w,hnp] using hΔ
    obtain ⟨p,j,hp,hj,hpj⟩ := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
    have hp' := Nat.prime_iff.mpr hp
    have hj2 : 2 ≤ j := by
      by_contra! h
      have he : j = 1 := by omega
      rw [he,pow_one] at hpj
      exact hnp (hpj ▸ hp')
    have hqn : m/a ≤ n/a := Nat.div_le_div_right hmn
    have hpn : p^2 ≤ n/a := (Nat.pow_le_pow_right hp'.pos hj2).trans (hpj.trans_le hqn)
    have hpl := Nat.le_sqrt.mpr (by simpa [pow_two] using hpn)
    have hjl : j ≤ L := Nat.le_log_of_pow_le (by decide : 1 < 2)
      ((Nat.pow_le_pow_left hp'.two_le j).trans ((hpj.trans_le (Nat.div_le_self m a)).trans hmn))
    apply Finset.mem_biUnion.mpr
    refine ⟨a-1,Finset.mem_range.mpr (by omega),?_⟩
    have he : a-1+1 = a := by omega
    apply Finset.mem_image.mpr
    refine ⟨(p,j), Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hp'.one_le,by simpa [he] using hpl⟩,
      Finset.mem_Icc.mpr ⟨by omega,hjl⟩⟩,?_⟩
    simp only [he,hpj,hmul]
  have hcard (i : ℕ) : (S i).card ≤ (n/(i+1)).sqrt*L := by
    exact Finset.card_image_le.trans (by simp [Finset.card_product,Nat.card_Icc])
  have bound : T.card ≤ ∑ i ∈ Finset.range B, (n/(i+1)).sqrt*L :=
    ((Finset.card_le_card sub).trans Finset.card_biUnion_le).trans (Finset.sum_le_sum (fun i _ => hcard i))
  change (T.card:ℝ) ≤ _
  rw [← Finset.sum_mul] at bound
  have hh : (T.card:ℝ) ≤ (∑ i ∈ Finset.range B, ((n/(i+1)).sqrt:ℝ))*(L:ℝ) := by exact_mod_cast bound
  exact hh.trans (mul_le_mul_of_nonneg_right (sqrt_sum n B) (Nat.cast_nonneg L))
