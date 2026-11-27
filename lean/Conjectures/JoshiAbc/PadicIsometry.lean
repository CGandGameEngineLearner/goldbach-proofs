import Mathlib
open scoped BigOperators
open Filter

private lemma padic_norm_inv_nat_le (p n : ℕ) [Fact p.Prime] (hn : 0 < n) :
    ‖((n : Padic p)⁻¹)‖ ≤ (n:ℝ) := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hn0 : (n:Padic p) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [norm_inv, Padic.norm_eq_zpow_neg_valuation hn0, Padic.valuation_natCast]
  rw [zpow_neg, zpow_natCast, inv_inv]
  have hd : p ^ multiplicity p n ≤ n := Nat.le_of_dvd hn (pow_multiplicity_dvd p n)
  exact_mod_cast hd

private lemma padic_scale_le (p : ℕ) [Fact p.Prime] :
    ‖(if p=2 then (4:Padic p) else (p:Padic p))‖ ≤ (1/3:ℝ) := by
  by_cases hp : p = 2
  · subst p
    simp only [ite_true]
    have heq : (4:Padic 2) = (2:Padic 2)^2 := by norm_num
    have hnorm : ‖(2:Padic 2)‖ = (1/2:ℝ) := by simpa using (Padic.norm_p (p:=2))
    rw [heq, norm_pow, hnorm]
    norm_num
  · rw [if_neg hp, Padic.norm_p]
    have hp3 : (3:ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have h := (Fact.out : p.Prime).two_le; omega)
    have hp0 : (0:ℝ) < p := by linarith
    have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<3) hp3
    simpa [one_div] using h

private lemma succ_le_two_pow (k : ℕ) : k+1 ≤ 2^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hp : 1 ≤ 2^k := Nat.one_le_pow k 2 (by omega)
    rw [pow_succ]
    omega

private lemma scale_geo (p : ℕ) [Fact p.Prime] (k : ℕ) :
    ((k+1:ℕ):ℝ) * ‖(if p=2 then (4:Padic p) else (p:Padic p))‖^k ≤ (2/3:ℝ)^k := by
  have hc := padic_scale_le p
  have hk : ((k+1:ℕ):ℝ) ≤ (2:ℝ)^k := by exact_mod_cast succ_le_two_pow k
  have hn : 0 ≤ ‖(if p=2 then (4:Padic p) else (p:Padic p))‖^k := by positivity
  calc
    _ ≤ (2:ℝ)^k * (1/3:ℝ)^k := mul_le_mul hk (pow_le_pow_left₀ (norm_nonneg _) hc k) hn (by positivity)
    _ = (2/3:ℝ)^k := by rw [← mul_pow]; norm_num

private lemma term_bound (p : ℕ) [Fact p.Prime] (x : Padic p) (hx : ‖x‖ ≤ 1) (k : ℕ) :
    let c : Padic p := if p=2 then 4 else (p:Padic p)
    ‖(-1:Padic p)^k*(c*x)^(k+1)/((k+1:ℕ):Padic p)‖ ≤ ‖c*x‖ * (2/3:ℝ)^k := by
  dsimp only
  let c : Padic p := if p=2 then 4 else (p:Padic p)
  change ‖(-1:Padic p)^k*(c*x)^(k+1)/((k+1:ℕ):Padic p)‖ ≤ ‖c*x‖ * (2/3:ℝ)^k
  have hcx : ‖c*x‖ ≤ ‖c‖ := by rw [norm_mul]; nlinarith [norm_nonneg c, norm_nonneg x]
  have hinv := padic_norm_inv_nat_le p (k+1) (by omega)
  have hpow : ‖c*x‖^k ≤ ‖c‖^k := pow_le_pow_left₀ (norm_nonneg _) hcx k
  have hgeo := scale_geo p k
  change ((k+1:ℕ):ℝ) * ‖c‖^k ≤ (2/3:ℝ)^k at hgeo
  simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [div_eq_mul_inv, ← norm_inv, pow_succ]
  have hmid : (‖c‖*‖x‖)^k * ‖((k+1:ℕ):Padic p)⁻¹‖ ≤ ‖c‖^k * ((k+1:ℕ):ℝ) := by
    apply mul_le_mul _ hinv (norm_nonneg _) (by positivity)
    simpa only [norm_mul] using hpow
  have hfinal := mul_le_mul_of_nonneg_left hmid (mul_nonneg (norm_nonneg c) (norm_nonneg x))
  calc
    _ = (‖c‖*‖x‖) * ((‖c‖*‖x‖)^k * ‖((k+1:ℕ):Padic p)⁻¹‖) := by ring
    _ ≤ (‖c‖*‖x‖) * (‖c‖^k * ((k+1:ℕ):ℝ)) := hfinal
    _ = (‖c‖*‖x‖) * (((k+1:ℕ):ℝ) * ‖c‖^k) := by ring
    _ ≤ (‖c‖*‖x‖) * (2/3:ℝ)^k := mul_le_mul_of_nonneg_left hgeo (by positivity)

private theorem padic_scaled_log_isometry (p : ℕ) [Fact p.Prime] (x : Padic p) (hx : ‖x‖ ≤ 1) :
    let c : Padic p := if p=2 then 4 else (p:Padic p)
    ‖(∑' k : ℕ, (-1:Padic p)^k*(c*x)^(k+1)/((k+1:ℕ):Padic p))/c‖ = ‖x‖ := by
  dsimp only
  let c : Padic p := if p=2 then 4 else (p:Padic p)
  let f : ℕ → Padic p := fun k => (-1:Padic p)^k*(c*x)^(k+1)/((k+1:ℕ):Padic p)
  change ‖(∑' k : ℕ, f k)/c‖ = ‖x‖
  have hc0 : c ≠ 0 := by
    dsimp only [c]
    split_ifs with hp
    · norm_num
    · exact_mod_cast (Fact.out : p.Prime).ne_zero
  by_cases hx0 : x = 0
  · subst x
    simp [f]
  · have hcx0 : c*x ≠ 0 := mul_ne_zero hc0 hx0
    have hcxpos : 0 < ‖c*x‖ := norm_pos_iff.mpr hcx0
    have hgeom : Summable (fun k : ℕ => ‖c*x‖ * (2/3:ℝ)^k) :=
      (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 2/3) (by norm_num)).mul_left _
    have hs : Summable f := hgeom.of_norm_bounded (by intro k; exact term_bound p x hx k)
    have htail : ‖∑' k : ℕ, f (k+1)‖ ≤ ‖c*x‖ * (2/3:ℝ) := by
      apply IsUltrametricDist.norm_tsum_le_of_forall_le
      intro k
      have h := term_bound p x hx (k+1)
      change ‖f (k+1)‖ ≤ ‖c*x‖ * (2/3:ℝ)^(k+1) at h
      calc
        _ ≤ ‖c*x‖ * (2/3:ℝ)^(k+1) := h
        _ ≤ ‖c*x‖ * (2/3:ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          rw [pow_succ]
          have hk : (2/3:ℝ)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
          nlinarith
    have hlt : ‖∑' k : ℕ, f (k+1)‖ < ‖c*x‖ := by nlinarith
    have hsplit := hs.sum_add_tsum_nat_add 1
    have hf0 : f 0 = c*x := by simp [f]
    simp only [Finset.sum_range_one, hf0] at hsplit
    have hnorm : ‖∑' k : ℕ, f k‖ = ‖c*x‖ := by
      rw [← hsplit, Padic.add_eq_max_of_ne (ne_of_gt hlt), max_eq_left hlt.le]
    rw [norm_div, hnorm, norm_mul]
    field_simp


theorem Conjectures.JoshiAbc.PadicIsometry :
    ∀ (p : ℕ) [Fact p.Prime], let c : Padic p := if p=2 then 4 else (p:Padic p); let tau := fun (x : Padic p) => (∑' k : ℕ, (-1:Padic p)^k*(c*x)^(k+1)/((k+1:ℕ):Padic p))/c; ∀ x : Padic p, ‖x‖ ≤ 1 → ‖tau x‖ = ‖x‖ := by
  intro p hp
  dsimp only
  intro x hx
  exact padic_scaled_log_isometry p x hx
