import Mathlib
import Conjectures.Goldbach.DynShiftFactorMean

namespace DynBlockCollision

open Finset

noncomputable section

/-- The number of targets in the block reached by both steps. -/
private def pairs (A : Finset ℕ) (p q : ℕ) : ℝ :=
  ((A.filter (fun n => p ≤ n ∧ Nat.Prime (n-p) ∧ q ≤ n ∧ Nat.Prime (n-q))).card : ℝ)

private theorem count_eq_sum (S : Finset ℕ) (r : ℕ → Prop) [DecidablePred r] :
    ((S.filter r).card : ℝ) = ∑ n ∈ S, if r n then (1:ℝ) else 0 := by
  simp

private theorem pairs_symm (A : Finset ℕ) (p q : ℕ) :
    pairs A p q = pairs A q p := by
  unfold pairs
  congr 2
  ext n
  simp only [mem_filter]
  tauto

private theorem square_eq_pairs (A P : Finset ℕ) :
    (∑ n ∈ A, ((P.filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card:ℝ)^2) =
      ∑ p ∈ P, ∑ q ∈ P, pairs A p q := by
  let v (n p : ℕ) := if p ≤ n ∧ Nat.Prime (n-p) then (1:ℝ) else 0
  have hcount (n : ℕ) :
      ((P.filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card:ℝ) =
        ∑ p ∈ P, v n p :=
    count_eq_sum _ _
  have hpair (p q : ℕ) : (∑ n ∈ A, v n p * v n q) = pairs A p q := by
    unfold pairs
    rw [count_eq_sum]
    apply sum_congr rfl
    intro n _
    by_cases hp : p ≤ n ∧ Nat.Prime (n-p) <;> by_cases hq : q ≤ n ∧ Nat.Prime (n-q) <;>
      simp [v, hp, hq]
  calc
    _ = ∑ n ∈ A, ∑ p ∈ P, ∑ q ∈ P, v n p * v n q := by
      simp only [pow_two, hcount, sum_mul]
      apply sum_congr rfl
      intro n _
      apply sum_congr rfl
      intro p _
      rw [mul_sum]
    _ = ∑ p ∈ P, ∑ q ∈ P, ∑ n ∈ A, v n p * v n q := by
      rw [sum_comm]
      apply sum_congr rfl
      intro p _
      exact sum_comm
    _ = _ := by simp only [hpair]

private theorem split_pairs (A P : Finset ℕ) :
    (∑ p ∈ P, ∑ q ∈ P, pairs A p q) =
      (∑ p ∈ P, pairs A p p) + 2 * ∑ p ∈ P, ∑ q ∈ P.filter (fun q => p < q),
        pairs A p q := by
  have hsplit (p : ℕ) (hp : p ∈ P) :
      (∑ q ∈ P, pairs A p q) =
        pairs A p p + (∑ q ∈ P.filter (fun q => p < q), pairs A p q) +
          ∑ q ∈ P.filter (fun q => q < p), pairs A p q := by
    have hunion : P.filter (fun q => p < q) ∪ P.filter (fun q => q < p) = P.erase p := by
      ext q
      simp only [mem_union, mem_filter, mem_erase]
      by_cases hq : q ∈ P <;> simp [hq]
      omega
    have hdisj : Disjoint (P.filter (fun q => p < q)) (P.filter (fun q => q < p)) := by
      rw [disjoint_left]
      intro q hq hq'
      exact (lt_asymm (mem_filter.mp hq).2 (mem_filter.mp hq').2).elim
    rw [← sum_erase_add _ _ hp, ← hunion, sum_union hdisj]
    ring
  have hswap :
      (∑ p ∈ P, ∑ q ∈ P.filter (fun q => q < p), pairs A p q) =
        ∑ p ∈ P, ∑ q ∈ P.filter (fun q => p < q), pairs A p q := by
    simp only [sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro p _
    apply sum_congr rfl
    intro q _
    rw [pairs_symm A q p]
  rw [sum_congr rfl hsplit, sum_add_distrib, sum_add_distrib, hswap]
  ring

/-- Expand the squared counts into diagonal and strictly ordered pairs, and
bound each diagonal count by the block cardinality. -/
private theorem square_sum_le (A P : Finset ℕ) :
    (∑ n ∈ A, ((P.filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card:ℝ)^2) ≤
      (A.card:ℝ)*(P.card:ℝ) + 2 * ∑ p ∈ P, ∑ q ∈ P.filter (fun q => p < q),
        pairs A p q := by
  rw [square_eq_pairs, split_pairs]
  refine add_le_add ?_ le_rfl
  calc
    (∑ p ∈ P, pairs A p p) ≤ ∑ _p ∈ P, (A.card:ℝ) :=
      sum_le_sum fun p _ => by
        unfold pairs
        exact_mod_cast card_filter_le _ _
    _ = _ := by rw [sum_const, nsmul_eq_mul, mul_comm]

end
end DynBlockCollision

namespace DynBlockCollision

open Filter

/-- The square-root prime cutoff and the block length have logarithms
comparable to that of the ambient scale. -/
private theorem scales (A : ℕ) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀,
      let s := X.sqrt
      let W := s * s.sqrt
      A ≤ s ∧ 3 ≤ s ∧ 0 < Real.log (s : ℝ) ∧ 0 < Real.log (W : ℝ) ∧
        Real.log (X : ℝ) ≤ 3 * Real.log (s : ℝ) ∧
        Real.log (X : ℝ) ≤ 3 * Real.log (W : ℝ) ∧
        ((s + 1 : ℕ) : ℝ) ≤ (X : ℝ) / (Real.log (X : ℝ)) ^ 4 := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (4 : ℝ)
    (show (0 : ℝ) < 1 / 2 by norm_num)).bound
      (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmall)
  refine ⟨max N ((max 3 A)^2), ?_⟩
  intro X hX
  dsimp only
  let s := X.sqrt
  let W := s * s.sqrt
  have hs : max 3 A ≤ s := Nat.le_sqrt'.mpr ((le_max_right ..).trans hX)
  have hs3 : 3 ≤ s := (le_max_left ..).trans hs
  have hA : A ≤ s := (le_max_right ..).trans hs
  have hW : s ≤ W := Nat.le_mul_of_pos_right _ (Nat.sqrt_pos.mpr (by omega))
  have hX1 : 1 < X := lt_of_lt_of_le (by omega : 1 < s) (Nat.sqrt_le_self X)
  have hX1r : (1 : ℝ) < X := by exact_mod_cast hX1
  have hsr3 : (3 : ℝ) ≤ s := by exact_mod_cast hs3
  have hsr0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hWr : (s : ℝ) ≤ W := by exact_mod_cast hW
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos hX1r
  have hlogs : 0 < Real.log (s : ℝ) := Real.log_pos (by linarith)
  have hlogW : 0 < Real.log (W : ℝ) := Real.log_pos (by linarith)
  have hXle : (X : ℝ) ≤ ((s : ℝ) + 1)^2 := by
    exact_mod_cast (Nat.lt_succ_sqrt' X).le
  have hcube : ((s : ℝ) + 1)^2 ≤ (s : ℝ)^3 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hsr3)
      (show 0 ≤ (s : ℝ)^2 + 2 * (s : ℝ) + 4 by positivity)]
  have hlogXle : Real.log (X : ℝ) ≤ 3 * Real.log (s : ℝ) := by
    simpa using Real.log_le_log (by linarith : (0 : ℝ) < X) (hXle.trans hcube)
  have hlogsle : Real.log (s : ℝ) ≤ Real.log (W : ℝ) :=
    Real.log_le_log (by linarith) hWr
  have hlogpow : Real.log (X : ℝ)^4 ≤ Real.sqrt (X : ℝ) / 2 := by
    have h := hN X ((le_max_left ..).trans hX)
    change ‖Real.log (X : ℝ) ^ (4 : ℝ)‖ ≤ (1 / 2) * ‖(X : ℝ) ^ (1 / 2 : ℝ)‖ at h
    rw [Real.rpow_ofNat, ← Real.sqrt_eq_rpow, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hlogX.le _), abs_of_nonneg (Real.sqrt_nonneg _)] at h
    linarith only [h]
  have hsqrt1 : 1 ≤ Real.sqrt (X : ℝ) := by
    simpa using Real.sqrt_le_sqrt hX1r.le
  have htwo : (s : ℝ) + 1 ≤ 2 * Real.sqrt (X : ℝ) := by
    linarith [Real.nat_sqrt_le_real_sqrt (a := X)]
  have hfinal : ((s + 1 : ℕ) : ℝ) ≤ (X : ℝ) / (Real.log (X : ℝ))^4 := by
    apply (le_div_iff₀ (pow_pos hlogX 4)).mpr
    push_cast
    calc
      ((s : ℝ) + 1) * Real.log (X : ℝ)^4 ≤
          (2 * Real.sqrt (X : ℝ)) * (Real.sqrt (X : ℝ) / 2) :=
        mul_le_mul htwo hlogpow (by positivity) (by positivity)
      _ = (X : ℝ) := by nlinarith only [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ X)]
  exact ⟨hA, hs3, hlogs, hlogW, hlogXle, by linarith, hfinal⟩

end DynBlockCollision

namespace DynBlockCollision

open Finset

/-- The shifted-prime bound and the square mean control the sum of shift factors over small-prime pairs. -/
private theorem shift_factor_sum (s : ℕ) (hs : 3 ≤ s) (K : ℝ) (hK : 0 ≤ K)
    (hsieve : ∀ d : ℕ, 0 < d → Even d → d ≤ s →
      (((Icc s (s + s)).filter (fun p => p.Prime ∧ (p + d).Prime)).card : ℝ) ≤
        K * (s : ℝ) * GoldbachSquareMean.Sf d / (Real.log s)^2) :
    (∑ p ∈ (Icc s (2*s)).filter Nat.Prime,
      ∑ q ∈ ((Icc s (2*s)).filter Nat.Prime).filter (fun q => p < q),
        GoldbachSquareMean.Sf (q - p)) ≤
      4 * K * (s : ℝ)^2 / (Real.log s)^2 := by
  calc
    _ ≤ K * (s : ℝ) / (Real.log s)^2 *
        ∑ d ∈ Icc 1 s, GoldbachSquareMean.Sf d ^ 2 :=
      MeanCond.pair_bound s hs K (Real.log s) hK hsieve
    _ ≤ K * (s : ℝ) / (Real.log s)^2 * (4 * (s : ℝ)) :=
      mul_le_mul_of_nonneg_left (GoldbachSquareMean.Sf_sq_sum s) (by positivity)
    _ = _ := by ring

end DynBlockCollision

namespace DynBlockCollision

open Finset
noncomputable section

/-- Translate common endpoints by the larger prime, retaining the window length. -/
private theorem local_pairs {A P : Finset ℕ} {s W y p q : ℕ}
    (hs : 3 ≤ s) (hsW : s ≤ W) (hsy : 2 * s ≤ y)
    (hA : A ⊆ Ico y (y + W)) (hP : P ⊆ (Icc s (2 * s)).filter Nat.Prime)
    (hp : p ∈ P) (hq : q ∈ P) (hpq : p < q)
    {K : ℝ}
    (hshift : ∀ a d : ℕ, 0 < d → Even d → d ≤ W →
      (((Icc a (a + W)).filter (fun m => m.Prime ∧ (m + d).Prime)).card : ℝ) ≤
        K * (W : ℝ) * GoldbachSquareMean.Sf d / (Real.log (W : ℝ))^2) :
    pairs A p q ≤ K * (W : ℝ) * GoldbachSquareMean.Sf (q - p) / (Real.log (W : ℝ))^2 := by
  obtain ⟨hpI, hpp⟩ := mem_filter.mp (hP hp)
  obtain ⟨hqI, hqp⟩ := mem_filter.mp (hP hq)
  obtain ⟨hps, hp2s⟩ := mem_Icc.mp hpI
  obtain ⟨hqs, hq2s⟩ := mem_Icc.mp hqI
  have hEven : Even (q - p) := Nat.Odd.sub_odd
    (hqp.odd_of_ne_two (by omega)) (hpp.odd_of_ne_two (by omega))
  apply le_trans _ (hshift (y - q) (q - p) (by omega) hEven (by omega))
  unfold pairs
  exact_mod_cast (show ((A.filter (fun n => p ≤ n ∧ Nat.Prime (n-p) ∧ q ≤ n ∧
      Nat.Prime (n-q))).card : ℕ) ≤
      ((Icc (y - q) (y - q + W)).filter (fun m => m.Prime ∧ (m + (q - p)).Prime)).card from by
    apply card_le_card_of_injOn (fun n => n - q)
    · intro n hn
      obtain ⟨hnA, hpn, hpnPrime, hqn, hqnPrime⟩ := mem_filter.mp hn
      have hnBounds := mem_Ico.mp (hA hnA)
      simp only [coe_filter, Set.mem_ofPred_eq, mem_Icc]
      refine ⟨⟨by omega, by omega⟩, hqnPrime, ?_⟩
      rwa [show n - q + (q - p) = n - p by omega]
    · intro n hn m hm hnm
      have hqn := (mem_filter.mp hn).2.2.2.1
      have hqm := (mem_filter.mp hm).2.2.2.1
      change n - q = m - q at hnm
      omega)

end
end DynBlockCollision

namespace DynBlockCollision

open Finset
noncomputable section

private theorem block_budget :
    let E := fun X : ℕ => (Icc X (2 * X)).filter (fun n => Even n)
    let P := fun X : ℕ => (Icc X.sqrt (2 * X.sqrt)).filter Nat.Prime
    let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n - p))).card
    let W := fun X : ℕ => X.sqrt * X.sqrt.sqrt
    let B := fun (X y : ℕ) => (E X).filter (fun n => y ≤ n ∧ n < y + W X)
    let M := fun X : ℕ => Real.sqrt (X : ℝ) / (Real.log (X : ℝ))^2
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ,
      X ≤ y → y + W X ≤ 2 * X →
        (∑ n ∈ B X y, (H X n : ℝ)^2) ≤ C * (W X : ℝ) * (M X)^2 := by
  intro E P H W B M
  obtain ⟨K, hK, Z₀, hshift⟩ := shifted_pair_upper
  obtain ⟨X₀, hscales⟩ := scales Z₀
  refine ⟨1 + 648 * K^2, by positivity, X₀, ?_⟩
  intro X hX y hy _
  let s := X.sqrt
  let w := s * s.sqrt
  let primes := P X
  let A := B X y
  obtain ⟨hsZ, hs3, hls, hlw, hxs, hxw, hdiag⟩ := hscales X hX
  have hsquare : s * s ≤ X := Nat.sqrt_le X
  have hsy : 2 * s ≤ y := (Nat.mul_le_mul_right s (show 2 ≤ s by omega)).trans (hsquare.trans hy)
  have hsw : s ≤ w := by
    exact Nat.le_mul_of_pos_right s (Nat.sqrt_pos.mpr (by omega))
  have hA : A ⊆ Ico y (y + w) := fun _ hn => mem_Ico.mpr (mem_filter.mp hn).2
  have hP : primes = (Icc s (2 * s)).filter Nat.Prime := rfl
  have hAcard : A.card ≤ w := by
    have hc := card_le_card hA
    rwa [Nat.card_Ico, Nat.add_sub_cancel_left] at hc
  have hPcard : primes.card ≤ s + 1 := by
    rw [hP]
    calc
      _ ≤ (Icc s (2 * s)).card := card_filter_le ..
      _ = s + 1 := by rw [Nat.card_Icc]; omega
  let lx := Real.log (X : ℝ)
  let ls := Real.log (s : ℝ)
  let lw := Real.log (w : ℝ)
  have hlx : 0 < lx := by
    apply Real.log_pos
    exact_mod_cast (show 1 < X by nlinarith [hs3, hsquare])
  have hshiftW := hshift w (hsZ.trans hsw)
  have hsf : (∑ p ∈ primes, ∑ q ∈ primes.filter (fun q => p < q),
      GoldbachSquareMean.Sf (q - p)) ≤ 4 * K * (s : ℝ)^2 / ls^2 := by
    rw [hP]
    exact shift_factor_sum s hs3 K hK.le (fun d hd hev hds => hshift s hsZ s d hd hev hds)
  have hpairs : (∑ p ∈ primes, ∑ q ∈ primes.filter (fun q => p < q), pairs A p q) ≤
      (K * (w : ℝ) / lw^2) * (4 * K * (s : ℝ)^2 / ls^2) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hsf (by positivity))
    rw [mul_sum]
    refine sum_le_sum (fun p hp => ?_)
    rw [mul_sum]
    refine sum_le_sum (fun q hq => ?_)
    obtain ⟨hqP, hpq⟩ := mem_filter.mp hq
    calc
      _ ≤ K * (w : ℝ) * GoldbachSquareMean.Sf (q - p) / lw^2 :=
        local_pairs hs3 hsw hsy hA hP.le hp hqP hpq hshiftW
      _ = _ := by ring
  have hlogS : lx^2 ≤ 9 * ls^2 := by
    have he : lx^2 ≤ (3 * ls)^2 := pow_le_pow_left₀ hlx.le hxs 2
    nlinarith only [he]
  have hlogW : lx^2 ≤ 9 * lw^2 := by
    have he : lx^2 ≤ (3 * lw)^2 := pow_le_pow_left₀ hlx.le hxw 2
    nlinarith only [he]
  have hlog : lx^4 ≤ 81 * (ls^2 * lw^2) := by
    have he := mul_le_mul hlogS hlogW (sq_nonneg lx) (by positivity : 0 ≤ 9 * ls^2)
    nlinarith only [he]
  have hratio : (s : ℝ)^2 / (ls^2 * lw^2) ≤ 81 * ((X : ℝ) / lx^4) := by
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    have hsR : (s : ℝ)^2 ≤ X := by
      simpa only [pow_two] using (show (s : ℝ) * s ≤ X by exact_mod_cast hsquare)
    calc
      (s : ℝ)^2 * lx^4 ≤ (X : ℝ) * lx^4 := mul_le_mul_of_nonneg_right hsR (by positivity)
      _ ≤ (X : ℝ) * (81 * (ls^2 * lw^2)) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = _ := by ring
  have hlocal : (K * (w : ℝ) / lw^2) * (4 * K * (s : ℝ)^2 / ls^2) ≤
      324 * K^2 * (w : ℝ) * ((X : ℝ) / lx^4) := by
    calc
      _ = (4 * K^2 * (w : ℝ)) * ((s : ℝ)^2 / (ls^2 * lw^2)) := by
        field_simp [ne_of_gt hls, ne_of_gt hlw]
      _ ≤ (4 * K^2 * (w : ℝ)) * (81 * ((X : ℝ) / lx^4)) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring
  have hdiagonal : (A.card : ℝ) * (primes.card : ℝ) ≤ (w : ℝ) * ((X : ℝ) / lx^4) := by
    have hcardR : (primes.card : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by exact_mod_cast hPcard
    exact mul_le_mul (by exact_mod_cast hAcard) (hcardR.trans hdiag) (by positivity) (by positivity)
  have hM : (M X)^2 = (X : ℝ) / lx^4 := by
    change (Real.sqrt (X : ℝ) / lx^2)^2 = _
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg X)]
    ring
  rw [hM]
  calc
    _ ≤ (A.card : ℝ) * (primes.card : ℝ) +
        2 * ∑ p ∈ primes, ∑ q ∈ primes.filter (fun q => p < q), pairs A p q :=
      square_sum_le A primes
    _ ≤ (w : ℝ) * ((X : ℝ) / lx^4) +
        2 * (324 * K^2 * (w : ℝ) * ((X : ℝ) / lx^4)) := by
      exact add_le_add hdiagonal (mul_le_mul_of_nonneg_left (hpairs.trans hlocal) (by norm_num))
    _ = _ := by change _ = (1 + 648 * K^2) * (w : ℝ) * ((X : ℝ) / lx^4); ring

end
end DynBlockCollision

/-- In every admissible moving block, the common-endpoint count has a bounded second moment. -/
theorem Conjectures.Goldbach.DynBlockCollisionBudget :
    let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n);
    let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime;
    let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card;
    let W := fun X : ℕ => Nat.sqrt X * Nat.sqrt (Nat.sqrt X);
    let B := fun (X y : ℕ) => (E X).filter (fun n => y ≤ n ∧ n < y + W X);
    let M := fun X : ℕ => Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2;
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y + W X ≤ 2*X →
      (∑ n ∈ B X y, (H X n:ℝ)^2) ≤ C*(W X:ℝ)*(M X)^2 :=
  DynBlockCollision.block_budget
