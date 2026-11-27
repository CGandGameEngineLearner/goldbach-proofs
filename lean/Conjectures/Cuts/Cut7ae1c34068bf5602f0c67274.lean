import Conjectures.TwinPrimes.SharpWindowContamination

namespace TwinWindowCount

open Finset

noncomputable section

def window (X : ℕ) : Finset ℕ :=
  (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)

def pairs (X : ℕ) : Finset ℕ :=
  (window X).filter (fun n => n.Prime ∧ (n+2).Prime)

def weight (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)

def logScale (X : ℕ) : ℝ := Real.log (2+(X:ℝ))
def errorScale (X : ℕ) : ℝ := logScale X ^ 3 / Real.sqrt X
def mass (X : ℕ) : ℝ := (window X).sum weight / (X:ℝ)

def RecordedSurplus : Prop :=
  ∀ (K : ℝ) (B : ℕ), ∃ X : ℕ, B < X ∧ K * errorScale X < mass X

def ArbitrarilyLargePairCounts : Prop :=
  ∀ (C : ℝ) (B : ℕ), ∃ X : ℕ, B < X ∧
    C * (Real.sqrt X * logScale X) < ((pairs X).card : ℝ)

private theorem logScale_pos (X : ℕ) : 0 < logScale X :=
  Real.log_pos (by have := Nat.cast_nonneg (α:=ℝ) X; linarith)

private theorem errorScale_mul {X : ℕ} (hX : 2 ≤ X) :
    errorScale X * (X : ℝ) = Real.sqrt X * logScale X ^ 3 := by
  have h0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hs : 0 < Real.sqrt (X : ℝ) := Real.sqrt_pos.2 h0
  unfold errorScale
  calc
    _ = logScale X ^ 3 / Real.sqrt X * (Real.sqrt X)^2 := by
      rw [Real.sq_sqrt h0.le]
    _ = _ := by field_simp [hs.ne']

private theorem pair_weight_bounds {X n : ℕ} (hX : 2 ≤ X) (hn : n ∈ pairs X) :
    logScale X^2/4 ≤ weight n ∧ weight n ≤ 4*logScale X^2 := by
  obtain ⟨hnW, hnP, hn2P⟩ := Finset.mem_filter.mp hn
  obtain ⟨hnR,hnX,_⟩ := Finset.mem_filter.mp hnW
  have hx : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hXp : (0 : ℝ) < X := by linarith
  have hnlo : (X : ℝ) ≤ n := by exact_mod_cast hnX.le
  have hnhi : (n : ℝ) ≤ 2*(X:ℝ) := by
    exact_mod_cast (show n ≤ 2*X by have := Finset.mem_range.mp hnR; omega)
  have htwice : logScale X ≤ 2*Real.log (X:ℝ) := by
    calc
      logScale X ≤ Real.log ((X:ℝ)^2) :=
        Real.log_le_log (by positivity) (by nlinarith only [hx,mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hx)])
      _ = _ := by rw [Real.log_pow]; norm_num
  have hNp : (0:ℝ) < n := by linarith
  have hN2p : (0:ℝ) < ((n+2:ℕ):ℝ) := by positivity
  have h0 := Real.log_le_log hXp hnlo
  have h1 : Real.log (X:ℝ) ≤ Real.log ((n+2:ℕ):ℝ) := by
    apply Real.log_le_log hXp
    push_cast
    linarith
  have hl0 : logScale X/2 ≤ Real.log (n:ℝ) := by linarith
  have hl1 : logScale X/2 ≤ Real.log ((n+2:ℕ):ℝ) := by linarith
  have hu1 : Real.log ((n+2:ℕ):ℝ) ≤ 2*logScale X := by
    calc
      _ ≤ Real.log ((2+(X:ℝ))^2) := by
        apply Real.log_le_log hN2p
        push_cast
        nlinarith only [hnhi,hx,sq_nonneg (X:ℝ)]
      _ = _ := by rw [Real.log_pow]; norm_num [logScale]
  have hu0 : Real.log (n:ℝ) ≤ 2*logScale X :=
    (Real.log_le_log hNp (by exact_mod_cast (show n≤n+2 by omega))).trans hu1
  rw [weight, ArithmeticFunction.vonMangoldt_apply_prime hnP,
    ArithmeticFunction.vonMangoldt_apply_prime hn2P]
  have hLog := logScale_pos X
  constructor
  · have h := mul_le_mul hl0 hl1 (by positivity : 0 ≤ logScale X/2)
      (by linarith [show 0 ≤ logScale X/2 by positivity] : 0 ≤ Real.log (n:ℝ))
    nlinarith only [h]
  · have h := mul_le_mul hu0 hu1 (by linarith [show 0 ≤ logScale X/2 by positivity] :
      0 ≤ Real.log ((n+2:ℕ):ℝ)) (by positivity : 0 ≤ 2*logScale X)
    nlinarith only [h]

private theorem count_le_mass {X : ℕ} (hX : 2 ≤ X) :
    ((pairs X).card:ℝ) * (logScale X^2/4) ≤ (window X).sum weight := by
  calc
    _ = ∑ n ∈ pairs X, logScale X^2/4 := by simp
    _ ≤ (pairs X).sum weight := sum_le_sum fun _ hn => (pair_weight_bounds hX hn).1
    _ ≤ (window X).sum weight := sum_le_sum_of_subset_of_nonneg
      (filter_subset ..) (fun _ _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        ArithmeticFunction.vonMangoldt_nonneg)

private theorem mass_le_count_and_contamination {C : ℝ}
    (hContamination : ∀ X : ℕ, 2 ≤ X →
      ((window X).filter (fun n => ¬ (n.Prime ∧ (n+2).Prime))).sum weight / (X:ℝ)
        ≤ C * errorScale X)
    {X : ℕ} (hX : 2 ≤ X) :
    mass X ≤ ((pairs X).card:ℝ) * (4*logScale X^2) / (X:ℝ) + C*errorScale X := by
  have hSplit : (pairs X).sum weight +
        ((window X).filter (fun n => ¬ (n.Prime ∧ (n+2).Prime))).sum weight =
      (window X).sum weight := by
    exact sum_filter_add_sum_filter_not (window X) (fun n => n.Prime ∧ (n+2).Prime) weight
  have hCount : (pairs X).sum weight ≤ ((pairs X).card:ℝ)*(4*logScale X^2) := by
    calc
      _ ≤ ∑ n ∈ pairs X, 4*logScale X^2 := sum_le_sum fun _ hn => (pair_weight_bounds hX hn).2
      _ = _ := by simp
  rw [mass, ← hSplit, add_div]
  exact add_le_add (div_le_div_of_nonneg_right hCount (Nat.cast_nonneg X)) (hContamination X hX)

theorem window_surplus_iff_pair_counts : RecordedSurplus ↔ ArbitrarilyLargePairCounts := by
  constructor
  · intro hSurplus A B
    obtain ⟨C, _, hCont⟩ := Conjectures.TwinPrimes.SharpWindowContamination
    have hc (X : ℕ) (hx : 2 ≤ X) :
        ((window X).filter (fun n => ¬ (n.Prime ∧ (n+2).Prime))).sum weight / (X:ℝ)
          ≤ C * errorScale X := by
      unfold window weight errorScale logScale
      simpa only [mul_div_assoc] using hCont X hx
    obtain ⟨X, hBX, hLarge⟩ := hSurplus (C+4*A) (max B 1)
    have hX : 2 ≤ X := by omega
    have hXp : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
    have hEst := mass_le_count_and_contamination hc hX
    have hLow : (4*A)*errorScale X < ((pairs X).card:ℝ)*(4*logScale X^2)/(X:ℝ) := by
      simp only [add_mul] at hLarge
      linarith only [hLarge,hEst]
    have hScaled := (lt_div_iff₀ hXp).mp hLow
    refine ⟨X, by omega, ?_⟩
    have hLog := logScale_pos X
    have hStrict : (A*(Real.sqrt X*logScale X))*(4*logScale X^2) <
        ((pairs X).card:ℝ)*(4*logScale X^2) := by
      calc
        _ = (4*A)*(errorScale X*(X:ℝ)) := by rw [errorScale_mul hX]; ring
        _ = ((4*A)*errorScale X)*(X:ℝ) := (mul_assoc _ _ _).symm
        _ < _ := hScaled
    by_contra! hReverse
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_right hReverse (by positivity))) hStrict
  · intro hCounts K B
    obtain ⟨X,hBX,hCount⟩ := hCounts (4*K) (max B 1)
    have hX : 2 ≤ X := by omega
    have hXp : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
    have hLog := logScale_pos X
    refine ⟨X, by omega, ?_⟩
    apply (lt_div_iff₀ hXp).2
    calc
      K * errorScale X * (X:ℝ) =
          (4*K*(Real.sqrt X*logScale X))*(logScale X^2/4) := by
        rw [mul_assoc,errorScale_mul hX]
        ring
      _ < ((pairs X).card : ℝ)*(logScale X^2/4) :=
        mul_lt_mul_of_pos_right hCount (by positivity)
      _ ≤ (window X).sum weight := count_le_mass hX

end

end TwinWindowCount

theorem twin_window_frozen_equivalence :
    (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let v := fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2); let M := fun (X : ℕ) => (w X).sum v / (X : ℝ); let e := fun (X : ℕ) => Real.log (2+(X:ℝ))^3 / Real.sqrt X; ∀ (K : ℝ) (B : ℕ), ∃ X : ℕ, B < X ∧ K * e X < M X) ↔ TwinWindowCount.ArbitrarilyLargePairCounts :=
  TwinWindowCount.window_surplus_iff_pair_counts

#print axioms twin_window_frozen_equivalence


namespace TwinDyadicGridCut

open Finset TwinWindowCount

set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

private def start (X i : ℕ) : ℕ := min (2 * X) (X + (X / 100) * i)

private theorem start_bounds (X i : ℕ) : X ≤ start X i ∧ start X i ≤ 2 * X := by
  exact ⟨le_min (by omega) (Nat.le_add_right _ _), min_le_left _ _⟩

private def dyadicPairs (X : ℕ) : Finset ℕ :=
  (Ioc X (2 * X)).filter (fun n => n.Prime ∧ (n + 2).Prime)

def GridCover : Prop :=
  ∀ X : ℕ, 200 ≤ X → ∀ n : ℕ, X < n → n ≤ 2 * X →
    ∃ i < 201, let Y := min (2*X) (X+(X/100)*i); Y < n ∧ 50*n < 51*Y

def DyadicPairCounts : Prop :=
  ∀ C : ℝ, ∀ B : ℕ, ∃ X : ℕ, B < X ∧
    C * (Real.sqrt (2 * (X : ℝ)) * Real.log (2 + 2 * (X : ℝ))) <
      ((dyadicPairs X).card : ℝ)

private theorem dyadicPairs_subset_windows (hCover : GridCover) {X : ℕ} (hX : 200 ≤ X) :
    dyadicPairs X ⊆ (range 201).biUnion (fun i => pairs (start X i)) := by
  intro n hn
  obtain ⟨hnI, hPrime⟩ := mem_filter.mp hn
  obtain ⟨hnLo, hnHi⟩ := mem_Ioc.mp hnI
  obtain ⟨i, hi, hY⟩ := hCover X hX n hnLo hnHi
  change start X i < n ∧ 50*n < 51*start X i at hY
  have hnRange : n < 2 * start X i + 1 := by omega
  exact mem_biUnion.mpr ⟨i, mem_range.mpr hi,
    mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr hnRange, hY⟩, hPrime⟩⟩

private theorem scale_at_most {X Y : ℕ} (hY : Y ≤ 2 * X) :
    Real.sqrt (Y : ℝ) * logScale Y ≤ Real.sqrt (2 * (X : ℝ)) *
      Real.log (2 + 2 * (X : ℝ)) := by
  have hYr : (Y : ℝ) ≤ 2 * (X : ℝ) := by exact_mod_cast hY
  have hLog : logScale Y ≤ Real.log (2 + 2 * (X : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith only [hYr])
  have hPos : 0 ≤ logScale Y := Real.log_nonneg (by
    have h := Nat.cast_nonneg (α := ℝ) Y
    linarith)
  exact mul_le_mul (Real.sqrt_le_sqrt hYr) hLog hPos (Real.sqrt_nonneg _)

theorem pairs_of_dyadic_and_cover (hDyadic : DyadicPairCounts) (hCover : GridCover) :
    ArbitrarilyLargePairCounts := by
  intro C B
  let K := max C 0
  have hK : 0 ≤ K := le_max_right _ _
  obtain ⟨X, hXlate, hLarge⟩ := hDyadic (201*K) (max B 199)
  have hBX : B < X := (le_max_left _ _).trans_lt hXlate
  have hX : 200 ≤ X := by omega
  by_contra! hNo
  have hCompare (i : ℕ) (_hi : i ∈ range 201) :
      ((pairs (start X i)).card : ℝ) ≤
        K * (Real.sqrt (2 * (X : ℝ)) * Real.log (2 + 2 * (X : ℝ))) := by
    have hY := start_bounds X i
    have hLate : B < start X i := hBX.trans_le hY.1
    have hMass := hNo (start X i) hLate
    have hPos : 0 ≤ Real.sqrt (start X i : ℝ) * logScale (start X i) := by
      apply mul_nonneg (Real.sqrt_nonneg _)
      apply Real.log_nonneg
      have h := Nat.cast_nonneg (α := ℝ) (start X i)
      linarith
    exact hMass.trans ((mul_le_mul_of_nonneg_right (le_max_left C 0) hPos).trans
      (mul_le_mul_of_nonneg_left (scale_at_most hY.2) hK))
  have hCard : (dyadicPairs X).card ≤ ∑ i ∈ range 201, (pairs (start X i)).card :=
    (card_le_card (dyadicPairs_subset_windows hCover hX)).trans card_biUnion_le
  have hCardReal : ((dyadicPairs X).card : ℝ) ≤ ∑ i ∈ range 201, ((pairs (start X i)).card : ℝ) := by
    exact_mod_cast hCard
  have hSum := sum_le_sum hCompare
  have hTotal : (∑ i ∈ range 201, K * (Real.sqrt (2 * (X : ℝ)) *
        Real.log (2 + 2 * (X : ℝ)))) =
      (201*K) * (Real.sqrt (2 * (X : ℝ)) * Real.log (2 + 2 * (X : ℝ))) := by
    simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_ofNat]
    ring
  exact hLarge.not_ge (hCardReal.trans (hSum.trans_eq hTotal))

theorem window_surplus_of_dyadic_and_cover
    (hDyadic : DyadicPairCounts) (hCover : GridCover) :
    (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let v := fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2); let M := fun (X : ℕ) => (w X).sum v / (X : ℝ); let e := fun (X : ℕ) => Real.log (2+(X:ℝ))^3 / Real.sqrt X; ∀ (K : ℝ) (B : ℕ), ∃ X : ℕ, B < X ∧ K * e X < M X) :=
  twin_window_frozen_equivalence.mpr (pairs_of_dyadic_and_cover hDyadic hCover)

#print axioms window_surplus_of_dyadic_and_cover

end TwinDyadicGridCut

namespace Conjectures.Cuts

-- child 1 zh: 在任意晚的二倍区间内，真孪生素数对计数超过任意常数倍的平方根乘对数尺度。
-- child 1 en: The true twin-prime count in arbitrarily late dyadic intervals exceeds each constant times the square-root logarithmic scale.
-- child 2 zh: 用 201 个起点的严格短窗覆盖二倍区间内的所有整数。
-- child 2 en: The strict short windows based at 201 starting points cover every integer in the dyadic interval.
theorem Cut7ae1c34068bf5602f0c67274 :
    (∀ C : ℝ, ∀ B : ℕ, ∃ X : ℕ, B < X ∧
      C * (Real.sqrt (2 * (X : ℝ)) * Real.log (2 + 2 * (X : ℝ))) <
        (((Finset.Ioc X (2 * X)).filter (fun n => n.Prime ∧ (n + 2).Prime)).card : ℝ)) →
    (∀ X : ℕ, 200 ≤ X → ∀ n : ℕ, X < n → n ≤ 2 * X →
      ∃ i < 201, let Y := min (2*X) (X+(X/100)*i); Y < n ∧ 50*n < 51*Y) →
    (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let v := fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2); let M := fun (X : ℕ) => (w X).sum v / (X : ℝ); let e := fun (X : ℕ) => Real.log (2+(X:ℝ))^3 / Real.sqrt X; ∀ (K : ℝ) (B : ℕ), ∃ X : ℕ, B < X ∧ K * e X < M X) :=
  TwinDyadicGridCut.window_surplus_of_dyadic_and_cover

#print axioms Cut7ae1c34068bf5602f0c67274

end Conjectures.Cuts
