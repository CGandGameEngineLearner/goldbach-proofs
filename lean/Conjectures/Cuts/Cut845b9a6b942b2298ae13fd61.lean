import Mathlib
import Conjectures.Goldbach.PolynomialFourierTransference

-- child 1 zh: 对每个既约类的归一化素数权重，控制受它支配的非负函数的三次谱矩。
-- child 1 en: Bound the cubic Fourier moment of nonnegative functions dominated by the normalized prime weight.
-- child 2 zh: 加细固定模数，使各既约类的归一化素数权重具有一致的小傅里叶偏差。
-- child 2 en: Refine the fixed modulus so all normalized prime weights have small Fourier discrepancy.
-- child 3 zh: 将固定既约类中的素数计数下密度转为相应的对数加权下界。
-- child 3 en: Transfer lower counting density in a fixed reduced class to a logarithmic weight bound.

open Finset
open scoped BigOperators

set_option maxHeartbeats 1200000 in
theorem Conjectures.Cuts.Cut845b9a6b942b2298ae13fd61
    (restriction :
      ∀ W : ℕ, 0 < W → ∃ C : ℝ, 1 ≤ C ∧
        ∀ d : ℕ, 0 < d → 2 * W ∣ d →
          ∃ T : ℕ, ∀ (N : ℕ) [NeZero N], T ≤ N →
            ∀ a : ℕ, a < d → a.Coprime d →
              let ν := fun x : ZMod N =>
                if Nat.Prime (d * x.val + a) then
                  (d.totient : ℝ) / (d : ℝ) * Real.log (d * x.val + a : ℕ)
                else 0
              let ft := fun (h : ZMod N → ℝ) (r : ZMod N) =>
                (∑ x : ZMod N, (h x : ℂ) *
                  Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
                    ((r * x).val : ℂ) / (N : ℂ))) / (N : ℂ)
              ∀ f : ZMod N → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ ν x) →
                (∑ r : ZMod N, ‖ft f r‖ ^ (3 : ℝ)) ≤ C ^ (3 : ℝ))
    (uniformity :
      ∀ W : ℕ, 0 < W → ∀ β : ℝ, 0 < β →
        ∃ d : ℕ, 0 < d ∧ 2 * W ∣ d ∧
          ∃ T : ℕ, ∀ (N : ℕ) [NeZero N], T ≤ N →
            ∀ a : ℕ, a < d → a.Coprime d →
              let ν := fun x : ZMod N =>
                if Nat.Prime (d * x.val + a) then
                  (d.totient : ℝ) / (d : ℝ) * Real.log (d * x.val + a : ℕ)
                else 0
              let ft := fun (h : ZMod N → ℝ) (r : ZMod N) =>
                (∑ x : ZMod N, (h x : ℂ) *
                  Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
                    ((r * x).val : ℂ) / (N : ℂ))) / (N : ℂ)
              ∀ r : ZMod N, ‖ft (fun x => ν x - 1) r‖ ≤ β)
    (weighted :
      ∀ (A : Set ℕ) [DecidablePred (· ∈ A)], (∀ p ∈ A, Nat.Prime p) →
        ∀ (d a : ℕ) (t : ℝ), 2 ≤ d → a < d → a.Coprime d → 0 ≤ t → t ≤ 1 →
          let primes := fun N : ℕ =>
            (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ p % d = a)
          (∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ N ≥ T,
            (t - ε) * ((primes N).card : ℝ) ≤
              (((primes N).filter (· ∈ A)).card : ℝ)) →
          ∀ ζ : ℝ, 0 < ζ → ∃ T : ℕ, ∀ L ≥ T,
            (t - ζ) * ((d * L : ℕ) : ℝ) ≤
              (d.totient : ℝ) * ∑ j ∈ Finset.range L,
                if d * j + a ∈ A then Real.log (d * j + a : ℕ) else 0) : (by
  classical
  let primes := fun N q a : ℕ => (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ p % q=a)
  let dense := fun (A : Set ℕ) (d a : ℕ) (t : ℝ) => ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ N ≥ T, (t-ε)*((primes N d a).card:ℝ) ≤ (((primes N d a).filter (fun p => p ∈ A)).card:ℝ)
  exact ∀ A B : Set ℕ, (∀ p ∈ A, Nat.Prime p) → (∀ p ∈ B, Nat.Prime p) →
    ∀ W b : ℕ, 0 < W → b < W → (∃ δ : ℝ, 0 < δ ∧ ∀ d : ℕ, 0 < d → 2*W ∣ d → ∀ r : ℕ, r < d → Even r → r % W=b →
      ∃ a c : ℕ, a < d ∧ c < d ∧ a.Coprime d ∧ c.Coprime d ∧ (a+c) % d=r ∧ ∃ u v : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ 0 ≤ v ∧ v ≤ 1 ∧ 1+δ ≤ u+v ∧ dense A d a u ∧ dense B d c v) →
    ∀ η : ℝ, 0 < η → ∃ T : ℕ, ∀ X ≥ T, (((Finset.Icc 1 X).filter (fun n => Even n ∧ n % W=b ∧ ¬∃ p ∈ A, ∃ q ∈ B, p+q=n)).card:ℝ) ≤ η*(X:ℝ)/(W:ℝ)) := by
  classical
  have sum_below : ∀ {M L : ℕ} [NeZero M], L ≤ M → ∀ F : ℕ → ℝ,
      (∑ x : ZMod M, if x.val < L then F x.val else 0) =
        ∑ n ∈ Finset.range L, F n := by
    intro M L _ hL F
    classical
    rw [← Finset.sum_filter]
    refine Finset.sum_bij' (fun x _ => x.val) (fun n _ => (n : ZMod M)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
    · intro n hn
      have hnL := Finset.mem_range.mp hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rwa [ZMod.val_natCast_of_lt (hnL.trans_le hL)]⟩
    · intro x _
      exact ZMod.natCast_zmod_val x
    · intro n hn
      exact ZMod.val_natCast_of_lt ((Finset.mem_range.mp hn).trans_le hL)
    · intro x _
      rfl

  have positive_convolution : ∀ {M : ℕ} [NeZero M] (f g : ZMod M → ℝ) (t : ZMod M),
      (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ g x) →
        0 < (∑ x : ZMod M, f x * g (t-x)) / (M : ℝ) →
          ∃ x y : ZMod M, x+y = t ∧ 0 < f x ∧ 0 < g y := by
    intro M _ f g t hf hg h
    classical
    have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
    have hpos := (div_pos_iff_of_pos_right hM).mp h
    have hx : ∃ x : ZMod M, 0 < f x * g (t-x) := by
      by_contra! hn
      exact (not_le_of_gt hpos) (Finset.sum_nonpos (fun x _ => hn x))
    obtain ⟨x, hx⟩ := hx
    exact ⟨x, t-x, by abel, pos_of_mul_pos_left hx (hg _), pos_of_mul_pos_right hx (hf _)⟩

  let eligible (W d b : ℕ) : Finset ℕ :=
    (range d).filter (fun r => r % W = b ∧ Even r)

  have eligible_card_le (W d b : ℕ) (hW : 0 < W) (hdW : W ∣ d) :
      (eligible W d b).card ≤ d / W := by
      classical
      calc
        (eligible W d b).card ≤ (range (d/W)).card := by
          apply card_le_card_of_injOn (fun r : ℕ => r / W)
          · intro r hr
            have hr' := mem_range.mp (mem_filter.mp hr).1
            apply mem_range.mpr
            apply (Nat.div_lt_iff_lt_mul hW).mpr
            simpa only [Nat.div_mul_cancel hdW] using hr'
          · intro r hr s hs hq
            change r / W = s / W at hq
            have hrb := (mem_filter.mp hr).2.1
            have hsb := (mem_filter.mp hs).2.1
            calc
              r = r % W + W * (r / W) := (Nat.mod_add_div r W).symm
              _ = s % W + W * (s / W) := by rw [hrb, hsb, hq]
              _ = s := Nat.mod_add_div s W
        _ = d / W := card_range _

  have shell_card_eq (W d b : ℕ) (F : Finset ℕ)
      (hd : 0 < d) (hdW : W ∣ d) (hd2 : 2 ∣ d)
      (hF : ∀ n ∈ F, Even n ∧ n % W = b) :
      F.card = ∑ r ∈ eligible W d b, (F.filter (fun n => n % d = r)).card := by
      classical
      apply card_eq_sum_card_fiberwise (f := fun n : ℕ => n % d)
      intro n hn
      obtain ⟨hne, hnb⟩ := hF n hn
      refine mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt n hd), ?_, ?_⟩
      · exact (Nat.mod_mod_of_dvd n hdW).trans hnb
      · rw [Nat.even_iff, Nat.mod_mod_of_dvd n hd2]
        exact Nat.even_iff.mp hne

  have colorLift
      (d K m a c r n : ℕ) (hd : 0 < d) (hK : 2 ≤ K) (hm : 0 < m)
      (ha : a < d) (hc : c < d)
      (hn : n ∈ Finset.Ico (d * ((K - 1) * m)) (d * (K * m)))
      (hnr : n % d = r) (har : (a + c) % d = r) [NeZero ((K + 1) * m)] :
      let M := (K + 1) * m
      let t := n / d - (a + c) / d
      t < M ∧ n = d * t + (a + c) ∧
        ∀ x y : ZMod M, x + y = (t : ZMod M) →
          x.val < K * m → y.val < K * m →
          (d * x.val + a) + (d * y.val + c) = n := by
    intro M t
    obtain ⟨hnlo, hnhi⟩ := Finset.mem_Ico.mp hn
    have hqlo : (K - 1) * m ≤ n / d :=
      (Nat.le_div_iff_mul_le hd).2 (by simpa only [Nat.mul_comm d] using hnlo)
    have hqhi : n / d < K * m :=
      (Nat.div_lt_iff_lt_mul hd).2 (by simpa only [Nat.mul_comm d] using hnhi)
    have hCarry : (a + c) / d ≤ 1 := by
      have h : (a + c) / d < 2 := (Nat.div_lt_iff_lt_mul hd).2 (by omega)
      omega
    have hlo : 1 ≤ (K - 1) * m :=
      Nat.succ_le_of_lt (Nat.mul_pos (by omega) hm)
    have hq : n / d = t + (a + c) / d := by
      dsimp only [t]
      omega
    have hM : M = K * m + m := by
      dsimp only [M]
      rw [Nat.add_mul, one_mul]
    have hSplit : K * m = (K - 1) * m + m := by
      calc
        K * m = (K - 1 + 1) * m := by rw [show K - 1 + 1 = K by omega]
        _ = (K - 1) * m + m := by rw [Nat.add_mul, one_mul]
    have ht : t < M := by
      have hle : t ≤ n / d := Nat.sub_le _ _
      omega
    have hnLift : n = d * t + (a + c) := by
      have hnParts := Nat.mod_add_div n d
      have hAddParts := Nat.mod_add_div (a + c) d
      rw [hnr.trans har.symm, hq, Nat.mul_add] at hnParts
      omega
    refine ⟨ht, hnLift, ?_⟩
    intro x y hxy hx hy
    have hval : (x + y).val = t := by
      rw [hxy, ZMod.val_natCast, Nat.mod_eq_of_lt ht]
    have hSumBound : x.val + y.val < t + M := by omega
    have hNoWrap : x.val + y.val < M := by
      by_contra! hWrap
      have h := ZMod.val_add_val_of_le (a := x) (b := y) hWrap
      rw [hval] at h
      omega
    have hSum : x.val + y.val = t := (ZMod.val_add_of_lt hNoWrap).symm.trans hval
    calc
      (d * x.val + a) + (d * y.val + c) = d * (x.val + y.val) + (a + c) := by
        rw [Nat.mul_add]
        omega
      _ = n := by rw [hSum, ← hnLift]

  have color_label_injOn {d K m a c : ℕ} {S : Finset ℕ}
      (hd : 0 < d) (hK : 2 ≤ K) (hm : 0 < m) (ha : a < d) (hc : c < d)
      (hS : S ⊆ Finset.Ico (d * ((K - 1) * m)) (d * (K * m)))
      (hres : ∀ n ∈ S, n % d = (a + c) % d) :
      Set.InjOn (fun n : ℕ => ((n / d - (a + c) / d : ℕ) : ZMod ((K + 1) * m)))
        (↑S : Set ℕ) := by
    have hcarry : (a + c) / d ≤ 1 := by
      apply Nat.lt_succ_iff.mp
      apply (Nat.div_lt_iff_lt_mul hd).mpr
      omega
    have hleft : 0 < (K - 1) * m := Nat.mul_pos (by omega) hm
    have hbounds (n : ℕ) (hn : n ∈ S) :
        (a + c) / d ≤ n / d ∧ n / d - (a + c) / d < (K + 1) * m := by
      obtain ⟨hnlo, hnhi⟩ := Finset.mem_Ico.mp (hS hn)
      have hlo : (K - 1) * m ≤ n / d :=
        (Nat.le_div_iff_mul_le hd).mpr (by simpa only [Nat.mul_comm d] using hnlo)
      have hhi : n / d < K * m :=
        (Nat.div_lt_iff_lt_mul hd).mpr (by simpa only [Nat.mul_comm d] using hnhi)
      refine ⟨by omega, ?_⟩
      exact ((Nat.sub_le _ _).trans_lt hhi).trans_le
        (Nat.mul_le_mul_right m (Nat.le_succ K))
    intro n hn p hp hnp
    have hnS : n ∈ S := hn
    have hpS : p ∈ S := hp
    obtain ⟨hnc, hnM⟩ := hbounds n hnS
    obtain ⟨hpc, hpM⟩ := hbounds p hpS
    have heq := congrArg ZMod.val hnp
    change (((n / d - (a + c) / d : ℕ) : ZMod ((K + 1) * m))).val =
      (((p / d - (a + c) / d : ℕ) : ZMod ((K + 1) * m))).val at heq
    rw [ZMod.val_natCast_of_lt hnM, ZMod.val_natCast_of_lt hpM] at heq
    have hquot : n / d = p / d := by omega
    calc
      n = n % d + d * (n / d) := (Nat.mod_add_div n d).symm
      _ = p % d + d * (p / d) := by rw [hres n hnS, hres p hpS, hquot]
      _ = p := Nat.mod_add_div p d


  have color_label_card_le {d K m a c : ℕ} {S : Finset ℕ} {T : Finset (ZMod ((K + 1) * m))}
      (hd : 0 < d) (hK : 2 ≤ K) (hm : 0 < m) (ha : a < d) (hc : c < d)
      (hS : S ⊆ Finset.Ico (d * ((K - 1) * m)) (d * (K * m)))
      (hres : ∀ n ∈ S, n % d = (a + c) % d)
      (hmap : ∀ n ∈ S, ((n / d - (a + c) / d : ℕ) : ZMod ((K + 1) * m)) ∈ T) :
      S.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn
      (fun n : ℕ => ((n / d - (a + c) / d : ℕ) : ZMod ((K + 1) * m)))
      (fun _ hn => hmap _ hn)
    exact color_label_injOn hd hK hm ha hc hS hres

  have eventual_card_le (E : ℕ → Prop) [DecidablePred E]
      (d K W T : ℕ) (hd : 0 < d) (hK : 2 ≤ K) (hW : 0 < W)
      (η : ℝ) (hη : 0 < η)
      (hshell : ∀ m ≥ T,
        (((Ico (d * ((K - 1) * m)) (d * (K * m))).filter E).card : ℝ) ≤
          (η / (8 * (K : ℝ))) * ((d * (K * m) : ℕ) : ℝ) / (W : ℝ)) :
      ∃ X₀ : ℕ, ∀ X ≥ X₀,
        (((Icc 1 X).filter E).card : ℝ) ≤ η * (X : ℝ) / (W : ℝ) := by
    let B := d * K
    let D := d * (K - 1)
    let S := max (2 * K * B) (T * B)
    let slope : ℝ := η / (2 * (W : ℝ))
    have hB : 0 < B := Nat.mul_pos hd (by omega)
    have hKr : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
    have hWr : 0 < (W : ℝ) := by exact_mod_cast hW
    have hslope : 0 < slope := by dsimp [slope]; positivity
    have hDB : D + d = B := by
      have hpred : K - 1 + 1 = K := by omega
      simpa [D, B, Nat.mul_add] using congrArg (d * ·) hpred
    have hbound : ∀ X : ℕ, (((Icc 1 X).filter E).card : ℝ) ≤
        slope * (X : ℝ) + (S : ℝ) := by
      intro X
      induction X using Nat.strong_induction_on with
      | ind X ih =>
        by_cases hXS : S ≤ X
        · let m := X / B + 1
          have hm : T ≤ m := by
            have hT : T * B ≤ X := (le_max_right _ _).trans hXS
            exact ((Nat.le_div_iff_mul_le hB).2 hT).trans (Nat.le_succ _)
          have hXupper : X < B * m := Nat.lt_mul_div_succ X hB
          have hupper : B * m ≤ X + B := by
            dsimp [m]
            rw [Nat.mul_add, Nat.mul_one]
            exact Nat.add_le_add_right (Nat.mul_div_le X B) B
          have hBscale : 2 * K * B ≤ X := (le_max_left _ _).trans hXS
          have hXpos : 0 < X := (Nat.mul_pos (by positivity) hB).trans_le hBscale
          have hXr : 0 < (X : ℝ) := by exact_mod_cast hXpos
          have hsmallB : (B : ℝ) ≤ (X : ℝ) / (2 * (K : ℝ)) := by
            apply (le_div_iff₀ (by positivity : 0 < 2 * (K : ℝ))).2
            have hscaleR : ((2 * K * B : ℕ) : ℝ) ≤ (X : ℝ) := by exact_mod_cast hBscale
            push_cast at hscaleR
            simpa [mul_assoc, mul_comm, mul_left_comm] using hscaleR
          have hstep : (X : ℝ) / (K : ℝ) ≤ ((d * m : ℕ) : ℝ) := by
            apply (div_le_iff₀ hKr).2
            have hXupperR : (X : ℝ) ≤ ((B * m : ℕ) : ℝ) := by
              exact_mod_cast hXupper.le
            simpa [B, Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using hXupperR
          have hretreat : ((D * m : ℕ) : ℝ) + (X : ℝ) / (2 * (K : ℝ)) ≤ (X : ℝ) := by
            have hab : ((D * m : ℕ) : ℝ) + ((d * m : ℕ) : ℝ) = ((B * m : ℕ) : ℝ) := by
              exact_mod_cast (show D * m + d * m = B * m by rw [←Nat.add_mul, hDB])
            have hupperR : ((B * m : ℕ) : ℝ) ≤ (X : ℝ) + (B : ℝ) := by
              exact_mod_cast hupper
            have hhalf : (X : ℝ) / (K : ℝ) = 2 * ((X : ℝ) / (2 * (K : ℝ))) := by ring
            rw [hhalf] at hstep
            linarith
          have hprev : D * m < X := by
            exact_mod_cast (show ((D * m : ℕ) : ℝ) < (X : ℝ) from
              (lt_add_of_pos_right _ (by positivity : 0 < (X : ℝ) / (2 * (K : ℝ)))).trans_le hretreat)
          have hBm : ((B * m : ℕ) : ℝ) ≤ 2 * (X : ℝ) := by
            have hBX : B ≤ X :=
              (Nat.le_mul_of_pos_left B (by positivity : 0 < 2 * K)).trans hBscale
            exact_mod_cast (show B * m ≤ 2 * X by omega)
          have hcost : (((Ico (D * m) (B * m)).filter E).card : ℝ) ≤
              slope * ((X : ℝ) / (2 * (K : ℝ))) := by
            calc
              _ ≤ (η / (8 * (K : ℝ))) * ((B * m : ℕ) : ℝ) / (W : ℝ) := by
                simpa [D, B, Nat.mul_assoc] using hshell m hm
              _ ≤ (η / (8 * (K : ℝ))) * (2 * (X : ℝ)) / (W : ℝ) := by gcongr
              _ = _ := by dsimp [slope]; ring
          have hsubset : (Icc 1 X).filter E ⊆
              ((Icc 1 (D * m)).filter E) ∪ ((Ico (D * m) (B * m)).filter E) := by
            intro n hn
            obtain ⟨hn, hEn⟩ := mem_filter.mp hn
            obtain ⟨hnlo, hnhi⟩ := mem_Icc.mp hn
            apply mem_union.mpr
            by_cases hcut : n ≤ D * m
            · exact Or.inl (mem_filter.mpr ⟨mem_Icc.mpr ⟨hnlo, hcut⟩, hEn⟩)
            · exact Or.inr (mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, hnhi.trans_lt hXupper⟩, hEn⟩)
          have hcards : (((Icc 1 X).filter E).card : ℝ) ≤
              (((Icc 1 (D * m)).filter E).card : ℝ) + (((Ico (D * m) (B * m)).filter E).card : ℝ) := by
            exact_mod_cast (card_le_card hsubset).trans (card_union_le _ _)
          calc
            _ ≤ slope * ((D * m : ℕ) : ℝ) + (S : ℝ) +
                slope * ((X : ℝ) / (2 * (K : ℝ))) :=
              hcards.trans (add_le_add (ih (D * m) hprev) hcost)
            _ = slope * (((D * m : ℕ) : ℝ) + (X : ℝ) / (2 * (K : ℝ))) + (S : ℝ) := by ring
            _ ≤ _ := by gcongr
        · have hcard : ((Icc 1 X).filter E).card ≤ X := by
            simpa using (card_filter_le (s := Icc 1 X) E)
          have hcardR : (((Icc 1 X).filter E).card : ℝ) ≤ (S : ℝ) := by
            exact_mod_cast hcard.trans (Nat.le_of_lt (Nat.lt_of_not_ge hXS))
          exact hcardR.trans (le_add_of_nonneg_left (by positivity))
    obtain ⟨X₀, hX₀⟩ := exists_nat_ge ((S : ℝ) / slope)
    refine ⟨X₀, fun X hX => ?_⟩
    have hXr : (X₀ : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have hS := (div_le_iff₀ hslope).1 (hX₀.trans hXr)
    calc
      _ ≤ slope * (X : ℝ) + (S : ℝ) := hbound X
      _ ≤ slope * (X : ℝ) + (X : ℝ) * slope := by gcongr
      _ = _ := by dsimp [slope]; ring

  dsimp only
  intro A B hA hB W b hW hb compatible η hη
  obtain ⟨δ, hδ, hCompatible⟩ := compatible
  let δ₀ : ℝ := min (δ / 4) (1 / 4)
  have hδ₀ : 0 < δ₀ := lt_min (by positivity) (by norm_num)
  have hδ₀quarter : δ₀ ≤ 1 / 4 := min_le_right _ _
  have hδ₀one : δ₀ ≤ 1 := by linarith only [hδ₀quarter]
  have hδloss : 4 * δ₀ ≤ δ := by linarith only [min_le_left (δ / 4) (1 / 4)]
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / δ₀)
  let K : ℕ := k + 2
  have hK : 2 ≤ K := by dsimp [K]; omega
  have hKR : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hKδ : 2 ≤ (K : ℝ) * δ₀ := by
    have hk' : 2 < (k : ℝ) * δ₀ := (div_lt_iff₀ hδ₀).mp hk
    have hkK : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast (show k ≤ K by dsimp [K]; omega)
    exact hk'.le.trans (mul_le_mul_of_nonneg_right hkK hδ₀.le)
  let ρ : ℝ := min (η / (16 * (K : ℝ))) 1
  have hρ : 0 < ρ := lt_min (by positivity) (by norm_num)
  have hρone : ρ ≤ 1 := min_le_right _ _
  have hρsmall : ρ ≤ η / (16 * (K : ℝ)) := min_le_left _ _

  obtain ⟨C, hC, hRestriction⟩ := restriction W hW
  obtain ⟨c₀, J, hc₀, hJ, hTransfer⟩ :=
    Conjectures.Goldbach.PolynomialFourierTransference 3 C (by norm_num) (by norm_num) hC
  let β := c₀ * (δ₀ * ρ) ^ J
  have hβ : 0 < β := mul_pos hc₀ (Real.rpow_pos_of_pos (mul_pos hδ₀ hρ) _)
  obtain ⟨d, hd, hd2W, TFour, hFour⟩ := uniformity W hW β hβ
  have hdW : W ∣ d := dvd_trans (by exact ⟨2, by omega⟩) hd2W
  have hd2 : 2 ∣ d := dvd_trans (dvd_mul_right 2 W) hd2W
  have hdMin : 2 ≤ d := Nat.le_of_dvd hd hd2
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hWR : 0 < (W : ℝ) := by exact_mod_cast hW
  obtain ⟨TRestr, hRestr⟩ := hRestriction d hd hd2W

  let bad (n : ℕ) : Prop :=
    Even n ∧ n % W = b ∧ ¬∃ p ∈ A, ∃ q ∈ B, p + q = n
  let F (m : ℕ) := (Finset.Ico (d * ((K - 1) * m)) (d * (K * m))).filter bad
  let classes := (Finset.range d).filter (fun r => r % W = b ∧ Even r)
  let ν (a N : ℕ) (x : ZMod N) : ℝ :=
    if Nat.Prime (d * x.val + a) then
      (d.totient : ℝ) / (d : ℝ) * Real.log (d * x.val + a : ℕ)
    else 0
  have ν_nonneg (a N : ℕ) (x : ZMod N) : 0 ≤ ν a N x := by
    unfold ν
    split
    · rename_i hPrime
      exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hPrime.one_lt.le))
    · exact le_rfl
  have weight_sum {N L : ℕ} [NeZero N] (hL : L ≤ N) (S : Set ℕ)
      (hp : ∀ p ∈ S, Nat.Prime p) (a : ℕ) :
      (∑ x : ZMod N, if x.val < L ∧ d * x.val + a ∈ S then ν a N x else 0) =
        (d.totient : ℝ) / (d : ℝ) *
          ∑ j ∈ Finset.range L, if d * j + a ∈ S then Real.log (d * j + a : ℕ) else 0 := by
    let w (j : ℕ) := if d * j + a ∈ S then Real.log (d * j + a : ℕ) else 0
    calc
      _ = ∑ x : ZMod N, if x.val < L then (d.totient : ℝ) / (d : ℝ) * w x.val else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x.val < L
        · by_cases hs : d * x.val + a ∈ S
          · simp [hx, hs, w, ν, hp _ hs]
          · simp [hx, hs, w]
        · simp [hx]
      _ = ∑ j ∈ Finset.range L, (d.totient : ℝ) / (d : ℝ) * w j :=
        sum_below (M := N) hL (fun j => (d.totient : ℝ) / (d : ℝ) * w j)
      _ = _ := (Finset.mul_sum _ _ _).symm

  have bound_per_class : ∀ r ∈ classes, ∃ T : ℕ, ∀ m ≥ T,
      (((F m).filter (fun n => n % d = r)).card : ℝ) ≤ ρ * (((K + 1) * m : ℕ) : ℝ) := by
    intro r hr
    obtain ⟨hrd, hrW, hrEven⟩ := Finset.mem_filter.mp hr
    obtain ⟨a, c, ha, hc, haCo, hcCo, har, u, v, hu₀, hu₁, hv₀, hv₁, huv, hDenseA, hDenseB⟩ :=
      hCompatible d hd hd2W r (Finset.mem_range.mp hrd) hrEven hrW
    obtain ⟨TA, hWeightA⟩ := weighted A hA d a u hdMin ha haCo hu₀ hu₁ hDenseA δ₀ hδ₀
    obtain ⟨TB, hWeightB⟩ := weighted B hB d c v hdMin hc hcCo hv₀ hv₁ hDenseB δ₀ hδ₀
    let T := max 1 (max TA (max TB (max TFour TRestr)))
    refine ⟨T, ?_⟩
    intro m hmT
    have hThresholds :
        1 ≤ m ∧ TA ≤ m ∧ TB ≤ m ∧ TFour ≤ m ∧ TRestr ≤ m := by
      simpa only [T, max_le_iff] using hmT
    rcases hThresholds with ⟨hmOne, hmA, hmB, hmFour, hmRestr⟩
    have hm : 0 < m := (by decide : 0 < 1).trans_le hmOne
    let N := (K + 1) * m
    let L := K * m
    have hL : L ≤ N := Nat.mul_le_mul_right m (Nat.le_succ K)
    have hmL : m ≤ L := by
      simpa only [one_mul] using Nat.mul_le_mul_right m (show 1 ≤ K by omega)
    have hN : 0 < N := hm.trans_le (hmL.trans hL)
    let nzN : NeZero N := ⟨Nat.ne_of_gt hN⟩
    have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
    let f (x : ZMod N) : ℝ := if x.val < L ∧ d * x.val + a ∈ A then ν a N x else 0
    let g (x : ZMod N) : ℝ := if x.val < L ∧ d * x.val + c ∈ B then ν c N x else 0
    have hDomA (x : ZMod N) : 0 ≤ f x ∧ f x ≤ ν a N x := by
      unfold f
      split
      · exact ⟨ν_nonneg _ _ _, le_rfl⟩
      · exact ⟨le_rfl, ν_nonneg _ _ _⟩
    have hDomB (x : ZMod N) : 0 ≤ g x ∧ g x ≤ ν c N x := by
      unfold g
      split
      · exact ⟨ν_nonneg _ _ _, le_rfl⟩
      · exact ⟨le_rfl, ν_nonneg _ _ _⟩
    have hMeanA : (u - δ₀) * (L : ℝ) ≤ ∑ x, f x := by
      have h := hWeightA L (hmA.trans hmL)
      change _ ≤ (∑ x : ZMod N, if x.val < L ∧ d * x.val + a ∈ A then ν a N x else 0)
      rw [weight_sum hL A hA a, div_mul_eq_mul_div, le_div_iff₀ hdR]
      calc
        (u - δ₀) * (L : ℝ) * (d : ℝ) = (u - δ₀) * ((d * L : ℕ) : ℝ) := by
          push_cast
          ring
        _ ≤ _ := h
    have hMeanB : (v - δ₀) * (L : ℝ) ≤ ∑ x, g x := by
      have h := hWeightB L (hmB.trans hmL)
      change _ ≤ (∑ x : ZMod N, if x.val < L ∧ d * x.val + c ∈ B then ν c N x else 0)
      rw [weight_sum hL B hB c, div_mul_eq_mul_div, le_div_iff₀ hdR]
      calc
        (v - δ₀) * (L : ℝ) * (d : ℝ) = (v - δ₀) * ((d * L : ℕ) : ℝ) := by
          push_cast
          ring
        _ ≤ _ := h
    have hMean : 1 + δ₀ ≤ (∑ x, f x) / (N : ℝ) + (∑ x, g x) / (N : ℝ) := by
      rw [← add_div, le_div_iff₀ hNR]
      have huv₀ : 1 + 4 * δ₀ ≤ u + v := by linarith only [huv, hδloss]
      have hkcalc : (1 + δ₀) * ((K : ℝ) + 1) ≤ (u + v - 2 * δ₀) * (K : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_right huv₀ hKR.le
        nlinarith only [hmul, hKδ, hδ₀quarter]
      have hmcalc : (1 + δ₀) * (N : ℝ) ≤ (u + v - 2 * δ₀) * (L : ℝ) := by
        simp only [N, L, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        calc
          _ = ((1 + δ₀) * ((K : ℝ) + 1)) * (m : ℝ) := by ring
          _ ≤ ((u + v - 2 * δ₀) * (K : ℝ)) * (m : ℝ) :=
            mul_le_mul_of_nonneg_right hkcalc (Nat.cast_nonneg m)
          _ = _ := by ring
      linarith only [hmcalc, hMeanA, hMeanB]
    let av (t : ZMod N) : ℝ := (∑ x, f x * g (t - x)) / (N : ℝ)
    let S := (Finset.univ.filter (fun t : ZMod N => av t < δ₀ ^ 3 / 1000))
    have hSmall : (S.card : ℝ) ≤ ρ * (N : ℝ) := by
      exact hTransfer δ₀ ρ hδ₀ hδ₀one hρ hρone N f g (ν a N) (ν c N)
        (fun x => ⟨(hDomA x).1, (hDomA x).2, (hDomB x).1, (hDomB x).2⟩)
        hMean
        (hRestr N (hmRestr.trans (hmL.trans hL)) a ha haCo f hDomA)
        (hRestr N (hmRestr.trans (hmL.trans hL)) c hc hcCo g hDomB)
        (fun t => ⟨hFour N (hmFour.trans (hmL.trans hL)) a ha haCo t,
          hFour N (hmFour.trans (hmL.trans hL)) c hc hcCo t⟩)
    have hmem (n : ℕ) (hn : n ∈ (F m).filter (fun n => n % d = r)) :
        ((n / d - (a + c) / d : ℕ) : ZMod N) ∈ S := by
      obtain ⟨hnF, hnr⟩ := Finset.mem_filter.mp hn
      obtain ⟨hnIco, _, _, hnBad⟩ := Finset.mem_filter.mp hnF
      let t : ZMod N := ((n / d - (a + c) / d : ℕ) : ZMod N)
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ t, ?_⟩
      change av t < δ₀ ^ 3 / 1000
      by_contra! hlarge
      have hav : 0 < av t := (by positivity : 0 < δ₀ ^ 3 / 1000).trans_le hlarge
      obtain ⟨x, y, hxy, hfx, hgy⟩ :=
        positive_convolution f g t (fun x => (hDomA x).1) (fun x => (hDomB x).1) hav
      have hx : x.val < L ∧ d * x.val + a ∈ A := by
        by_contra hh
        simp [f, hh] at hfx
      have hy : y.val < L ∧ d * y.val + c ∈ B := by
        by_contra hh
        simp [g, hh] at hgy
      have hlift := (colorLift d K m a c r n hd hK hm ha hc hnIco hnr har).2.2 x y hxy hx.1 hy.1
      exact hnBad ⟨d * x.val + a, hx.2, d * y.val + c, hy.2, hlift⟩
    have hFinite :
        ((F m).filter (fun n => n % d = r)).card ≤ S.card :=
      color_label_card_le hd hK hm ha hc
        (fun n hn => (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1)
        (fun n hn => (Finset.mem_filter.mp hn).2.trans har.symm) hmem
    have hReal : ((((F m).filter (fun n => n % d = r)).card : ℕ) : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast hFinite
    exact hReal.trans hSmall

  have hEventually : ∀ᶠ m in Filter.atTop, ∀ r ∈ classes,
      (((F m).filter (fun n => n % d = r)).card : ℝ) ≤ ρ * (((K + 1) * m : ℕ) : ℝ) := by
    rw [Filter.eventually_all_finset]
    intro r hr
    exact Filter.eventually_atTop.mpr (bound_per_class r hr)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hEventually
  apply eventual_card_le bad d K W T hd hK hW η hη
  intro m hmT
  have hPart := shell_card_eq W d b (F m) hd hdW hd2 (fun n hn =>
    let hn' := (Finset.mem_filter.mp hn).2
    ⟨hn'.1, hn'.2.1⟩)
  have hSum : ((F m).card : ℝ) =
      ∑ r ∈ classes, (((F m).filter (fun n => n % d = r)).card : ℝ) := by
    exact_mod_cast hPart
  have hClassNat : classes.card ≤ d / W := eligible_card_le W d b hW hdW
  have hDiv : ((d / W : ℕ) : ℝ) = (d : ℝ) / (W : ℝ) := by
    apply (eq_div_iff hWR.ne').mpr
    exact_mod_cast Nat.div_mul_cancel hdW
  have hClass : (classes.card : ℝ) ≤ (d : ℝ) / (W : ℝ) := by
    rw [← hDiv]
    exact_mod_cast hClassNat
  have hCmul : ((K : ℝ) + 1) ≤ 2 * (K : ℝ) := by
    have hKreal : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    linarith
  have hρmul : ρ * ((K : ℝ) + 1) ≤ (η / (8 * (K : ℝ))) * (K : ℝ) := by
    calc
      _ ≤ (η / (16 * (K : ℝ))) * ((K : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hρsmall (by positivity)
      _ ≤ (η / (16 * (K : ℝ))) * (2 * (K : ℝ)) :=
        mul_le_mul_of_nonneg_left hCmul (by positivity)
      _ = _ := by ring
  change ((F m).card : ℝ) ≤ _
  calc
    _ = ∑ r ∈ classes, (((F m).filter (fun n => n % d = r)).card : ℝ) := hSum
    _ ≤ ∑ _r ∈ classes, ρ * (((K + 1) * m : ℕ) : ℝ) :=
      Finset.sum_le_sum (hT m hmT)
    _ = (classes.card : ℝ) * (ρ * (((K + 1) * m : ℕ) : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((d : ℝ) / (W : ℝ)) * (ρ * (((K + 1) * m : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hClass (by positivity)
    _ = ((d : ℝ) * (m : ℝ) / (W : ℝ)) * (ρ * ((K : ℝ) + 1)) := by
      push_cast
      ring
    _ ≤ ((d : ℝ) * (m : ℝ) / (W : ℝ)) * ((η / (8 * (K : ℝ))) * (K : ℝ)) :=
      mul_le_mul_of_nonneg_left hρmul (by positivity)
    _ = _ := by push_cast; ring
