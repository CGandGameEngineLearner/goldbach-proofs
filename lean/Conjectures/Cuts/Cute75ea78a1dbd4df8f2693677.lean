import Mathlib

/- The change from packet length to logarithmic size follows the proof of
PacketSpikesFromLateLevels.lean. The lower cutoff uses the sharper geometric
tail from the first child. The upper cutoff uses Chebyshev's theta bound. -/
open Real Finset

-- child 1 zh: 对任意长度 ℓ，实倍频余弦和高于 ℓ/2 的集合在单位区间内的测度至多为 2(21/25)^ℓ。
-- child 1 en: For every length ℓ the real doubling sum exceeds ℓ/2 on a subset of the unit interval of measure at most 2(21/25)^ℓ.
-- child 2 zh: 只对 j 大于长度的四分之一取整且平方振幅门槛低于 4n² 的深次弧层，证明冻结的单层素数能量预算。
-- child 2 en: Prove the deep-minor prime bin budget only above one quarter of the packet length and below squared height 4n².
theorem Conjectures.Cuts.Cute75ea78a1dbd4df8f2693677
    (hTail : ∀ ℓ : ℕ, (∫ t in (0:ℝ)..1, if (ℓ:ℝ)/2 < ∑ i ∈ Finset.range ℓ, Real.cos (2*Real.pi*(2:ℝ)^(i+1)*t) then (1:ℝ) else 0) ≤ 2*(21/25:ℝ)^ℓ)
    (hMiddle : ∃ N : ℕ, ∀ n ≥ N, Even n →
  let ℓ := max 1 (Nat.log 2 n / 2)
  let Q := (Nat.log 2 (n+2))^2
  let A := fun r : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤r ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/q| ≤ (r:ℝ)/(q*n)}
  let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0
  let f := fun t : ℝ => ‖∑ k ∈ Finset.range (n+1), ((w k - (if k^3≤n then w k else 0):ℝ):ℂ) *
    Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I)‖^2
  let u := 1+Real.log (n:ℝ)
  ∀ j : ℕ, ℓ/4 < j → j < Nat.log 2 n+3 →
    let y := (2:ℝ)^j*((n:ℝ)*u^4)
    y < 4*(n:ℝ)^2 →
    y * (∫ t in (0:ℝ)..1, ({x : ℝ | x ∉ A Q ∧ (1:ℝ)/2 < (∑ i ∈ Finset.range ℓ, Real.cos (2*Real.pi*(2:ℝ)^(i+1)*x))/(ℓ:ℝ) ∧ x ∉ A (Q^2) ∧ y < f x ∧ f x ≤ 2*y}).indicator (fun _ => (1:ℝ)) t) ≤ (n:ℝ)/(100000*u^2)) : (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2; let T := fun n : ℕ => (n:ℝ)*(1+Real.log (n:ℝ))^4; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → ∀ j : ℕ, L n / 16 ≤ j → j < Nat.log 2 n + 3 → let y := (2:ℝ)^j*T n; y * m ((B n \ (W n (fun _ => True))) ∩ {t : ℝ | y < F n t ∧ F n t ≤ 2*y}) (fun _ => (1:ℝ)) ≤ (n:ℝ)/(100000*(1+Real.log (n:ℝ))^2)) := by
  classical
  let len (n : ℕ) := max 1 (Nat.log 2 n / 2)
  let waveSum (m : ℕ) (t : ℝ) := ∑ j ∈ range m, cos (2*Real.pi*(2:ℝ)^(j+1)*t)
  let pw (k : ℕ) : ℝ := if Nat.Prime k then log (k:ℝ) else 0

  have primeCap (n : ℕ) (t : ℝ) :
      ‖∑ k ∈ range (n+1), ((pw k - (if k^3≤n then pw k else 0):ℝ):ℂ)*
        Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I)‖^2 ≤ 4*(n:ℝ)^2 := by
    have hn (k : ℕ) : 0 ≤ pw k := by
      unfold pw
      split_ifs with h
      · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
      · exact le_rfl
    have hsum : (∑ k ∈ range (n+1), pw k) = Chebyshev.theta n := by
      rw [Chebyshev.theta_eq_sum_Icc]; simp only [Nat.floor_natCast]
      rw [Finset.sum_filter, ←Nat.range_succ_eq_Icc_zero]
    have hlog : log 4 ≤ 2 := by
      rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
      norm_num only [Nat.cast_ofNat] 
      linarith [Real.log_two_lt_d9]
    have hmag : ‖∑ k ∈ range (n+1), ((pw k - (if k^3≤n then pw k else 0):ℝ):ℂ)*
        Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I)‖ ≤ 2*n := by
      calc
        _ ≤ ∑ k ∈ range (n+1), ‖((pw k - (if k^3≤n then pw k else 0):ℝ):ℂ)*
              Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I)‖ := norm_sum_le ..
        _ ≤ ∑ k ∈ range (n+1), pw k := by
          apply sum_le_sum; intro k _
          rw [norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
          by_cases h : k^3≤n <;> simp [h,hn k,abs_of_nonneg (hn k)]
        _ ≤ _ := by
          rw [hsum]
          exact (Chebyshev.theta_le_log4_mul_x (by positivity)).trans
            (mul_le_mul_of_nonneg_right hlog (by positivity))
    exact (pow_le_pow_left₀ (norm_nonneg _) hmag 2).trans_eq (by ring)

  have area {m : ℕ} (E : Set ℝ) (h : ∀ t ∈ E, (m:ℝ)/2 < waveSum m t)
      (hm : (∫ t in (0:ℝ)..1, if (m:ℝ)/2 < waveSum m t then (1:ℝ) else 0) ≤ 2*(21/25:ℝ)^m) :
      (∫ t in (0:ℝ)..1, E.indicator (fun _ => (1:ℝ)) t) ≤ 2*(21/25:ℝ)^m := by
    let A := {t : ℝ | (m:ℝ)/2 < waveSum m t}
    have hc : Continuous (waveSum m) := by unfold waveSum; fun_prop
    have ha : MeasurableSet A := (isOpen_lt continuous_const hc).measurableSet
    have hi : IntervalIntegrable (A.indicator (fun _ => (1:ℝ))) MeasureTheory.volume (0:ℝ) 1 :=
      ⟨intervalIntegrable_const.1.indicator ha, intervalIntegrable_const.2.indicator ha⟩
    change (∫ t in (0:ℝ)..1, A.indicator (fun _ => (1:ℝ)) t) ≤ _ at hm
    by_cases he : IntervalIntegrable (E.indicator (fun _ => (1:ℝ))) MeasureTheory.volume (0:ℝ) 1
    · apply le_trans _ hm
      apply intervalIntegral.integral_mono_on (by norm_num) he hi
      intro t _
      by_cases ht : t∈E
      · have ht' : t∈A := h t ht
        simp [ht,ht']
      · by_cases h' : t∈A <;> simp [ht,h']
    · rw [intervalIntegral.integral_undef he]; positivity

  have rangeBudget : ∃ N : ℕ, ∀ n≥N, ∀ j : ℕ, j ≤ len n / 4 →
      (2:ℝ)^j*(1+log (n:ℝ))^6 * (2*(21/25:ℝ)^(len n)) ≤ 1/100000 := by
    let r : ℝ := 2*(21/25:ℝ)^4
    have ht := tendsto_pow_const_mul_const_pow_of_lt_one 6 (r:=r) (by norm_num [r]) (by norm_num [r])
    obtain ⟨M,hM⟩ := Filter.eventually_atTop.mp (ht.eventually_lt_const
      (by norm_num : (0:ℝ)<1/(200000*35^6)))
    refine ⟨2^(8*(M+1)),?_⟩
    intro n hN j hj
    have hn : 1 ≤ n := (Nat.one_le_pow _ _ (by decide : 0<2)).trans hN
    have hn0 : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
    have hlog := Nat.le_log_of_pow_le (by decide : 1<2) hN
    let k := len n / 4
    have hk : M+1 ≤ k := by unfold k len; omega
    have hL : 4*k ≤ len n := by unfold k; omega
    have hL' : len n ≤ 4*k+3 := by unfold k; omega
    have hn' : (n:ℝ) < (2:ℝ)^(Nat.log 2 n+1) := by exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1<2) n
    have hln := Real.log_le_log hn0 hn'.le
    rw [Real.log_pow] at hln
    have hlen : Nat.log 2 n+1 ≤ 2*(len n)+2 := by unfold len; omega
    have h35 : Nat.log 2 n+2 ≤ 35*k := by omega
    have hu : 1+log (n:ℝ) ≤ 35*(k:ℝ) := by
      have h1 := mul_le_mul_of_nonneg_left (le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num : (0.6931471808:ℝ)<1))) (Nat.cast_nonneg (α:=ℝ) (Nat.log 2 n+1))
      have h2 : ((Nat.log 2 n+2 : ℕ):ℝ) ≤ 35*(k:ℝ) := by exact_mod_cast h35
      push_cast at hln h1 h2
      linarith
    have hnon : 0≤1+log (n:ℝ) := by linarith [Real.log_nonneg (by exact_mod_cast hn : (1:ℝ)≤n)]
    have hp : (21/25:ℝ)^(len n) ≤ (21/25:ℝ)^(4*k) := pow_le_pow_of_le_one (by norm_num) (by norm_num) hL
    have h2 : (2:ℝ)^j ≤ (2:ℝ)^k := pow_le_pow_right₀ (by norm_num) hj
    calc
      _ ≤ (2:ℝ)^k*(35*(k:ℝ))^6*(2*(21/25:ℝ)^(4*k)) := by gcongr
      _ = (2*35^6)*((k:ℝ)^6*r^k) := by dsimp [r]; rw [mul_pow 2,←pow_mul]; ring
      _ ≤ _ := by have hb := hM k (by omega); linarith only [hb]
  intro w E S Q arcs low high L K B W F T m
  obtain ⟨N,hN⟩ := hMiddle
  obtain ⟨M,hM⟩ := rangeBudget
  refine ⟨max 1 (max N M),?_⟩
  intro n hn he j _ hj
  let y := (2:ℝ)^j*T n
  let D := (B n \ (W n (fun _ => True))) ∩ {t : ℝ | y < F n t ∧ F n t ≤ 2*y}
  change y * m D (fun _ => (1:ℝ)) ≤ _
  by_cases hl : j ≤ L n / 4
  · let ℓ := L n
    have hs : 0 < (ℓ:ℝ) := by
      have hp : 0 < ℓ := by change 0 < max 1 _; omega
      exact_mod_cast hp
    have bound := area D (m:=ℓ) (fun t ht => by
      have ht' := ht.1.1.2
      change (1:ℝ)/2 < waveSum ℓ t / ℓ at ht'
      have z := (lt_div_iff₀ hs).mp ht'
      linarith) (hTail ℓ)
    have b := hM n (by omega) j hl
    let u := 1+Real.log (n:ℝ)
    have hu : 0 < u := by
      have h1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
      dsimp [u]; linarith [Real.log_nonneg h1]
    change (2:ℝ)^j*u^6*(2*(21/25:ℝ)^ℓ) ≤ 1/100000 at b
    change m D (fun _ => (1:ℝ)) ≤ _ at bound
    change (2:ℝ)^j*((n:ℝ)*u^4)*_ ≤ (n:ℝ)/(100000*u^2)
    apply (le_div_iff₀ (by positivity)).mpr
    have b' := mul_le_mul_of_nonneg_right bound (show 0 ≤ (2:ℝ)^j*u^6 by positivity)
    have bb : m D (fun _ => (1:ℝ)) * ((2:ℝ)^j*u^6) ≤ 1/100000 := b'.trans (by linarith only [b])
    have e := mul_le_mul_of_nonneg_left bb (Nat.cast_nonneg (α:=ℝ) n)
    linarith only [e]
  · by_cases hy : y < 4*(n:ℝ)^2
    · have hm := hN n (by omega) he j (Nat.lt_of_not_ge hl) hj hy
      let V := fun r : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤r ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/q| ≤ (r:ℝ)/(q*n)}
      have hW : W n (fun _ => True) = V ((Q n)^2) := by
        ext t
        simp only [W,V, Set.mem_ofPred_eq,true_and,Nat.cast_pow]
      have hd : D = {t : ℝ | t ∉ V (Q n) ∧ (1:ℝ)/2 < K n t ∧ t ∉ V ((Q n)^2) ∧ y < F n t ∧ F n t ≤ 2*y} := by
        ext t
        simp only [D,Set.mem_inter_iff,Set.mem_sdiff,Set.mem_ofPred_eq,hW]
        change (((t ∉ V (Q n) ∧ (1:ℝ)/2 < K n t) ∧ t ∉ V ((Q n)^2)) ∧ _) ↔ _
        tauto
      rw [hd]
      exact hm
    · have em : D = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro t h
        have cap : F n t ≤ 4*(n:ℝ)^2 := primeCap n t
        exact (not_lt_of_ge (le_trans cap (le_of_not_gt hy))) h.2.1
      simp [em,m]
      positivity
