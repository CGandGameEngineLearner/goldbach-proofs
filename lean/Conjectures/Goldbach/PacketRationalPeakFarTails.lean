import Mathlib

namespace Conjectures.Goldbach.PacketRationalPeakFarTails_aux

private def gridQ (n : ℕ) := (Nat.log 2 (n+2))^2
private noncomputable def lorentz (r c t : ℝ) := 1/(r^2+(t-c)^2)

private theorem lorentzContinuous {r : ℝ} (hr : 0 < r) (c : ℝ) : Continuous (lorentz r c) := by
  unfold lorentz
  fun_prop (disch := intro t; positivity)

/-- The integral is bounded uniformly in the location of the center, including endpoints. -/
private theorem lorentzIntegral {r : ℝ} (hr : 0 < r) (c : ℝ) :
    (∫ t in (0:ℝ)..1, lorentz r c t) ≤ Real.pi/r := by
  let F := fun t : ℝ => Real.arctan ((t-c)/r)/r
  have deriv (t : ℝ) : HasDerivAt F (lorentz r c t) t := by
    have h := (((Real.hasDerivAt_arctan ((t-c)/r)).comp t
      (((hasDerivAt_id t).sub_const c).div_const r)).div_const r)
    have eq : lorentz r c t = 1 / (1 + ((t-c)/r)^2) * (1/r) / r := by
      unfold lorentz
      field_simp <;> ring
    rw [eq]
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => deriv t)
    ((lorentzContinuous hr c).intervalIntegrable ..)]
  dsimp [F]
  rw [← sub_div]
  apply div_le_div_of_nonneg_right _ hr.le
  have ha := Real.arctan_lt_pi_div_two ((1-c)/r)
  have hb := Real.neg_pi_div_two_lt_arctan ((0-c)/r)
  linarith

private theorem onRegion {s : Set ℝ} (hs : MeasurableSet s) {f : ℝ → ℝ} (hf : Continuous f) :
    IntervalIntegrable (s.indicator f) MeasureTheory.volume (0:ℝ) 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
    (hf.intervalIntegrable (μ := MeasureTheory.volume) 0 1)).indicator hs

private noncomputable def integralOn (s : Set ℝ) (f : ℝ → ℝ) := ∫ t in (0:ℝ)..1, s.indicator f t

private theorem totientSquare (q : ℕ) :
    q ≤ 2*q.totient^2 ∧ (¬ 2 ∣ q → q ≤ q.totient^2) := by
  induction q using Nat.strong_induction_on with
  | ind q ih =>
    rcases eq_or_ne q 0 with rfl | h0
    · simp
    rcases eq_or_ne q 1 with rfl | h1
    · simp
    obtain ⟨p,hp,m,rfl⟩ := Nat.exists_prime_and_dvd h1
    have hp2 := hp.two_le
    have hm : 0 < m := Nat.pos_of_ne_zero (fun hz => h0 (by simp [hz]))
    have lt : m < p*m := by nlinarith [Nat.mul_le_mul_right m hp2]
    obtain ⟨all,odd⟩ := ih m lt
    have lift (f c : ℕ) (eq : (p*m).totient = f*m.totient) (hf : p ≤ f^2)
        (h : m ≤ c*m.totient^2) : p*m ≤ c*(p*m).totient^2 := by
      calc
        _ ≤ f^2*(c*m.totient^2) := Nat.mul_le_mul hf h
        _ = _ := by rw [eq]; ring
    have both (f : ℕ) (eq : (p*m).totient = f*m.totient) (hf : p ≤ f^2) :
        p*m ≤ 2*(p*m).totient^2 ∧ (¬2 ∣ p*m → p*m ≤ (p*m).totient^2) := by
      refine ⟨lift f 2 eq hf all, ?_⟩
      intro hn
      have hodd := odd (fun h => hn (dvd_mul_of_dvd_right h p))
      simpa only [one_mul] using lift f 1 eq hf (by simpa using hodd)
    by_cases divides : p ∣ m
    · exact both p (Nat.totient_mul_of_dvd divides) (by nlinarith [Nat.le_mul_self p])
    · have eq := Nat.totient_mul_of_prime_of_not_dvd hp divides
      by_cases two : p=2
      · subst p
        simp only [Nat.reduceSub,one_mul] at eq
        constructor
        · rw [eq]; exact Nat.mul_le_mul_left 2 (odd divides)
        · simp
      · apply both (p-1) eq
        have e : p = (p-1)+1 := by omega
        have g : 2 ≤ p-1 := by omega
        nlinarith [Nat.mul_le_mul_right (p-1) g]

private theorem totientSum (m : ℕ) :
    (∑ j ∈ Finset.range m, 1/((j+1).totient:ℝ)) ≤ 4*Real.sqrt (m:ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    let u := Real.sqrt (m:ℝ)
    let v := Real.sqrt ((m:ℝ)+1)
    let f : ℝ := (m+1).totient
    have fp : 0 < f := by dsimp [f]; exact_mod_cast (Nat.totient_pos.mpr (Nat.succ_pos m))
    have hb : (m:ℝ)+1 ≤ 2*f^2 := by dsimp [f]; exact_mod_cast (totientSquare (m+1)).1
    have hu : u^2 = (m:ℝ) := Real.sq_sqrt (by positivity)
    have hv : v^2 = (m:ℝ)+1 := Real.sq_sqrt (by positivity)
    have uv : u ≤ v := Real.sqrt_le_sqrt (by linarith)
    have pos : 0 ≤ v := Real.sqrt_nonneg _
    have v2 : v ≤ 2*f := by
      by_contra! hh
      have h := mul_pos (sub_pos.mpr hh) (show 0<v+2*f by linarith)
      nlinarith only [hb,hv,h,sq_nonneg f]
    have bound : v+u ≤ 4*f := by linarith
    have step : 1/f ≤ 4*(v-u) := by
      apply (div_le_iff₀ fp).mpr
      nlinarith only [mul_le_mul_of_nonneg_right bound (sub_nonneg.mpr uv),hu,hv]
    rw [Finset.sum_range_succ,Nat.cast_succ]
    change _ ≤ 4*v
    linarith only [ih,step]

private noncomputable def profile (n q : ℕ) (c t : ℝ) :=
  4*(n:ℝ)^2/((q.totient:ℝ)^2*(1+((n:ℝ)*(t-c))^2))
private noncomputable def farPeak (n q : ℕ) (a : ℕ) :=
  integralOn {t : ℝ | (gridQ n:ℝ)^2/(n:ℝ) < |t-(a:ℝ)/(q:ℝ)|} (profile n q ((a:ℝ)/(q:ℝ)))

private theorem peakOutside (n q : ℕ) (hq : 0<q) (c r : ℝ) (hr : 0<r) :
    integralOn {t : ℝ | r < |t-c|} (profile n q c) ≤
      (8/(q.totient:ℝ)^2)*(Real.pi/r) := by
  let f : ℝ := q.totient
  let s := {t : ℝ | r < |t-c|}
  have fp : 0<f := by dsimp [f]; exact_mod_cast (Nat.totient_pos.mpr hq)
  have hs : MeasurableSet s :=
    (isOpen_lt continuous_const (continuous_abs.comp (continuous_id.sub continuous_const))).measurableSet
  have hd : Continuous (fun t : ℝ => f^2*(1+((n:ℝ)*(t-c))^2)) := by fun_prop
  have hc : Continuous (profile n q c) :=
    (continuous_const : Continuous (fun _ : ℝ => 4*(n:ℝ)^2)).div hd
      (fun t => ne_of_gt (mul_pos (by positivity) (by positivity)))
  calc
    _ ≤ ∫ t in (0:ℝ)..1, (8/f^2)*lorentz r c t := by
      apply intervalIntegral.integral_mono_on (by norm_num) (onRegion hs hc)
        (((lorentzContinuous hr c).intervalIntegrable ..).const_mul _)
      intro t _
      change s.indicator (profile n q c) t ≤ _
      by_cases ht : t ∈ s
      · rw [Set.indicator_of_mem ht]
        have d : r ≤ |t-c| := le_of_lt ht
        have sq := pow_le_pow_left₀ hr.le d 2
        rw [sq_abs] at sq
        have bound : (n:ℝ)^2/(1+((n:ℝ)*(t-c))^2) ≤ 2/(r^2+(t-c)^2) := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          nlinarith only [mul_le_mul_of_nonneg_left sq (sq_nonneg (n:ℝ))]
        calc
          profile n q c t = (4/f^2)*((n:ℝ)^2/(1+((n:ℝ)*(t-c))^2)) := by unfold profile; dsimp [f]; field_simp <;> ring
          _ ≤ (4/f^2)*(2/(r^2+(t-c)^2)) := mul_le_mul_of_nonneg_left bound (by positivity)
          _ = _ := by unfold lorentz; ring
      · rw [Set.indicator_of_notMem ht]; unfold lorentz; positivity
    _ = (8/f^2)*(∫ t in (0:ℝ)..1, lorentz r c t) := intervalIntegral.integral_const_mul ..
    _ ≤ (8/f^2)*(Real.pi/r) := mul_le_mul_of_nonneg_left (lorentzIntegral hr c) (by positivity)

private theorem singleFarPeak (n q : ℕ) (hn : 0<n) (hq : 0<q) (hQ : 0<gridQ n) (a : ℕ) :
    farPeak n q a ≤ (8*Real.pi*((n:ℝ)/(gridQ n:ℝ)^2))/(q.totient:ℝ)^2 := by
  have hr : 0 < (gridQ n:ℝ)^2/(n:ℝ) := by positivity
  apply (peakOutside n q hq ((a:ℝ)/(q:ℝ)) _ hr).trans_eq
  field_simp <;> ring

private def numerators (q : ℕ) := (Finset.range (q+1)).filter (fun a => Nat.Coprime a q)

private theorem countNumerators (q : ℕ) (hq : 0<q) : (numerators q).card ≤ 2*q.totient := by
  have card : ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
    simp only [Nat.totient_eq_card_coprime,Nat.coprime_comm]
  have sub : numerators q ⊆ insert q ((Finset.range q).filter (fun a => Nat.Coprime a q)) := by
    intro a ha
    obtain ⟨hr,hc⟩ := Finset.mem_filter.mp ha
    rcases eq_or_ne a q with rfl | h
    · simp
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hr; omega),hc⟩)
  have bound := (Finset.card_le_card sub).trans (Finset.card_insert_le ..)
  rw [card] at bound
  have hp := Nat.totient_pos.mpr hq
  omega

theorem farTailQuantitative (n : ℕ) (hn : 0<n) (hQ : 0<gridQ n) :
    (∑ q ∈ Finset.Icc 1 ((gridQ n)^2), ∑ a ∈ numerators q, farPeak n q a) ≤
      64*Real.pi*(n:ℝ)/(gridQ n:ℝ) := by
  let Q := gridQ n
  let C := 8*Real.pi*((n:ℝ)/(Q:ℝ)^2)
  have pos : 0≤C := by dsimp [C]; positivity
  have bb (q : ℕ) (hq : 0<q) : (∑ a ∈ numerators q, farPeak n q a) ≤ (2*C)*(1/(q.totient:ℝ)) := by
    have hf : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
    calc
      _ ≤ ∑ _a ∈ numerators q, C/(q.totient:ℝ)^2 := Finset.sum_le_sum fun a _ => singleFarPeak n q hn hq hQ a
      _ = ((numerators q).card:ℝ)*(C/(q.totient:ℝ)^2) := by simp
      _ ≤ (2*(q.totient:ℝ))*(C/(q.totient:ℝ)^2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast countNumerators q hq
      _ = _ := by field_simp <;> ring
  have index : Finset.Icc 1 (Q^2) = (Finset.range (Q^2)).map (addRightEmbedding 1) := by
    ext k
    simp only [Finset.mem_Icc,Finset.mem_map,Finset.mem_range,addRightEmbedding_apply]
    constructor
    · intro h; exact ⟨k-1,by omega,by omega⟩
    · rintro ⟨j,h,rfl⟩; omega
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 (Q^2), (2*C)*(1/(q.totient:ℝ)) :=
      Finset.sum_le_sum fun q h => bb q (Finset.mem_Icc.mp h).1
    _ = (2*C)*(∑ j ∈ Finset.range (Q^2), 1/((j+1).totient:ℝ)) := by
      rw [index,← Finset.mul_sum,Finset.sum_map]; rfl
    _ ≤ (2*C)*(4*Real.sqrt ((Q^2:ℕ):ℝ)) := mul_le_mul_of_nonneg_left (totientSum (Q^2)) (by positivity)
    _ = _ := by
      push_cast
      rw [Real.sqrt_sq (Nat.cast_nonneg _)]
      dsimp [C,Q]; field_simp <;> ring

theorem farTails (ε : ℝ) (hε : 0<ε) : ∃ N : ℕ, ∀ n ≥ N,
    (∑ q ∈ Finset.Icc 1 ((gridQ n)^2), ∑ a ∈ numerators q, farPeak n q a) ≤ ε*(n:ℝ) := by
  obtain ⟨M,hM⟩ := exists_nat_ge (64*Real.pi/ε)
  let B := max 1 M
  refine ⟨2^B, ?_⟩
  intro n hn
  have hn' : 0<n := lt_of_lt_of_le (by positivity : 0<2^B) hn
  have hb : B ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (by omega)
  have hq : B ≤ gridQ n := by unfold gridQ; nlinarith [Nat.le_mul_self (Nat.log 2 (n+2))]
  have hQ : 0<gridQ n := lt_of_lt_of_le (by dsimp [B]; omega) hq
  apply (farTailQuantitative n hn' hQ).trans
  have hM' : 64*Real.pi/ε ≤ (gridQ n:ℝ) := hM.trans (by exact_mod_cast (le_trans (le_max_right 1 M) hq))
  apply (div_le_iff₀ (by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ hε).mp hM') (Nat.cast_nonneg (α := ℝ) n)
  linarith only [hh]

private theorem profile_eta (n q : ℕ) (c : ℝ) :
    profile n q c = fun t => 4*(n:ℝ)^2/((q.totient:ℝ)^2*(1+((n:ℝ)*(t-c))^2)) := rfl

private theorem integralOn_eta (s : Set ℝ) (f : ℝ → ℝ) :
    integralOn s f = intervalIntegral (Set.indicator s f) (0:ℝ) 1 MeasureTheory.volume := rfl


theorem packetFarTails (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, ∀ n ≥ N,
    (∑ q ∈ Finset.Icc 1 (((Nat.log 2 (n+2))^2)^2),
      ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
        intervalIntegral
          (Set.indicator {t : ℝ | (((Nat.log 2 (n+2))^2 : ℕ) : ℝ)^2/(n:ℝ) < |t-(a:ℝ)/(q:ℝ)|}
            (fun t => 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2*(1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2))))
          (0:ℝ) 1 MeasureTheory.volume) ≤ ε*(n:ℝ) := by
  simpa only [gridQ, numerators, farPeak, integralOn_eta, profile_eta] using farTails ε hε

end Conjectures.Goldbach.PacketRationalPeakFarTails_aux

theorem Conjectures.Goldbach.PacketRationalPeakFarTails : let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), m {t : ℝ | (Q n:ℝ)^2/(n:ℝ) < |t-(a:ℝ)/(q:ℝ)|} (fun t => 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2*(1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)))) ≤ ε*(n:ℝ) := by
  intro Q m ε hε
  simpa only [Q, m] using
    Conjectures.Goldbach.PacketRationalPeakFarTails_aux.packetFarTails ε hε
