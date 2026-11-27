import Conjectures.Goldbach.EstermannAlmostAllPolylog

/-! Endpoint and multiplicity bounds for the published binary-shift union.
The ordinary exceptional count is an explicit input to the exponent transfer. -/

namespace Conjectures.Goldbach.BinaryShiftExceptionalTransfer

open Finset Filter Real
open scoped Topology

def reps (n : ℕ) := ((range (n+1)).filter (fun p => p.Prime ∧ (n-p).Prime)).card

def ordinary (X : ℕ) := (range (X+1)).filter (fun n => 4 ≤ n ∧ Even n ∧ reps n = 0)

def band (X : ℕ) := Icc 1 (Nat.log 2 X / 2)

def unionBad (X : ℕ) := (Ico X (2*X)).filter (fun n => Even n ∧
  0 < ((band X).filter (fun e => reps (n-2^e)=0)).card)

private theorem shift_size {X e : ℕ} (hX : 8 ≤ X) (he : e ∈ band X) :
    2^e+4 ≤ X ∧ Even (2^e) := by
  obtain ⟨he1,he2⟩ := mem_Icc.mp he
  have hpow := Nat.pow_log_le_self 2 (show X ≠ 0 by omega)
  have he' : e+1 ≤ Nat.log 2 X := by omega
  have htwice : 2*(2^e) ≤ X := by
    simpa [pow_succ, Nat.mul_comm] using
      (Nat.pow_le_pow_right (by decide : 0 < 2) he').trans hpow
  exact ⟨by omega, Even.pow_of_ne_zero (by decide : Even (2 : ℕ)) (by omega)⟩

/-- Every missed target is a translate of an ordinary exception. The finite
bound includes all admissible exponents, the parity and the low endpoint four. -/
theorem card_union_le {X : ℕ} (hX : 8 ≤ X) :
    (unionBad X).card ≤ (Nat.log 2 X / 2) * (ordinary (2*X)).card := by
  classical
  let O := ordinary (2*X)
  have hs : unionBad X ⊆ (band X).biUnion (fun e => O.image (fun m => m+2^e)) := by
    intro n hn
    obtain ⟨hI,hEven,hw⟩ := mem_filter.mp hn
    obtain ⟨e,he⟩ := card_pos.mp hw
    obtain ⟨he,hr⟩ := mem_filter.mp he
    have hs := shift_size hX he
    obtain ⟨hn₁,hn₂⟩ := mem_Ico.mp hI
    have hle : 2^e ≤ n := by omega
    have hnsub := Nat.sub_le n (2^e)
    refine mem_biUnion.mpr ⟨e,he,mem_image.mpr ⟨n-2^e,?_,by omega⟩⟩
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),by omega,
      (Nat.even_sub hle).2 (iff_of_true hEven hs.2),hr⟩
  calc
    (unionBad X).card ≤ _ := card_le_card hs
    _ ≤ ∑ e ∈ band X, (O.image (fun m => m+2^e)).card := card_biUnion_le
    _ ≤ ∑ _e ∈ band X, O.card := sum_le_sum (fun _ _ => card_image_le)
    _ = _ := by simp [band, O]

/-- The shift by two embeds every ordinary exception from the interior of
the dyadic block in the shifted failure set. -/
theorem interior_le_card_union {X : ℕ} (hX : 8 ≤ X) :
    (((Ico X (2*X-2)).filter (fun n => Even n ∧ reps n=0)).card) ≤ (unionBad X).card := by
  let s := (Ico X (2*X-2)).filter (fun n => Even n ∧ reps n=0)
  have hlog : 2 ≤ Nat.log 2 X := (Nat.le_log_iff_pow_le (by decide) (by omega)).2 (by omega)
  have hf : Set.MapsTo (fun m : ℕ => m+2) s (unionBad X) := by
    intro m hm
    obtain ⟨hi,hev,hr⟩ := mem_filter.mp hm
    obtain ⟨h₁,h₂⟩ := mem_Ico.mp hi
    change m+2 ∈ unionBad X
    refine mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,hev.add (by decide),card_pos.mpr ?_⟩
    refine ⟨1,mem_filter.mpr ⟨mem_Icc.mpr ⟨by decide,by omega⟩,?_⟩⟩
    simpa using hr
  exact card_le_card_of_injOn _ hf (fun _ _ _ _ h => Nat.add_right_cancel h)

/-- A classical bound with any exponent below 4/5 suffices for the exact
frozen power inequality, including an arbitrary fixed implied constant. -/
theorem of_ordinary_power {θ C : ℝ} (hθ : θ < 4/5) (hC : 0 < C)
    (hb : ∀ᶠ X : ℕ in atTop, ((ordinary X).card : ℝ) ≤ C*(X : ℝ)^θ) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (unionBad X).card^5 ≤ X^4 := by
  let δ := (4/5 : ℝ)-θ
  have hδ : 0 < δ := sub_pos.mpr hθ
  let K := C*(2 : ℝ)^θ / Real.log 2
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  have hlim : Tendsto (fun X : ℕ => K * (Real.log (X : ℝ) / (X : ℝ)^δ)) atTop (nhds 0) := by
    simpa using ((isLittleO_log_rpow_atTop hδ).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul K
  obtain ⟨N,hN⟩ := eventually_atTop.1 hb
  apply eventually_atTop.1
  filter_upwards [eventually_ge_atTop (max N 8),
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with X hX hsmall
  have h8 : 8 ≤ X := (le_max_right ..).trans hX
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hpow := hN (2*X) (by omega)
  push_cast at hpow
  rw [Real.mul_rpow (by norm_num) hx.le] at hpow
  have hlog : (↑(Nat.log 2 X / 2) : ℝ) ≤ Real.log X / Real.log 2 :=
    (Nat.cast_le.mpr (Nat.div_le_self _ _)).trans (Real.natLog_le_logb X 2)
  have hcard : ((unionBad X).card : ℝ) ≤ ((Nat.log 2 X / 2 : ℕ) : ℝ) * (ordinary (2*X)).card :=
    by exact_mod_cast card_union_le h8
  have hpoint : ((unionBad X).card : ℝ) ≤ (X : ℝ)^(4/5 : ℝ) := calc
    _ ≤ (Real.log X / Real.log 2) * (C*((2 : ℝ)^θ * (X : ℝ)^θ)) :=
      hcard.trans (mul_le_mul hlog hpow (Nat.cast_nonneg _) (by positivity))
    _ = (K*Real.log X) * (X : ℝ)^θ := by dsimp [K]; ring
    _ ≤ (X : ℝ)^δ * (X : ℝ)^θ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx.le _)
      rw [mul_div_assoc'] at hsmall
      exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hx δ)).1 hsmall |>.le).trans_eq (one_mul _)
    _ = (X : ℝ)^(4/5 : ℝ) := by rw [← Real.rpow_add hx]; congr 1; dsimp [δ]; ring
  have hf := pow_le_pow_left₀ (Nat.cast_nonneg _) hpoint 5
  rw [← Real.rpow_mul_natCast hx.le] at hf
  norm_num at hf
  exact_mod_cast hf

/-- Unconditionally, the verified Estermann estimate survives simultaneous
shifting, with the same arbitrary logarithmic saving. -/
theorem all_shifts_polylog (A : ℝ) (hA : 0 < A) : ∃ X₀ : ℕ, ∀ X ≥ X₀,
    ((unionBad X).card : ℝ) ≤ (X : ℝ) * (Real.log X)^(-A) := by
  obtain ⟨N,hN⟩ := Conjectures.Goldbach.EstermannAlmostAllPolylog.1 (A+2) (by linarith)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogAtTop : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply eventually_atTop.1
  filter_upwards [eventually_ge_atTop (max N 8), hlogAtTop.eventually (eventually_ge_atTop (2/Real.log 2))]
    with X hX hlarge
  have h8 : 8 ≤ X := (le_max_right ..).trans hX
  have hx : 1 < (X : ℝ) := by exact_mod_cast (show 1 < X by omega)
  have hlog : 0 < Real.log X := Real.log_pos hx
  have hmon : Real.log X ≤ Real.log (2*(X : ℝ)) := Real.log_le_log (by positivity) (by linarith)
  have ho : ((ordinary (2*X)).card : ℝ) ≤ (2*(X : ℝ)) * (Real.log (2*X))^(-(A+2)) := by
    have raw := hN (2*X) (by omega)
    push_cast at raw ⊢
    unfold ordinary reps
    convert raw using 1
  have hd : ((Nat.log 2 X / 2 : ℕ) : ℝ) ≤ Real.log X / Real.log 2 :=
    (Nat.cast_le.mpr (Nat.div_le_self _ _)).trans (Real.natLog_le_logb X 2)
  have hfall := Real.rpow_le_rpow_of_nonpos hlog hmon (show -(A+2) ≤ 0 by linarith)
  have hsquare : (2/Real.log 2) * Real.log X ≤ (Real.log X)^2 := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hlarge hlog.le
  have hcard : ((unionBad X).card : ℝ) ≤ ((Nat.log 2 X / 2 : ℕ) : ℝ) * (ordinary (2*X)).card :=
    by exact_mod_cast card_union_le h8
  calc
    _ ≤ (Real.log X/Real.log 2)*(2*(X : ℝ)*(Real.log X)^(-(A+2))) :=
      hcard.trans (mul_le_mul hd (ho.trans (mul_le_mul_of_nonneg_left hfall (by positivity)))
        (Nat.cast_nonneg _) (by positivity))
    _ = (X : ℝ) * (((2/Real.log 2)*Real.log X) * (Real.log X)^(-(A+2))) := by ring
    _ ≤ (X : ℝ) * ((Real.log X)^2 * (Real.log X)^(-(A+2))) := by gcongr
    _ = _ := by
      rw [← Real.rpow_natCast (Real.log X) 2, ← Real.rpow_add hlog]
      congr 2; ring

end Conjectures.Goldbach.BinaryShiftExceptionalTransfer

open Conjectures.Goldbach.BinaryShiftExceptionalTransfer in
/-- The logarithmic bound for the frozen union and its exact power transfer. -/
theorem Conjectures.Goldbach.BinaryShiftExceptionalTransfer :
    (∀ A : ℝ, 0 < A → ∃ X₀ : ℕ, ∀ X ≥ X₀, ((unionBad X).card : ℝ) ≤
      (X : ℝ)*(Real.log X)^(-A)) ∧
    (∀ θ C : ℝ, θ < 4/5 → 0 < C → (∀ᶠ X : ℕ in Filter.atTop,
      ((ordinary X).card : ℝ) ≤ C*(X : ℝ)^θ) →
      ∃ X₀ : ℕ, ∀ X ≥ X₀, (unionBad X).card^5 ≤ X^4) :=
    ⟨all_shifts_polylog, fun _ _ => of_ordinary_power⟩
