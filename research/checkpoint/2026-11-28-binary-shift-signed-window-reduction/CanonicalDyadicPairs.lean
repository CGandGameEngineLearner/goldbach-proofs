import ActualCanonicalCount

open Filter Finset
namespace Goldbach.CanonicalDyadicPairs
open ShiftWideArc MiddleCanonicalModel
noncomputable section
open scoped Classical

/-- Actual and model pairs use exactly the same ranges and parity. -/
def pairs (X : ℕ) (P : ℕ → ℕ → Prop) : ℕ :=
  ∑ m ∈ Icc (X/2) (2*X), ((interiorScales m).filter (fun Y => Even m ∧ P Y m)).card

def actualBadPairs (X : ℕ) := pairs X (fun Y m => (coefficient (bandSet Y) Y m).re < -(Y:ℝ)/64)

def modelBadPairs (X : ℕ) := pairs X (fun Y m => (fieldCoefficient Y m).re < -(Y:ℝ)/128)

def centeredActualBadPairs (P : ℕ → ℕ → ℂ) (X : ℕ) :=
  pairs X (fun Y m => (coefficient (bandSet Y) Y m - P Y m).re < -(Y:ℝ)/64)

def centeredModelBadPairs (P : ℕ → ℕ → ℂ) (X : ℕ) :=
  pairs X (fun Y m => (fieldCoefficient Y m - P Y m).re < -(Y:ℝ)/128)

/-- The perturbation in a pair of frequencies does not depend on their common center. -/
theorem centered_negative_counts : ∀ᶠ Y : ℕ in atTop,
    ∀ (P : ℕ → ℂ) (I : Finset ℕ),
    ((I.filter (fun m => (coefficient (bandSet Y) Y m - P m).re < -(Y:ℝ)/64)).card:ℝ) ≤
      ((I.filter (fun m => (fieldCoefficient Y m - P m).re < -(Y:ℝ)/128)).card:ℝ) +
      (18*128^2:ℝ)*(Y:ℝ)^(2/3:ℝ) := by
  filter_upwards [actual_exceptional_at_128] with Y hY
  intro P I
  let A := I.filter (fun m => (coefficient (bandSet Y) Y m - P m).re < -(Y:ℝ)/64)
  let B := I.filter (fun m => (fieldCoefficient Y m - P m).re < -(Y:ℝ)/128)
  let E := I.filter (fun m => (Y:ℝ)/128 ≤ ‖coefficient (bandSet Y) Y m - fieldCoefficient Y m‖)
  have hsub : A ⊆ B ∪ E := by
    intro m hm
    obtain ⟨hi,ha⟩ := mem_filter.mp hm
    by_cases h : (fieldCoefficient Y m - P m).re < -(Y:ℝ)/128
    · exact mem_union_left _ (mem_filter.mpr ⟨hi,h⟩)
    · apply mem_union_right _ (mem_filter.mpr ⟨hi,?_⟩)
      have hr := Complex.re_le_norm (fieldCoefficient Y m - coefficient (bandSet Y) Y m)
      rw [Complex.sub_re,norm_sub_rev] at hr
      simp only [Complex.sub_re] at h ha
      linarith
  have hcount : A.card ≤ B.card+E.card := (card_le_card hsub).trans (card_union_le ..)
  change (A.card:ℝ) ≤ (B.card:ℝ) + _
  exact (show (A.card:ℝ) ≤ (B.card:ℝ)+(E.card:ℝ) by exact_mod_cast hcount).trans
    (add_le_add (le_refl _) (hY I))

private def eligible (X Y : ℕ) := (Icc (X/2) (2*X)).filter (fun m => Y ∈ interiorScales m ∧ Even m)

private theorem swap_pairs (X : ℕ) (P : ℕ → ℕ → Prop) : pairs X P =
    ∑ Y ∈ Icc (X/4) (2*X), ((eligible X Y).filter (fun m => P Y m)).card := by
  let F := Icc (X/2) (2*X)
  let R := Icc (X/4) (2*X)
  let pair (m Y : ℕ) : ℕ := if Y ∈ interiorScales m ∧ Even m ∧ P Y m then 1 else 0
  have hm (m : ℕ) (hi : m ∈ F) : ((interiorScales m).filter (fun Y => Even m ∧ P Y m)).card =
      ∑ Y ∈ R, pair m Y := by
    have heq : (interiorScales m).filter (fun Y => Even m ∧ P Y m) = R.filter (fun Y => Y ∈ interiorScales m ∧ Even m ∧ P Y m) := by
      ext Y
      simp only [mem_filter]
      constructor
      · rintro ⟨hS,hP⟩
        obtain ⟨h1,h2⟩ := mem_Icc.mp hi
        obtain ⟨h3,h4⟩ := mem_Icc.mp hS
        exact ⟨mem_Icc.mpr ⟨by omega,by omega⟩,hS,hP⟩
      · rintro ⟨_,hs,hP⟩; exact ⟨hs,hP⟩
    simp only [pair,sum_boole,Nat.cast_id]; rw [heq]
  have hY (Y : ℕ) : ∑ m ∈ F, pair m Y = ((eligible X Y).filter (fun m => P Y m)).card := by
    simp only [pair,sum_boole,Nat.cast_id]
    apply congrArg Finset.card
    ext m; simp [eligible,F,and_assoc]
  calc
    _ = ∑ m ∈ F, ∑ Y ∈ R, pair m Y := sum_congr rfl hm
    _ = ∑ Y ∈ R, ∑ m ∈ F, pair m Y := sum_comm
    _ = _ := sum_congr rfl fun Y _ => hY Y

/-- Every exceptional frequency at scale Y is charged once to the same
model frequency or to the unconditionally bounded perturbation count. -/
theorem centered_actual_le_model_add : ∀ᶠ X : ℕ in atTop,
    ∀ P : ℕ → ℕ → ℂ, (centeredActualBadPairs P X:ℝ) ≤ (centeredModelBadPairs P X:ℝ) + (108*128^2:ℝ)*(X:ℝ)^(5/3:ℝ) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp centered_negative_counts
  filter_upwards [eventually_ge_atTop (max 1 (4*N))] with X hx
  intro P
  let R := Icc (X/4) (2*X)
  let e (Y : ℕ) : ℝ := (18*128^2:ℝ)*(Y:ℝ)^(2/3:ℝ)
  have hX1 : 1 ≤ X := by omega
  have hX : 0 < (X:ℝ) := by exact_mod_cast hX1
  have hcard : (R.card:ℝ) ≤ 3*(X:ℝ) := by
    exact_mod_cast (show R.card ≤ 3*X by dsimp [R]; rw [Nat.card_Icc]; omega)
  have h2 : (2:ℝ)^(2/3:ℝ) ≤ 2 := by
    simpa using (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) (by norm_num : (2/3:ℝ)≤1))
  have hsum : ∑ Y ∈ R, e Y ≤ (108*128^2:ℝ)*(X:ℝ)^(5/3:ℝ) := by
    calc
      _ ≤ ∑ _Y ∈ R, (18*128^2:ℝ)*(2*(X:ℝ)^(2/3:ℝ)) := by
        apply sum_le_sum
        intro Y hy
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          _ ≤ (2*(X:ℝ))^(2/3:ℝ) := Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (mem_Icc.mp hy).2) (by norm_num)
          _ ≤ _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hX.le]; exact mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = (R.card:ℝ)*((18*128^2:ℝ)*(2*(X:ℝ)^(2/3:ℝ))) := by simp
      _ ≤ (3*(X:ℝ))*((18*128^2:ℝ)*(2*(X:ℝ)^(2/3:ℝ))) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by rw [show (5/3:ℝ) = 2/3+1 by norm_num,Real.rpow_add_one hX.ne']; ring
  unfold centeredActualBadPairs centeredModelBadPairs
  rw [swap_pairs,swap_pairs]
  simp only [Nat.cast_sum]
  calc
    _ ≤ ∑ Y ∈ R, ((((eligible X Y).filter (fun m => (fieldCoefficient Y m - P Y m).re < -(Y:ℝ)/128)).card:ℝ) + e Y) := by
      apply sum_le_sum
      intro Y hY
      exact hN Y (by have := (mem_Icc.mp hY).1; omega) (P Y) (eligible X Y)
    _ ≤ _ := by rw [sum_add_distrib]; exact add_le_add (le_refl _) hsum

private theorem power_transfer (A B : ℕ → ℕ)
    (hAB : ∀ᶠ X : ℕ in atTop, (A X:ℝ) ≤ (B X:ℝ)+(108*128^2:ℝ)*(X:ℝ)^(5/3:ℝ))
    {α K : ℝ} (ha : α<4/5) (hK : 0<K)
    (hm : ∃ N : ℕ, ∀ X ≥ N, (B X:ℝ) ≤ K*(X:ℝ)^(1+α)) :
    ∃ β C : ℝ, β<4/5 ∧ 0<C ∧ ∃ N : ℕ, ∀ X ≥ N, (A X:ℝ) ≤ C*(X:ℝ)^(1+β) := by
  obtain ⟨N,hN⟩ := hm
  let β := max α (2/3:ℝ)
  refine ⟨β,K+108*128^2,max_lt ha (by norm_num),by positivity,?_⟩
  apply eventually_atTop.mp
  filter_upwards [hAB,eventually_ge_atTop (max 1 N)] with X hX hx
  have hx1 : (1:ℝ)≤X := by exact_mod_cast (show 1≤X by omega)
  have ha' : (X:ℝ)^(1+α) ≤ (X:ℝ)^(1+β) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (add_le_add (le_refl _) (le_max_left α (2/3:ℝ)))
  have hb' : (X:ℝ)^(5/3:ℝ) ≤ (X:ℝ)^(1+β) := by
    apply Real.rpow_le_rpow_of_exponent_le hx1
    have h := le_max_right α (2/3:ℝ)
    dsimp [β]; linarith only [h]
  calc
    _ ≤ K*(X:ℝ)^(1+α)+(108*128^2:ℝ)*(X:ℝ)^(5/3:ℝ) := hX.trans (add_le_add (hN X (by omega)) (le_refl _))
    _ ≤ K*(X:ℝ)^(1+β)+(108*128^2:ℝ)*(X:ℝ)^(1+β) :=
      add_le_add (mul_le_mul_of_nonneg_left ha' hK.le) (mul_le_mul_of_nonneg_left hb' (by positivity))
    _ = _ := by ring

/-- Any model pair exponent 1+α with α<4/5 yields the same type of power
saving for the true middle band, at exponent 1+max(α,2/3). -/
theorem centered_actual_power_of_model (P : ℕ → ℕ → ℂ) {α K : ℝ} (ha : α<4/5) (hK : 0<K)
    (hm : ∃ N : ℕ, ∀ X ≥ N, (centeredModelBadPairs P X:ℝ) ≤ K*(X:ℝ)^(1+α)) :
    ∃ β C : ℝ, β<4/5 ∧ 0<C ∧ ∃ N : ℕ, ∀ X ≥ N, (centeredActualBadPairs P X:ℝ) ≤ C*(X:ℝ)^(1+β) :=
  power_transfer _ _ (centered_actual_le_model_add.mono fun _ h => h P) ha hK hm

theorem actual_le_model_add : ∀ᶠ X : ℕ in atTop,
    (actualBadPairs X:ℝ) ≤ (modelBadPairs X:ℝ) + (108*128^2:ℝ)*(X:ℝ)^(5/3:ℝ) := by
  filter_upwards [centered_actual_le_model_add] with X hX
  simpa [centeredActualBadPairs, centeredModelBadPairs, actualBadPairs, modelBadPairs] using
    hX (fun _ _ => 0)

theorem actual_power_of_model {α K : ℝ} (ha : α<4/5) (hK : 0<K)
    (hm : ∃ N : ℕ, ∀ X ≥ N, (modelBadPairs X:ℝ) ≤ K*(X:ℝ)^(1+α)) :
    ∃ β C : ℝ, β<4/5 ∧ 0<C ∧ ∃ N : ℕ, ∀ X ≥ N, (actualBadPairs X:ℝ) ≤ C*(X:ℝ)^(1+β) := by
  simpa [centeredActualBadPairs,actualBadPairs] using
    centered_actual_power_of_model (fun _ _ => 0) ha hK
      (by simpa [centeredModelBadPairs,modelBadPairs] using hm)

end
end Goldbach.CanonicalDyadicPairs

#print axioms Goldbach.CanonicalDyadicPairs.centered_actual_le_model_add
#print axioms Goldbach.CanonicalDyadicPairs.centered_actual_power_of_model
