import PEqualNP.Outside.L_goldbach_frontier_no_siegel_zero

/-! Finite estimates for the classes of exceptional Dirichlet zeros in
Pintz, arXiv:1804.09084, (2.39)–(2.44) and §9. The density and repulsion
inequalities are hypotheses. Case 8 below uses exponent 4 and acts directly
on the remaining zeros, without truncating the exceptional zero's weight. -/

namespace Conjectures.Goldbach.PintzExceptionalClassEnergy

open Finset Real

def fiber (Z : Finset ℕ) (g : ℕ → ℕ) (i : ℕ) := Z.filter (fun j => g j=i)

/-- Restricted pairs are dominated by the full square in each class. -/
theorem pair_bound (Z I : Finset ℕ) (g : ℕ → ℕ) (P : Finset (ℕ×ℕ))
    (w : ℕ → ℝ) (hw : ∀ j ∈ Z, 0 ≤ w j)
    (hp : ∀ p ∈ P, p.1 ∈ Z ∧ p.2 ∈ Z ∧ g p.1 ∈ I ∧ g p.1=g p.2) :
    ∑ p ∈ P,w p.1*w p.2 ≤ ∑ i ∈ I,(∑ j ∈ fiber Z g i,w j)^2 := by
  classical
  let box := fun i => (fiber Z g i) ×ˢ (fiber Z g i)
  have hsub : P ⊆ I.biUnion box := by
    intro p h
    obtain ⟨ha,hb,hi,he⟩ := hp p h
    exact mem_biUnion.mpr ⟨g p.1,hi,mem_product.mpr
      ⟨mem_filter.mpr ⟨ha,rfl⟩,mem_filter.mpr ⟨hb,he.symm⟩⟩⟩
  have hd : (I : Set ℕ).PairwiseDisjoint box := by
    intro i hi k hk hik
    apply disjoint_left.mpr
    intro p hp hq
    exact hik ((mem_filter.mp (mem_product.mp hp).1).2.symm.trans
      (mem_filter.mp (mem_product.mp hq).1).2)
  calc
    _ ≤ ∑ p ∈ I.biUnion box,w p.1*w p.2 := sum_le_sum_of_subset_of_nonneg hsub (by
      intro p h _
      obtain ⟨i,_,h⟩ := mem_biUnion.mp h
      obtain ⟨ha,hb⟩ := mem_product.mp h
      exact mul_nonneg (hw _ (mem_filter.mp ha).1) (hw _ (mem_filter.mp hb).1))
    _ = _ := by
      rw [sum_biUnion hd]
      apply sum_congr rfl
      intro i hi
      simp only [box,sum_product,pow_two,sum_mul,mul_sum]
      exact sum_congr rfl (fun j hj => sum_congr rfl (fun k hk => mul_comm _ _))

private theorem general (I : Finset ℕ) (a b : ℕ → ℝ) {M : ℝ}
    (ha : ∀ i ∈ I, 0 ≤ a i) (hb : ∀ i ∈ I, 0 ≤ b i) (hm : ∀ i ∈ I,b i ≤ M) :
    ∑ i ∈ I,(a i+b i)^2 ≤ (∑ i ∈ I,a i)^2 + M*(2*(∑ i ∈ I,a i)+∑ i ∈ I,b i) := by
  have h : ∑ i ∈ I,(a i+b i)^2 ≤ ∑ i ∈ I,((a i)^2+(2*M)*a i+M*b i) := by
    apply sum_le_sum
    intro i hi
    have h₁ := mul_le_mul_of_nonneg_right (hm i hi) (ha i hi)
    have h₂ := mul_le_mul_of_nonneg_right (hm i hi) (hb i hi)
    nlinarith only [h₁,h₂]
  rw [sum_add_distrib,sum_add_distrib,← mul_sum,← mul_sum] at h
  nlinarith only [h,sum_sq_le_sq_sum_of_nonneg ha]

private theorem bonuses (I T : Finset ℕ) {k : ℝ} (hk : 0 ≤ k) :
    (∑ i ∈ I, if i ∈ T then k else 0) ≤ T.card*k := by
  classical
  rw [← sum_filter]
  simp only [sum_const,nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hk
  exact_mod_cast card_le_card (show I.filter (fun i => i ∈ T) ⊆ T from
    fun i h => (mem_filter.mp h).2)

/-- Cases 1–6. Each exceptional tail cap has two places. Their locations
and the number of nonexceptional classes are arbitrary. -/
theorem regular (I U V : Finset ℕ) (a b : ℕ → ℝ)
    (hU : U.card ≤ 2) (hV : V.card ≤ 2)
    (ha : ∀ i ∈ I, 0 ≤ a i) (hb : ∀ i ∈ I, 0 ≤ b i)
    (hA : ∑ i ∈ I,a i ≤ 0.622) (hB : ∑ i ∈ I,b i ≤ 6.805)
    (hcap : ∀ i ∈ I,b i ≤ if i ∈ U then 0.0826 else if i ∈ V then 0.0751 else 0.0722) :
    ∑ i ∈ I,(a i+b i)^2 ≤ 0.98311306 := by
  classical
  let u : ℝ := 0.0826*(0.0826-0.0722)
  let v : ℝ := 0.0751*(0.0751-0.0722)
  have h : ∑ i ∈ I,(a i+b i)^2 ≤ ∑ i ∈ I,((a i)^2+(2*0.0826)*a i+
      0.0722*b i+(if i ∈ U then u else 0)+(if i ∈ V then v else 0)) := by
    apply sum_le_sum
    intro i hi
    have H := hcap i hi
    have one (m : ℝ) (h₁ : b i ≤ m) (h₂ : (0.0722 : ℝ) ≤ m) (h₃ : m ≤ 0.0826) :
        (a i+b i)^2 ≤ (a i)^2+(2*0.0826)*a i+0.0722*b i+m*(m-0.0722) := by
      have h₄ := mul_le_mul_of_nonneg_right (h₁.trans h₃) (ha i hi)
      have h₅ := mul_nonneg (sub_nonneg.mpr h₁) (show 0 ≤ m+b i-0.0722 by linarith [hb i hi])
      nlinarith only [h₄,h₅]
    by_cases hiU : i ∈ U <;> by_cases hiV : i ∈ V <;> simp [hiU,hiV] at H ⊢
    all_goals first
      | nlinarith only [one _ H (by norm_num) (by norm_num),show 0 ≤ v by norm_num [v],
          show u=0.0826*(0.0826-0.0722) from rfl,show v=0.0751*(0.0751-0.0722) from rfl]
  simp only [sum_add_distrib,← mul_sum] at h
  have hU' : (U.card : ℝ) ≤ 2 := by exact_mod_cast hU
  have hV' : (V.card : ℝ) ≤ 2 := by exact_mod_cast hV
  have hu := (bonuses I U (k:=u) (by norm_num [u])).trans
    (mul_le_mul_of_nonneg_right hU' (by norm_num [u]))
  have hv := (bonuses I V (k:=v) (by norm_num [v])).trans
    (mul_le_mul_of_nonneg_right hV' (by norm_num [v]))
  have hsq := pow_le_pow_left₀ (sum_nonneg ha) hA 2
  dsimp only [u,v] at hu hv
  linarith only [h,sum_sq_le_sq_sum_of_nonneg ha,hsq,hA,hB,hu,hv]

/-- Case 7, with the 0.0715 cap appearing in equation (9.28). -/
theorem isolated (I : Finset ℕ) (a b : ℕ → ℝ)
    (ha : ∀ i ∈ I, 0 ≤ a i) (hb : ∀ i ∈ I, 0 ≤ b i)
    (hA : ∑ i ∈ I,a i ≤ 0.86671) (hB : ∑ i ∈ I,b i ≤ 1.74516)
    (hm : ∀ i ∈ I,b i ≤ 0.0715) :
    ∑ i ∈ I,(a i+b i)^2 ≤ 0.9999046941 := by
  have h := general I a b ha hb hm
  have hsq := pow_le_pow_left₀ (sum_nonneg ha) hA 2
  linarith only [h,hsq,hA,hB]

private theorem compare_weight {x l : ℝ} (hx : 0 < x) (h : -Real.log x ≤ l) :
    Real.exp (-4*l) ≤ x^2*Real.exp (-2*l) := by
  rw [show -4*l=(-2*l)+(-2*l) by ring,Real.exp_add]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  calc
    _ ≤ Real.exp (Real.log x+Real.log x) := Real.exp_le_exp.mpr (by linarith)
    _ = x^2 := by rw [Real.exp_add,Real.exp_log hx,pow_two]

private theorem sum_fibers (I Z : Finset ℕ) (g : ℕ → ℕ) (w : ℕ → ℝ)
    (hw : ∀ j ∈ Z,0 ≤ w j) :
    (∑ i ∈ I,∑ j ∈ fiber Z g i,w j) ≤ ∑ j ∈ Z,w j := by
  classical
  have hd : (I : Set ℕ).PairwiseDisjoint (fiber Z g) := by
    intro i hi k hk hik
    exact disjoint_left.mpr (fun j hj hj' => hik
      ((mem_filter.mp hj).2.symm.trans (mem_filter.mp hj').2))
  rw [← sum_biUnion hd]
  exact sum_le_sum_of_subset_of_nonneg (fun j h => by
    obtain ⟨_,_,hj⟩ := mem_biUnion.mp h
    exact (mem_filter.mp hj).1) (fun j h _ => hw j h)

/-- Case 8 for q at the fourth-root scale. The distinguished real zero
has distance x. All other zeros satisfy the stated log-repulsion inequality.
The inputs on them are the two actual exponential moments in (9.32). -/
theorem repelled (I Z : Finset ℕ) (g : ℕ → ℕ) (l : ℕ → ℝ) (k : ℕ)
    {x : ℝ} (hx : 0 < x) (hsmall : x ≤ 1/25)
    (hrep : ∀ j ∈ Z, -Real.log x ≤ l j)
    (ht : ∑ j ∈ Z,Real.exp (-(8/3 : ℝ)*l j) ≤ 10.4)
    (hc : ∀ i ∈ I,∑ j ∈ fiber Z g i,Real.exp (-2*l j) ≤ 10.4) :
    ∑ i ∈ I,((if i=k then Real.exp (-4*x) else 0)+
      ∑ j ∈ fiber Z g i,Real.exp (-4*l j))^2 ≤ 1-5*x := by
  classical
  let a := fun i : ℕ => if i=k then Real.exp (-4*x) else 0
  let b := fun i : ℕ => ∑ j ∈ fiber Z g i,Real.exp (-4*l j)
  have ha (i) (_ : i ∈ I) : 0 ≤ a i := by dsimp [a]; split <;> positivity
  have hb (i) (_ : i ∈ I) : 0 ≤ b i := sum_nonneg (fun _ _ => (Real.exp_pos _).le)
  have hm (i) (hi : i ∈ I) : b i ≤ 10.4*x^2 := calc
    _ ≤ ∑ j ∈ fiber Z g i,x^2*Real.exp (-2*l j) := sum_le_sum (fun j hj =>
      compare_weight hx (hrep j (mem_filter.mp hj).1))
    _ ≤ _ := by rw [← mul_sum,mul_comm (10.4:ℝ)]; gcongr; exact hc i hi
  have hlog : Real.log x ≤ 0 := Real.log_nonpos hx.le (by linarith)
  have ht' : ∑ i ∈ I,b i ≤ x*10.4 := calc
    _ ≤ ∑ j ∈ Z,Real.exp (-4*l j) := sum_fibers I Z g _ (fun _ _ => (Real.exp_pos _).le)
    _ ≤ ∑ j ∈ Z,x*Real.exp (-(8/3 : ℝ)*l j) := by
      apply sum_le_sum
      intro j hj
      rw [← Real.exp_log hx,← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith only [hrep j hj,hlog]
    _ ≤ _ := by rw [← mul_sum]; gcongr
  have hA : ∑ i ∈ I,a i ≤ Real.exp (-4*x) := by
    simp only [a,sum_ite_eq']
    split
    · exact le_rfl
    · exact (Real.exp_pos _).le
  have he₁ : Real.exp (-4*x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hE := general I a b ha hb hm
  have hs := pow_le_pow_left₀ (sum_nonneg ha) hA 2
  rw [show (Real.exp (-4*x))^2 = Real.exp (-8*x) by
    rw [pow_two,← Real.exp_add]; congr 1; ring] at hs
  have htot : 2*(∑ i ∈ I,a i)+(∑ i ∈ I,b i) ≤ 2.416 :=
    by linarith only [hA,he₁,ht',hsmall]
  have hmul := mul_le_mul_of_nonneg_left htot (show 0 ≤ 10.4*x^2 by positivity)
  -- Keep the full exponential margin. 8/(1+8/25) is strictly above 6.
  have he' : Real.exp (-8*x) ≤ 1-6.05*x := by
    have hlin : 1+8*x ≤ Real.exp (8*x) := by linarith only [Real.add_one_le_exp (8*x)]
    rw [show -8*x=-(8*x) by ring,Real.exp_neg]
    apply (inv_le_iff_one_le_mul₀ (Real.exp_pos _)).2
    calc
      1 ≤ (1+8*x)*(1-6.05*x) := by
        nlinarith only [mul_nonneg hx.le (show 0 ≤ 1/25-x by linarith),hx.le]
      _ ≤ Real.exp (8*x)*(1-6.05*x) := mul_le_mul_of_nonneg_right hlin (by linarith)
      _ = _ := mul_comm _ _
  change ∑ i ∈ I,(a i+b i)^2 ≤ _
  nlinarith only [hE,hs,he',hmul,mul_nonneg hx.le (show 0 ≤ 1/25-x by linarith),hx.le]

/-- The project’s independently proved real quadratic zero gap makes the
deficit uniform even when the conductor r and the multiple-scale q vary. -/
theorem uniform_repelled : ∃ η : ℝ,0 < η ∧
    ∀ (q r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (β : ℝ),
    2 ≤ q → r ≤ q → χ^2=1 → β<1 → DirichletCharacter.LFunction χ (β:ℂ)=0 →
    let x := (1-β)*Real.log q
    ∀ (I Z : Finset ℕ) (g : ℕ → ℕ) (l : ℕ → ℝ) (k : ℕ), x ≤ 1/25 →
      (∀ j ∈ Z,-Real.log x ≤ l j) →
      (∑ j ∈ Z,Real.exp (-(8/3 : ℝ)*l j) ≤ 10.4) →
      (∀ i ∈ I,∑ j ∈ fiber Z g i,Real.exp (-2*l j) ≤ 10.4) →
      ∑ i ∈ I,((if i=k then Real.exp (-4*x) else 0)+
        ∑ j ∈ fiber Z g i,Real.exp (-4*l j))^2 ≤ 1-η := by
  obtain ⟨c,hc,H⟩ := PEqualNP.Outside.L_goldbach_frontier_no_siegel_zero
  refine ⟨5*c/2,by positivity,?_⟩
  intro q r _ χ β hq hr hχ hβ hz x I Z g l k hsmall hrep ht hclasses
  have hlog : 0 < Real.log ((r:ℝ)+2) := Real.log_pos (by
    linarith only [Nat.cast_nonneg (α:=ℝ) r])
  have hright : β ≤ 1-c/Real.log ((r:ℝ)+2) :=
    le_of_not_gt (fun h => H r χ β hχ h hβ hz)
  have hlower : c ≤ (1-β)*Real.log ((r:ℝ)+2) :=
    (div_le_iff₀ hlog).1 (by linarith only [hright])
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hr' : (r : ℝ) ≤ q := by exact_mod_cast hr
  have hL : Real.log ((r:ℝ)+2) ≤ 2*Real.log (q:ℝ) := calc
    _ ≤ Real.log ((q:ℝ)^2) := Real.log_le_log (by positivity) (by
      nlinarith only [hr',mul_nonneg (show 0≤(q:ℝ)-2 by linarith) (show 0≤(q:ℝ)+1 by positivity)])
    _ = _ := by rw [Real.log_pow]; norm_num
  have hgap := hlower.trans (mul_le_mul_of_nonneg_left hL (sub_nonneg.mpr hβ.le))
  have hx : 0 < x := mul_pos (sub_pos.mpr hβ) (Real.log_pos (by linarith))
  have he := repelled I Z g l k hx hsmall hrep ht hclasses
  dsimp only [x] at he ⊢
  linarith only [he,hgap]

end Conjectures.Goldbach.PintzExceptionalClassEnergy

open Conjectures.Goldbach.PintzExceptionalClassEnergy in
/-- Class-pair energy and the three numerical regimes for the near-real zeros. -/
theorem Conjectures.Goldbach.PintzExceptionalClassEnergy :
let F := fun (Z : Finset ℕ) (g : ℕ → ℕ) (i : ℕ) => Z.filter (fun j => g j = i);
(∀ (Z I : Finset ℕ) (g : ℕ → ℕ) (P : Finset (ℕ × ℕ)) (w : ℕ → ℝ),
  (∀ j ∈ Z, 0 ≤ w j) → (∀ p ∈ P, p.1 ∈ Z ∧ p.2 ∈ Z ∧ g p.1 ∈ I ∧ g p.1 = g p.2) →
  ∑ p ∈ P, w p.1*w p.2 ≤ ∑ i ∈ I, (∑ j ∈ F Z g i, w j)^2) ∧
(∀ (I U V : Finset ℕ) (a b : ℕ → ℝ), U.card ≤ 2 → V.card ≤ 2 →
  (∀ i ∈ I, 0 ≤ a i) → (∀ i ∈ I, 0 ≤ b i) →
  (∑ i ∈ I, a i) ≤ 0.622 → (∑ i ∈ I, b i) ≤ 6.805 →
  (∀ i ∈ I, b i ≤ if i ∈ U then 0.0826 else if i ∈ V then 0.0751 else 0.0722) →
  ∑ i ∈ I, (a i+b i)^2 ≤ 0.98311306) ∧
(∀ (I : Finset ℕ) (a b : ℕ → ℝ), (∀ i ∈ I, 0 ≤ a i) → (∀ i ∈ I, 0 ≤ b i) →
  (∑ i ∈ I, a i) ≤ 0.86671 → (∑ i ∈ I, b i) ≤ 1.74516 →
  (∀ i ∈ I, b i ≤ 0.0715) → ∑ i ∈ I, (a i+b i)^2 ≤ 0.9999046941) ∧
(∀ (I Z : Finset ℕ) (g : ℕ → ℕ) (l : ℕ → ℝ) (k : ℕ) (x : ℝ), 0 < x → x ≤ 1/25 →
  (∀ j ∈ Z, -Real.log x ≤ l j) →
  (∑ j ∈ Z, Real.exp (-(8/3 : ℝ)*l j)) ≤ 10.4 →
  (∀ i ∈ I, (∑ j ∈ F Z g i, Real.exp (-2*l j)) ≤ 10.4) →
  (∑ i ∈ I, ((if i=k then Real.exp (-4*x) else 0)+∑ j ∈ F Z g i, Real.exp (-4*l j))^2) ≤ 1-5*x) ∧
(∃ η : ℝ, 0 < η ∧ ∀ (q r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (β : ℝ),
  2 ≤ q → r ≤ q → χ^2=1 → β<1 → DirichletCharacter.LFunction χ (β:ℂ)=0 →
  let x := (1-β)*Real.log q;
  ∀ (I Z : Finset ℕ) (g : ℕ → ℕ) (l : ℕ → ℝ) (k : ℕ), x ≤ 1/25 →
    (∀ j ∈ Z, -Real.log x ≤ l j) →
    (∑ j ∈ Z, Real.exp (-(8/3 : ℝ)*l j)) ≤ 10.4 →
    (∀ i ∈ I, (∑ j ∈ F Z g i, Real.exp (-2*l j)) ≤ 10.4) →
    (∑ i ∈ I, ((if i=k then Real.exp (-4*x) else 0)+∑ j ∈ F Z g i, Real.exp (-4*l j))^2) ≤ 1-η) :=
  ⟨pair_bound,regular,isolated,fun I Z g l k _ => repelled I Z g l k,uniform_repelled⟩
