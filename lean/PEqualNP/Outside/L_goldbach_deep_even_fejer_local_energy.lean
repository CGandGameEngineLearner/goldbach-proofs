import Mathlib

namespace EvenWindowEnergy
open Finset MeasureTheory
open scoped ComplexConjugate
noncomputable section

private def E (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
private def w (k : ℕ) : ℝ := if k.Prime then Real.log k else 0
private def S (n : ℕ) (t : ℝ) : ℂ := ∑ k ∈ range (n+1), (w k:ℂ)*E ((k:ℝ)*t)
private def P (n : ℕ) : ℕ := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
private def widthFactor (n : ℕ) : ℕ := 256*P n*(Nat.log 2 (n+2))^2
private def wide (n : ℕ) : Set ℝ := {t | ∃ q a : ℕ, 1≤q ∧ q≤P n ∧ a≤q ∧ a.Coprime q ∧
  |t-(a:ℝ)/q| ≤ (widthFactor n:ℝ)/((q:ℝ)*n)}
private def F (n : ℕ) : ℝ→ℂ := (wide n)ᶜ.indicator (fun t=> (S n t)^2)
private def mode (n k : ℕ) (t : ℝ) := F n t*E (-(k:ℝ)*t)
private def coeff (n k : ℕ) := ∫ t in (0:ℝ)..1, mode n k t
private def freq (m H : ℕ) (p : ℕ×ℕ) := m+2*(p.1+(H-1)-p.2)
private def idx (H : ℕ) := range H ×ˢ range H

private theorem eAdd (x y : ℝ) : E (x+y)=E x*E y := by
  unfold E;rw [←Complex.exp_add];push_cast;congr 1;ring
private theorem eNeg (x : ℝ) : conj (E x)=E (-x) := by
  unfold E;rw [←Complex.exp_conj,map_mul,Complex.conj_ofReal,Complex.conj_I];push_cast;congr 1;ring

private theorem wideMeas (n : ℕ) : MeasurableSet (wide n) := by
  unfold wide;simp only [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  by_cases h : 1≤q ∧ q≤P n ∧ a≤q ∧ a.Coprime q
  · obtain ⟨h1,h2,h3,h4⟩ := h
    simp only [h1,h2,h3,true_and]
    have hs : {t:ℝ | a.Coprime q ∧ |t-(a:ℝ)/q|≤(widthFactor n:ℝ)/((q:ℝ)*n)} =
        {t:ℝ | |t-(a:ℝ)/q|≤(widthFactor n:ℝ)/((q:ℝ)*n)} := by ext t;exact ⟨And.right,And.intro h4⟩
    rw [hs]
    exact measurableSet_le (f:=fun t:ℝ => |t-(a:ℝ)/q|) (g:=fun _=>(widthFactor n:ℝ)/((q:ℝ)*n)) (by fun_prop) measurable_const
  · have hs : {t:ℝ | 1≤q ∧ q≤P n ∧ a≤q ∧ a.Coprime q ∧ |t-(a:ℝ)/q|≤(widthFactor n:ℝ)/((q:ℝ)*n)}=∅ := by
      ext t;simp;tauto
    rw [hs];exact MeasurableSet.empty

private theorem modeMask (n k : ℕ) (t : ℝ) :
    mode n k t=(wide n)ᶜ.indicator (fun x=> (S n x)^2*E (-(k:ℝ)*x)) t := by
  by_cases h:t∈(wide n)ᶜ <;> simp [mode,F,h]

private theorem modeInt (n k : ℕ) : IntervalIntegrable (mode n k) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have hc : Continuous (fun x=> (S n x)^2*E (-(k:ℝ)*x)) := by unfold S E;fun_prop
  have he : mode n k=(wide n)ᶜ.indicator (fun x=> (S n x)^2*E (-(k:ℝ)*x)) := funext (modeMask n k)
  rw [he]
  exact (hc.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator (wideMeas n).compl

private theorem modeConjInt (n k : ℕ) : IntervalIntegrable (fun t=>conj (mode n k t)) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have hc : Continuous (fun x=> conj ((S n x)^2*E (-(k:ℝ)*x))) := by unfold S E;fun_prop
  have he : (fun t=>conj (mode n k t))=(wide n)ᶜ.indicator (fun x=>conj ((S n x)^2*E (-(k:ℝ)*x))) := by
    ext t:1
    by_cases h:t∈(wide n)ᶜ <;> simp [modeMask,h]
  rw [he]
  exact (hc.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator (wideMeas n).compl

private theorem kernel (n m H : ℕ) (hH : 0<H) (u v : ℝ) :
    (∑ p ∈ idx H, mode n (freq m H p) u*conj (mode n (freq m H p) v)) =
      F n u*conj (F n v)*E (-((m+2*(H-1):ℕ):ℝ)*(u-v))*
      ((‖∑ j ∈ range H, E (2*(j:ℝ)*(u-v))‖^2:ℝ):ℂ) := by
  let z := fun j : ℕ => E (2*(j:ℝ)*(u-v))
  let c := -((m+2*(H-1):ℕ):ℝ)*(u-v)
  have hterm (i j : ℕ) (hj : j∈range H) :
      mode n (freq m H (i,j)) u*conj (mode n (freq m H (i,j)) v) =
        (F n u*conj (F n v)*E c)*(conj (z i)*z j) := by
    have hji : j ≤ i+(H-1) := by have := mem_range.mp hj;omega
    have hf : (freq m H (i,j):ℝ)=(m:ℝ)+2*((i:ℝ)+(H-1:ℕ)-j) := by unfold freq;dsimp;rw [Nat.cast_add,Nat.cast_mul,Nat.cast_sub hji,Nat.cast_add];norm_num
    dsimp only [mode,z]
    rw [map_mul,eNeg,eNeg]
    have he : E (-(freq m H (i,j):ℝ)*u)*E (-(-(freq m H (i,j):ℝ)*v)) =
        E c*(E (-(2*(i:ℝ)*(u-v)))*E (2*(j:ℝ)*(u-v))) := by
      simp only [←eAdd,hf,c,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
      congr 1;ring
    calc
      _ = (F n u*conj (F n v))*(E (-(freq m H (i,j):ℝ)*u)*E (-(-(freq m H (i,j):ℝ)*v))) := by ring
      _ = _ := by rw [he];ring
  rw [idx,sum_product]
  calc
    _ = ∑ i ∈ range H, ∑ j ∈ range H,(F n u*conj (F n v)*E c)*(conj (z i)*z j) :=
      sum_congr rfl (fun i _=>sum_congr rfl (fun j hj=>hterm i j hj))
    _ = (F n u*conj (F n v)*E c)*(conj (∑ i ∈ range H,z i)*(∑ j ∈ range H,z j)) := by
      rw [map_sum,sum_mul_sum];simp_rw [Finset.mul_sum]
    _ = _ := by
      rw [mul_comm (conj (∑ i ∈ range H,z i)),Complex.mul_conj,Complex.normSq_eq_norm_sq]

private theorem identity (n m H : ℕ) (hH : 0<H) :
    ((∑ i ∈ range H,∑ j ∈ range H,‖coeff n (freq m H (i,j))‖^2:ℝ):ℂ) =
      ∫ u in (0:ℝ)..1, ∫ v in (0:ℝ)..1,
        F n u*conj (F n v)*E (-((m+2*(H-1):ℕ):ℝ)*(u-v))*
          ((‖∑ j ∈ range H,E (2*(j:ℝ)*(u-v))‖^2:ℝ):ℂ) := by
  let A := fun p : ℕ×ℕ => mode n (freq m H p)
  let B := fun p : ℕ×ℕ => coeff n (freq m H p)
  have hind (u : ℝ) : (∫ v in (0:ℝ)..1, ∑ p ∈ idx H, A p u*conj (A p v))=
      ∑ p ∈ idx H,A p u*conj (B p) := by
    rw [intervalIntegral.integral_finsetSum (fun p _ => (modeConjInt n (freq m H p)).const_mul (A p u))]
    apply sum_congr rfl
    intro p _
    rw [intervalIntegral.integral_const_mul,intervalIntegral.intervalIntegral_conj]
    rfl
  simp_rw [←kernel n m H hH]
  change _ = ∫ u in (0:ℝ)..1,∫ v in (0:ℝ)..1,∑ p ∈ idx H,A p u*conj (A p v)
  simp_rw [hind]
  rw [intervalIntegral.integral_finsetSum (fun p _=>(modeInt n (freq m H p)).mul_const (conj (B p)))]
  simp_rw [intervalIntegral.integral_mul_const]
  change _ = ∑ p ∈ idx H,B p*conj (B p)
  simp only [idx,sum_product,Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.ofReal_sum,B]

end
end EvenWindowEnergy

open EvenWindowEnergy in
theorem PEqualNP.Outside.L_goldbach_deep_even_fejer_local_energy : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let deepCoeff := fun (n m : ℕ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun u => (S n w u)^2 * E (-(m:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let F := fun (n : ℕ) => (wideArcs n)ᶜ.indicator (fun u => (S n w u)^2); ∀ (n m H : ℕ), 0 < H → Even m → n ≤ m → m+4*(H-1) ≤ 2*n → ((∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H, ‖deepCoeff n (m+2*(i+(H-1)-j))‖^2 : ℝ):ℂ) = intervalIntegral (fun u => intervalIntegral (fun v => F n u * (starRingEnd ℂ) (F n v) * E (-((m+2*(H-1):ℕ):ℝ)*(u-v)) * ((‖∑ j ∈ Finset.range H, E (2*(j:ℝ)*(u-v))‖^2:ℝ):ℂ)) (0:ℝ) 1 MeasureTheory.volume) (0:ℝ) 1 MeasureTheory.volume := by
  dsimp only
  intro n m H hH _ _ _
  simpa only [coeff,modeMask,F,wide,S,w,E,widthFactor,P,freq] using identity n m H hH
