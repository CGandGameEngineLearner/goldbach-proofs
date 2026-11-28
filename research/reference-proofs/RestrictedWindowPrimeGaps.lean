import Mathlib

/-!
What a prime in the square-root summand band entails for prime gaps.
The short-window premise is kept as an explicit hypothesis throughout.
-/

namespace Conjectures.Goldbach.RestrictedWindowPrimeGaps

open Finset Filter
open scoped BigOperators Topology

noncomputable def Width (α : ℝ) (y : ℕ) := ⌊(y : ℝ)^α⌋₊

def Hit (X n : ℕ) : Prop := ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧
  Nat.sqrt X ≤ p ∧ p ≤ 2*Nat.sqrt X ∧ p+q=n

def EvenWindowHit (W : ℕ → ℕ) : Prop :=
  ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, Even y → X ≤ y → y+W y ≤ 2*X →
    ∃ n : ℕ, y ≤ n ∧ n ≤ y+W y ∧ Hit X n

private theorem width_small (α : ℝ) {y k : ℕ} (hα : α ≤ 1/3)
    (hy : 1 ≤ y) (hk : 160 ≤ k) (hyk : y ≤ 18*k^2) :
    2 * Width α y ≤ k := by
  have hyR : 1 ≤ (y : ℝ) := by exact_mod_cast hy
  have hkR : 160 ≤ (k : ℝ) := by exact_mod_cast hk
  have hb : (y : ℝ) ≤ 18*(k : ℝ)^2 := by exact_mod_cast hyk
  have hc : ((y : ℝ)^α)^3 ≤ (y : ℝ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg y)]
    exact (Real.rpow_le_rpow_of_exponent_le hyR (by norm_num; linarith only [hα])).trans_eq
      (Real.rpow_one _)
  have htarget : (y : ℝ) ≤ ((k : ℝ)/2)^3 := by
    nlinarith only [hb, mul_nonneg (show 0 ≤ (k : ℝ)-144 by linarith only [hkR])
      (sq_nonneg (k : ℝ))]
  have hroot : (y : ℝ)^α ≤ (k : ℝ)/2 := le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0)
    (by positivity) (hc.trans htarget)
  have hfloor := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg y) α)
  change 2*⌊(y : ℝ)^α⌋₊ ≤ k
  exact_mod_cast (show (2 : ℝ)*(⌊(y : ℝ)^α⌋₊ : ℝ) ≤ k by linarith only [hroot,hfloor])

/-- Move the requested Goldbach window so that its larger prime has to fall
strictly inside any prescribed interval (a,a+m) adjacent to the square m². -/
theorem slidingGap (α : ℝ) (hα : α ≤ 1/3) (hhit : EvenWindowHit (Width α)) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ a : ℕ, m^2 ≤ a → a ≤ (m+1)^2 →
      ∃ q : ℕ, Nat.Prime q ∧ a < q ∧ q < a+m := by
  obtain ⟨X₀, hX₀⟩ := hhit
  refine ⟨4*(X₀+160), ?_⟩
  intro m hm a hlow hhigh
  let k := m/4
  have hkm : 4*k ≤ m ∧ m ≤ 4*k+3 := by dsimp [k]; omega
  have hk : X₀+160 ≤ k := by dsimp [k]; omega
  let X := (3*k)^2
  let y := 2*(a/2+3*k+1)
  have hy : a+6*k+1 ≤ y ∧ y ≤ a+6*k+2 := by dsimp [y]; omega
  have hE : Even y := even_two_mul _
  have hX : X₀ ≤ X := by dsimp [X]; nlinarith only [hk, Nat.le_mul_self k]
  have hXy : X ≤ y := by
    have h' := Nat.pow_le_pow_left hkm.1 2
    dsimp [X]
    nlinarith only [h',hlow,hy.1, Nat.zero_le k, Nat.zero_le (k^2)]
  have hwall : y+k ≤ 18*k^2 := by
    have h' := Nat.pow_le_pow_left (Nat.succ_le_succ hkm.2) 2
    have hpoly := Nat.mul_le_mul_right k (show 160 ≤ k by omega)
    nlinarith only [h',hhigh,hy.2,hpoly,hk, Nat.zero_le X₀]
  have hwidth := width_small α hα (show 1 ≤ y by omega) (show 160 ≤ k by omega)
    (show y ≤ 18*k^2 by omega)
  have hend : y+Width α y ≤ 2*X := by dsimp [X]; nlinarith only [hwidth,hwall]
  obtain ⟨n, hyn, hny, p, q, _, hq, hsp, hps, hsum⟩ := hX₀ X hX y hE hXy hend
  have hsq : Nat.sqrt X = 3*k := by simp [X]
  rw [hsq] at hsp hps
  exact ⟨q,hq,by omega,by omega⟩

def EventualOppermann : Prop :=
  ∃ M : ℕ, ∀ m ≥ M, (∃ p : ℕ, Nat.Prime p ∧ m^2 < p ∧ p < m*(m+1)) ∧
    (∃ q : ℕ, Nat.Prime q ∧ m*(m+1) < q ∧ q < (m+1)^2)

theorem oppermann_of_hit (α : ℝ) (hα : α ≤ 1/3) (hhit : EvenWindowHit (Width α)) :
    EventualOppermann := by
  obtain ⟨M, hM⟩ := slidingGap α hα hhit
  refine ⟨M, ?_⟩
  intro m hm
  have hm1 : m^2 ≤ m*(m+1) := by nlinarith
  have hm2 : m*(m+1) ≤ (m+1)^2 := by nlinarith
  obtain ⟨p, hp, hpl, hpu⟩ := hM m hm (m^2) le_rfl (hm1.trans hm2)
  obtain ⟨q, hq, hql, hqu⟩ := hM m hm (m*(m+1)) hm1 hm2
  exact ⟨⟨p,hp,hpl,by nlinarith⟩,⟨q,hq,hql,by nlinarith⟩⟩

def Ultrashort : Prop :=
  let W := fun y : ℕ => Nat.floor ((y : ℝ) ^ ((26 : ℝ) / 1075))
  ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y + W y ≤ 2 * X →
    ∃ n : ℕ, y ≤ n ∧ n ≤ y + W y ∧ Even n ∧
      (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.sqrt X ≤ p ∧ p ≤ 2 * Nat.sqrt X ∧ p + q = n)

theorem of_ultrashort (H : Ultrashort) : EventualOppermann := by
  apply oppermann_of_hit (26/1075) (by norm_num)
  obtain ⟨X₀, hX₀⟩ := H
  refine ⟨X₀, ?_⟩
  intro X hX y _ hy hw
  obtain ⟨n, h₁, h₂, _, hpair⟩ := hX₀ X hX y hy hw
  exact ⟨n, h₁, h₂, hpair⟩

def countHits (X n : ℕ) : ℕ :=
  (((Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime).filter
    (fun p => p ≤ n ∧ Nat.Prime (n-p))).card

def PowerSaving : Prop :=
  let W := Width (13/225)
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ,
    X ≤ y → y+W y ≤ 2*X →
    (((Finset.Icc y (y+W y)).filter (fun n => Even n ∧ countHits X n=0)).card : ℝ)
      ≤ C*((W y : ℝ)+1)*(X : ℝ)^(-δ)

private theorem exists_hit_of_pos {X n : ℕ} (h : 0 < countHits X n) : Hit X n := by
  obtain ⟨p,hp⟩ := Finset.card_pos.mp h
  obtain ⟨⟨hpband,hprime⟩,hpn,hq⟩ := Finset.mem_filter.mp hp |>.imp_left Finset.mem_filter.mp
  exact ⟨p,n-p,hprime,hq,(Finset.mem_Icc.mp hpband).1,(Finset.mem_Icc.mp hpband).2,by omega⟩

private theorem evenCount (y W : ℕ) (hy : Even y) :
    W/2+1 ≤ ((Icc y (y+W)).filter Even).card := by
  let s := (Icc y (y+W)).filter Even
  have hf : Set.MapsTo (fun i : ℕ => y+2*i) (Finset.range (W/2+1)) s := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    change y+2*i ∈ (Icc y (y+W)).filter Even
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩, hy.add (even_two_mul _)⟩
  have hinj : Set.InjOn (fun i : ℕ => y+2*i) (Finset.range (W/2+1)) := by
    intro a _ b _ hab
    dsimp at hab
    omega
  simpa using Finset.card_le_card_of_injOn _ hf hinj

theorem of_powerSaving (H : PowerSaving) : EventualOppermann := by
  classical
  apply oppermann_of_hit (13/225) (by norm_num)
  obtain ⟨C,δ,_,hδ,X₀,hX₀⟩ := H
  have hlim : Tendsto (fun X : ℕ => C*(X : ℝ)^(-δ)) atTop (nhds 0) := by
    simpa using ((tendsto_rpow_neg_atTop hδ).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul C
  obtain ⟨X₁,hX₁⟩ := Filter.eventually_atTop.1
    (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2)))
  refine ⟨max X₀ X₁, ?_⟩
  intro X hX y hy hXy hend
  let w := Width (13/225) y
  have hbound := hX₀ X ((le_max_left ..).trans hX) y hXy hend
  have hsmall : C*(X : ℝ)^(-δ) < 1/2 := hX₁ _ ((le_max_right ..).trans hX)
  by_contra! hnone
  have hz {n : ℕ} (hn : n ∈ Icc y (y+w)) : countHits X n = 0 := by
    by_contra! hpos
    exact hnone n (mem_Icc.mp hn).1 (mem_Icc.mp hn).2
      (exists_hit_of_pos (Nat.pos_of_ne_zero hpos))
  have heq : ((Icc y (y+w)).filter (fun n => Even n ∧ countHits X n=0)) =
      ((Icc y (y+w)).filter Even) := by
    ext n
    simp only [mem_filter]
    exact ⟨fun h => ⟨h.1,h.2.1⟩,fun h => ⟨h.1,h.2,hz h.1⟩⟩
  change (((Icc y (y+w)).filter (fun n => Even n ∧ countHits X n=0)).card : ℝ) ≤
    C*((w : ℝ)+1)*(X : ℝ)^(-δ) at hbound
  rw [heq] at hbound
  have hc : ((w/2+1 : ℕ) : ℝ) ≤ (((Icc y (y+w)).filter Even).card : ℝ) := by
    exact_mod_cast evenCount y w hy
  have hhalf : (w : ℝ)+1 ≤ 2*((w/2+1 : ℕ) : ℝ) := by
    exact_mod_cast (show w+1 ≤ 2*(w/2+1) by omega)
  have hs := mul_lt_mul_of_pos_right hsmall (show 0 < (w : ℝ)+1 by positivity)
  linarith only [hc, hbound, hhalf, show C*((w : ℝ)+1)*(X : ℝ)^(-δ) <
    (1/2)*((w : ℝ)+1) by simpa only [mul_right_comm] using hs]

end Conjectures.Goldbach.RestrictedWindowPrimeGaps

open Conjectures.Goldbach.RestrictedWindowPrimeGaps in
/-- Each restricted short-window target separately implies eventual Oppermann. -/
theorem Conjectures.Goldbach.RestrictedWindowPrimeGaps :
    (Ultrashort ∨ PowerSaving) → EventualOppermann :=
  fun h => h.elim of_ultrashort of_powerSaving
