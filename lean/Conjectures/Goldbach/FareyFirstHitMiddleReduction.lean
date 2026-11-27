import Mathlib
import Conjectures.Goldbach.FareyInitialSieveLower

-- Upper sieve adapted from Xiaoyan Guo, goldbach-proofs PR #3731.
-- https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/3731
-- The underlying block estimates come from the merged lower sieve, PR #2973.
namespace FareyBrun
open Finset Real ErdosStraus.BrunHooley ErdosStraus.RoughEstimates
open scoped BigOperators
noncomputable section
open scoped Classical

private theorem finite_block_upper {ι α β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    [DecidableEq β] (A : Finset β) (P : ι → Finset α) (hit : α → β → Prop)
    (r : ι → ℕ) (w : α → ℝ) (X D e : ℝ) (hX : 0 ≤ X)
    (hw : ∀ j p, p ∈ P j → 0 ≤ w p ∧ w p < 1)
    (htail : (∑ j, ((∑ p ∈ P j, w p) ^ (2*r j+1) / ((2*r j+1).factorial : ℝ)) /
       (∏ p ∈ P j, (1-w p))) ≤ e)
    (hround : ∀ k : ι → ℕ, (∀ j, k j ≤ 2*r j+1) →
      ∃ E : ℝ, (choices P k).card * E ≤ D ∧ ∀ f ∈ choices P k,
        |intersectionCount A hit (selected f) - X * ∏ j, ∏ p ∈ f j, w p| ≤ E) :
    ((A.filter (fun u => ∀ j p, p ∈ P j → ¬ hit p u)).card:ℝ) ≤
      X * ((∏ j, ∏ p ∈ P j, (1-w p)) * Real.exp e) + D := by
  have hpoint : ((A.filter (fun u => ∀ j p, p ∈ P j → ¬ hit p u)).card:ℝ) ≤
      ∑ u ∈ A, box P (fun p => if hit p u then 1 else 0) (fun j => 2 * r j) := by
    rw [Finset.card_filter]
    push_cast
    apply sum_le_sum
    intro u _
    exact sift_indicator_le_weight P (fun p => hit p u) (fun j => r j)
  obtain ⟨E,hE,hf⟩ := hround (fun j => 2 * r j) (fun j => by omega)
  have hm := box_mean A P hit (fun j => 2 * r j) w X E hf
  have hm' := (abs_le.mp (hm.trans hE)).2
  have hprod := product_truncation_upper P w hw r
  have hp0 : 0 ≤ ∏ j, ∏ p ∈ P j, (1-w p) :=
    prod_nonneg (fun j _ => prod_nonneg (fun p hp => sub_nonneg.mpr (hw j p hp).2.le))
  have h2 : (∏ j, truncation (P j) w (2 * r j)) ≤
      (∏ j, ∏ p ∈ P j, (1-w p)) * Real.exp e :=
    hprod.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htail) hp0)
  have h3 := mul_le_mul_of_nonneg_left h2 hX
  have h4 : X * box P w (fun j => 2 * r j) ≤ X * ((∏ j, ∏ p ∈ P j, (1-w p)) * Real.exp e) := by
    unfold box; exact h3
  linarith

private theorem farey_window_upper (n z K : ℕ) (hn : 64≤n) (heven : Even n) (hz : 2≤z) :
    (sift n z:ℝ) ≤ mainTerm n z * (1 + tiltError K * Real.exp (tiltError K)) +
      (((z^(8*(K+2)):ℕ):ℝ)^2 * n.divisors.card) := by
  let m := blockCount z
  let P := fun j : Fin m => blocks n z j.val
  let r := fun j : Fin m => rank K j.val
  let w := fun p : ℕ => 2/(p:ℝ)
  let W := z^(8*(K+2))
  have hdisj : Pairwise (fun j k => Disjoint (P j) (P k)) := block_disjoint n z hz
  have hcover : univ.biUnion P = good n z := block_cover n z hz
  have hP (j : Fin m) : P j ⊆ good n z := fun _ hp => (mem_filter.mp hp).1
  have hw (j : Fin m) (p : ℕ) (hp : p ∈ P j) : 0 ≤ w p ∧ w p < 1 := by
    have h3 : 3≤p := by
      have hpr := blocks_prime n z j.val p hp
      have h2 := hpr.two_le
      have hcop := (mem_filter.mp (hP j hp)).2
      have htwo := even_iff_two_dvd.mp heven
      by_contra! h
      obtain rfl : p=2 := by omega
      exact hcop htwo
    dsimp [w]
    have h2 : (2:ℝ)<p := by exact_mod_cast h3
    exact ⟨by positivity,(div_lt_one (by positivity)).mpr h2⟩
  have ht := rank_tail K P w (fun j => block_mass n z j.val hz)
    (fun j p hp => (hw j p hp).1) (fun j => block_euler n z j.val heven hz)
  have hround (k : Fin m → ℕ) (hk : ∀ j, k j≤2*r j+1) :=
    window_round hn P hP hdisj k W (fun f hf => by
      have hreal := rank_support K P hdisj (by exact_mod_cast (by omega : 1≤z) : (1:ℝ)≤z)
        (fun j p hp => (mem_filter.mp hp).2.2) k hk hf
      exact_mod_cast hreal)
  have hmain := finite_block_upper (mask n) P (fun p u => p ∣ u*(n-u)) r w
    (scale n) ((W:ℝ)^2*n.divisors.card) (tiltError K)
    (by unfold scale; positivity) hw ht hround
  have hV : (∏ j, ∏ p ∈ P j, (1-w p)) = ∏ p ∈ good n z, (1-w p) := by
    rw [←hcover,prod_biUnion]
    exact hdisj.set_pairwise _
  rw [hV] at hmain
  rw [←sift_blocks n z hn P hcover]
  have hM : 0 ≤ mainTerm n z := mainTerm_nonneg n z
  have hexp : Real.exp (tiltError K) ≤ 1 + tiltError K * Real.exp (tiltError K) := by
    have := Real.add_one_le_exp (-(tiltError K))
    rw [Real.exp_neg] at this
    have hp := Real.exp_pos (tiltError K)
    have h5 : 0 ≤ tiltError K := (Real.exp_pos _).le
    have : 1 - tiltError K ≤ (Real.exp (tiltError K))⁻¹ := by linarith
    have h6 := mul_le_mul_of_nonneg_left this hp.le
    rw [mul_inv_cancel₀ hp.ne'] at h6
    nlinarith
  have h7 : mainTerm n z * Real.exp (tiltError K) ≤ mainTerm n z * (1 + tiltError K * Real.exp (tiltError K)) :=
    mul_le_mul_of_nonneg_left hexp hM
  have h8 : scale n * ((∏ p ∈ good n z, (1-w p)) * Real.exp (tiltError K)) = mainTerm n z * Real.exp (tiltError K) := by
    simp only [mainTerm, w]; ring
  simp only [m, w, W] at hmain h8 ⊢
  linarith
end
end FareyBrun

namespace FareyBrun
open Filter Real Finset
open scoped Topology BigOperators
noncomputable section

private theorem initial_sieve_upper :
    ∃ U₀ : ℕ, 8≤U₀ ∧ ∀ U : ℕ, U₀≤U → ∃ N₀ : ℕ, 64≤N₀ ∧ ∀ n : ℕ, N₀≤n → Even n →
      (sift n (cut n U):ℝ) ≤ mainTerm n (cut n U) + mainTerm n n.sqrt/8 := by
  obtain ⟨C,hC,hterm⟩ := terminal_floor_power
  obtain ⟨U₁,hU₁⟩ := eventually_atTop.1 tilt_eventually
  refine ⟨max 4096 U₁,by omega,?_⟩
  intro U hU
  have hU4 : 4096≤U := le_trans (le_max_left ..) hU
  have htilt := hU₁ U (le_trans (le_max_right ..) hU)
  have hg := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/8)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (32/C)
  obtain ⟨N,hN⟩ := eventually_atTop.1 ((rounding_eventually U hU4).and hg)
  refine ⟨max 64 N,le_max_left ..,?_⟩
  intro n hn heven
  have hn64 : 64≤n := le_trans (le_max_left ..) hn
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  obtain ⟨⟨hcut,hround⟩,hpow⟩ := hN n ((le_max_right ..).trans hn)
  change 32/C ≤ (n:ℝ)^(1/8:ℝ) at hpow
  have hfloor := hterm n hn64 heven
  have hfac := (div_le_iff₀ hC).mp hpow
  have hrem : 2*(n:ℝ)^(3/4:ℝ) ≤ mainTerm n n.sqrt/16 := by
    have hp : (n:ℝ)^(3/4:ℝ)*(n:ℝ)^(1/8:ℝ) = (n:ℝ)^(7/8:ℝ) := by
      rw [←Real.rpow_add hn0]; norm_num
    have hh := mul_le_mul_of_nonneg_left hfac (show 0 ≤ (n:ℝ)^(3/4:ℝ) by positivity)
    rw [show (n:ℝ)^(3/4:ℝ)*((n:ℝ)^(1/8:ℝ)*C) = (n:ℝ)^(7/8:ℝ)*C by rw [←mul_assoc,hp]] at hh
    linarith
  have hcompare := terminal_ratio n U (by omega) heven (by omega)
  have htail := mul_le_mul_of_nonneg_right htilt (mainTerm_nonneg n (cut n U))
  have hl := farey_window_upper n (cut n U) (U/1024) hn64 heven hcut
  have hone : (1:ℝ) ≤ 1 + 2*(blockCount (cut n U):ℝ) := by
    have : (0:ℝ) ≤ (blockCount (cut n U):ℝ) := Nat.cast_nonneg _
    linarith
  have hD : 0 ≤ (((cut n U ^ (8*(U/1024+2)):ℕ):ℝ)^2 * n.divisors.card) := by positivity
  have hD' := mul_le_mul_of_nonneg_right hone hD
  linarith only [hl,hround,hrem,hcompare,htail,hD']
end
end FareyBrun

namespace FareyMiddleReduction

open Finset

noncomputable section

private def cubeCut (n : ℕ) : ℕ := ⌊(n:ℝ)^(1/3:ℝ)⌋₊

private theorem cut_le_cube (n U : ℕ) (hn : 1 ≤ n) (hU : 3 ≤ U) :
    FareyBrun.cut n U ≤ cubeCut n := by
  unfold FareyBrun.cut cubeCut
  apply Nat.floor_mono
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
    (one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hU))

/-- Splitting the initial sift according to the cube-root cutoff gives the
survivors of the middle sift and the candidates with a middle first hit. -/
private theorem sift_split (n z₀ z₁ : ℕ) (hz : z₀ ≤ z₁) :
    FareyBrun.sift n z₀ = FareyBrun.sift n z₁ +
      ((FareyBrun.window n).filter (fun u =>
        u.Coprime n ∧ z₀ < (u*(n-u)).minFac ∧ (u*(n-u)).minFac ≤ z₁)).card := by
  let A := (FareyBrun.window n).filter (fun u => u.Coprime n ∧ z₀ < (u*(n-u)).minFac)
  let p (u : ℕ) := z₁ < (u*(n-u)).minFac
  have hupper :
      A.filter p = (FareyBrun.window n).filter (fun u => u.Coprime n ∧ p u) := by
    ext u
    simp only [A, p, mem_filter]
    constructor
    · rintro ⟨⟨hu,hcop,_⟩,hmin⟩
      exact ⟨hu,hcop,hmin⟩
    · rintro ⟨hu,hcop,hmin⟩
      exact ⟨⟨hu,hcop,hz.trans_lt hmin⟩,hmin⟩
  have hmid :
      A.filter (fun u => ¬ p u) =
        (FareyBrun.window n).filter (fun u =>
          u.Coprime n ∧ z₀ < (u*(n-u)).minFac ∧ (u*(n-u)).minFac ≤ z₁) := by
    ext u
    simp only [A, p, mem_filter, not_lt, and_assoc]
  have h := (card_filter_add_card_filter_not (s := A) p).symm
  rw [hupper, hmid] at h
  exact h

end
end FareyMiddleReduction

/-- The middle first-hit budget follows from the upper initial sift and the middle lower sift. -/
theorem Conjectures.Goldbach.FareyFirstHitMiddleReduction :
    let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3);
    let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime;
    let V := fun n z : ℕ => ((I n).card:ℝ)*(n.totient:ℝ)/n * ∏ p ∈ (P z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ));
    let S := fun n z : ℕ => ((I n).filter (fun u => u.Coprime n ∧ z < (u*(n-u)).minFac)).card;
    let Z₀ := fun n U : ℕ => ⌊(n:ℝ)^((1:ℝ)/(U:ℝ))⌋₊;
    let Z₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊;
    let Z₂ := Nat.sqrt;
    (∃ N₁ : ℕ, 64 ≤ N₁ ∧ ∀ n : ℕ, N₁ ≤ n → Even n → V n (Z₁ n) - V n n.sqrt / 8 ≤ (S n (Z₁ n):ℝ)) →
      (∃ U₁ : ℕ, 8 ≤ U₁ ∧ ∀ U : ℕ, U₁ ≤ U → ∃ N₀ : ℕ, 64 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n → Even n →
        let L := ((I n).filter (fun u => u.Coprime n ∧ Z₀ n U < (u*(n-u)).minFac ∧ (u*(n-u)).minFac ≤ Z₁ n)).card;
        (L:ℝ) ≤ V n (Z₀ n U) - V n (Z₁ n) + V n (Z₂ n)/4) := by
  dsimp only
  intro hmiddle
  change (∃ N₁ : ℕ, 64 ≤ N₁ ∧ ∀ n : ℕ, N₁ ≤ n → Even n →
    FareyBrun.mainTerm n (FareyMiddleReduction.cubeCut n) - FareyBrun.mainTerm n n.sqrt / 8 ≤
      (FareyBrun.sift n (FareyMiddleReduction.cubeCut n) : ℝ)) at hmiddle
  obtain ⟨N₁, hN₁, hmiddle⟩ := hmiddle
  obtain ⟨U₁, hU₁, hsmall⟩ := FareyBrun.initial_sieve_upper
  refine ⟨U₁, hU₁, ?_⟩
  intro U hU
  obtain ⟨N, _, hsmall⟩ := hsmall U hU
  refine ⟨max N N₁, hN₁.trans (le_max_right _ _), ?_⟩
  intro n hn heven
  have hn₁ := (le_max_right N N₁).trans hn
  have hn₀ := (le_max_left N N₁).trans hn
  have hz := FareyMiddleReduction.cut_le_cube n U (by omega) (by omega)
  have hcount := FareyMiddleReduction.sift_split n (FareyBrun.cut n U)
    (FareyMiddleReduction.cubeCut n) hz
  have hcountReal := congrArg (fun k : ℕ => (k : ℝ)) hcount
  push_cast at hcountReal
  change (((FareyBrun.window n).filter (fun u => u.Coprime n ∧
      FareyBrun.cut n U < (u * (n - u)).minFac ∧
      (u * (n - u)).minFac ≤ FareyMiddleReduction.cubeCut n)).card : ℝ) ≤
    FareyBrun.mainTerm n (FareyBrun.cut n U) -
      FareyBrun.mainTerm n (FareyMiddleReduction.cubeCut n) + FareyBrun.mainTerm n n.sqrt / 4
  linarith only [hcountReal, hsmall n hn₀ heven, hmiddle n hn₁ heven]
