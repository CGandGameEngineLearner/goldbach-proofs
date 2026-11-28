import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.NormNum

namespace FareyMiddleSwitch
open Finset

def win (n : ℕ) := Icc ((n+2)/3) ((2*n)/3)
def fac (n u : ℕ) := (u * (n-u)).minFac
def hits (n z y : ℕ) := (win n).filter fun u => u.Coprime n ∧ z < fac n u ∧ fac n u ≤ y
def pairs (n z y : ℕ) := ((Ioc z y).product (range (n+1))).filter fun v =>
  let p := v.1
  let k := v.2
  p.Prime ∧ p*k ∈ win n ∧ (p*k).Coprime n ∧
    ∀ d ∈ range p, d.Prime → ¬ d ∣ k*(n-p*k)

private theorem refl_win {n u : ℕ} (hu : u ∈ win n) : n-u ∈ win n := by
  have h := mem_Icc.mp hu
  exact mem_Icc.mpr ⟨by omega, by omega⟩

private theorem refl_fac {n u : ℕ} (hu : u ∈ win n) : fac n (n-u) = fac n u := by
  have h := mem_Icc.mp hu
  simp [fac, show n-(n-u)=u by omega, mul_comm]

private theorem fac_prime {n u : ℕ} (hn : 64 ≤ n) (hu : u ∈ win n) : (fac n u).Prime := by
  have h := mem_Icc.mp hu
  have hu2 : 2 ≤ u := by omega
  have hv2 : 2 ≤ n-u := by omega
  have hp := Nat.mul_le_mul hu2 hv2
  exact Nat.minFac_prime (by omega)

private theorem switch_side {n u : ℕ} (hn : 64 ≤ n) (hu : u ∈ win n) (hc : u.Coprime n) :
    fac n u ∣ n-u ↔ ¬ fac n u ∣ u := by
  have h := mem_Icc.mp hu
  have hp := fac_prime hn hu
  constructor
  · intro h1 h2
    have h3 : fac n u ∣ n := by
      simpa [Nat.add_sub_cancel' (show u ≤ n by omega)] using Nat.dvd_add h2 h1
    have hg := Nat.dvd_gcd h2 h3
    rw [hc.gcd_eq_one] at hg
    exact hp.not_dvd_one hg
  · intro h2
    exact (hp.dvd_mul.mp (Nat.minFac_dvd _)).resolve_left h2

private theorem half {n z y : ℕ} (hn : 64 ≤ n) :
    (hits n z y).card = 2*((hits n z y).filter fun u => fac n u ∣ u).card := by
  let h := hits n z y
  let l := h.filter fun u => fac n u ∣ u
  let r := h.filter fun u => ¬ fac n u ∣ u
  have refl_h {u : ℕ} (hu : u ∈ h) : n-u ∈ h := by
    have hu' := mem_filter.mp hu
    have h1 := mem_Icc.mp hu'.1
    exact mem_filter.mpr ⟨refl_win hu'.1, (Nat.coprime_self_sub_left (by omega)).2 hu'.2.1,
      by rw [refl_fac hu'.1]; exact hu'.2.2⟩
  have he : l.card = r.card := by
    apply card_bij (fun u _ => n-u)
    · intro u hu
      have hh := mem_filter.mp (mem_filter.mp hu).1
      have hnot := (switch_side hn hh.1 hh.2.1).1
      exact mem_filter.mpr ⟨refl_h (mem_filter.mp hu).1, by
        rw [refl_fac hh.1]
        exact fun hd => hnot hd (mem_filter.mp hu).2⟩
    · intro a ha b hb hab
      have h1 := mem_Icc.mp (mem_filter.mp (mem_filter.mp ha).1).1
      have h2 := mem_Icc.mp (mem_filter.mp (mem_filter.mp hb).1).1
      omega
    · intro u hu
      have hh := mem_filter.mp (mem_filter.mp hu).1
      have h1 := mem_Icc.mp hh.1
      refine ⟨n-u, mem_filter.mpr ⟨refl_h (mem_filter.mp hu).1, ?_⟩, by omega⟩
      rw [refl_fac hh.1]
      exact (switch_side hn hh.1 hh.2.1).2 (mem_filter.mp hu).2
  have add : l.card + r.card = h.card := card_filter_add_card_filter_not _
  change h.card = 2*l.card
  omega

private theorem forward {n z y u : ℕ} (hn : 64 ≤ n) (hh : u ∈ hits n z y)
    (hd : fac n u ∣ u) : (fac n u, u / fac n u) ∈ pairs n z y := by
  have h := mem_filter.mp hh
  have hw := mem_Icc.mp h.1
  have hp := fac_prime hn h.1
  have eq := Nat.mul_div_cancel' hd
  have hK : u / fac n u ≤ u := Nat.div_le_self _ _
  refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_Ioc.mpr h.2.2, mem_range.mpr (by dsimp; omega)⟩,
    hp, by simpa only [eq] using h.1, by simpa only [eq] using h.2.1, ?_⟩
  intro d hdRange hdp hdvd
  have hdlt := mem_range.mp hdRange
  change d ∣ u / fac n u * (n - fac n u * (u / fac n u)) at hdvd
  rw [eq] at hdvd
  have hdiv : d ∣ u*(n-u) := by
    convert dvd_mul_of_dvd_right hdvd (fac n u) using 1
    rw [← mul_assoc, eq]
  have hmin : fac n u ≤ d := Nat.minFac_le_of_dvd hdp.two_le hdiv
  omega

private theorem backward {n z y p k : ℕ} (hn : 64 ≤ n) (hpair : (p,k) ∈ pairs n z y) :
    fac n (p*k) = p := by
  have h := (mem_filter.mp hpair).2
  have hp := h.1
  have hm := fac_prime hn h.2.1
  have hle : fac n (p*k) ≤ p := Nat.minFac_le_of_dvd hp.two_le
    (dvd_mul_of_dvd_left (dvd_mul_right p k) _)
  by_contra ne
  have hlt : fac n (p*k) < p := by omega
  have hd : fac n (p*k) ∣ p * (k*(n-p*k)) := by
    rw [← mul_assoc]
    exact Nat.minFac_dvd _
  rcases hm.dvd_mul.mp hd with h1 | h2
  · exact hlt.ne ((Nat.prime_dvd_prime_iff_eq hm hp).1 h1)
  · exact h.2.2.2 _ (mem_range.mpr hlt) hm h2

theorem switched (n z y : ℕ) (hn : 64 ≤ n) : (hits n z y).card = 2*(pairs n z y).card := by
  rw [half hn]
  congr 1
  apply card_bij (fun u _ => (fac n u, u/fac n u))
  · intro u hu
    exact forward hn (mem_filter.mp hu).1 (mem_filter.mp hu).2
  · intro a ha b hb hab
    have h1 := Nat.mul_div_cancel' (mem_filter.mp ha).2
    have h2 := Nat.mul_div_cancel' (mem_filter.mp hb).2
    exact h1.symm.trans ((congrArg (fun t : ℕ × ℕ => t.1 * t.2) hab).trans h2)
  · rintro ⟨p,k⟩ hk
    have h := (mem_filter.mp hk).2
    have hp := mem_Ioc.mp (mem_product.mp (mem_filter.mp hk).1).1
    have eq := backward hn hk
    refine ⟨p*k, mem_filter.mpr ⟨mem_filter.mpr ⟨h.2.1, h.2.2.1, by rwa [eq]⟩, ?_⟩, ?_⟩
    · rw [eq]
      exact dvd_mul_right _ _
    · simp only [eq, Nat.mul_div_right _ h.1.pos]

end FareyMiddleSwitch


theorem Conjectures.Cuts.Taskbc45812d7a3b53e078e42d66 : (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → ℕ → ℕ → Finset (ℕ × ℕ) := fun (x2 x3 x4 : ℕ) =>   {x5 ∈ (Finset.Ioc x3 x4).product (Finset.range (x2 + (1 : ℕ))) |     have x6 : ℕ := x5.1;     have x7 : ℕ := x5.2;     Nat.Prime x6 ∧ x6 * x7 ∈ x1 x2 ∧ (x6 * x7).Coprime x2 ∧ ∀ x8 ∈ Finset.range x6, Nat.Prime x8 → ¬x8 ∣ x7 * (x2 - x6 * x7)}; have x3 : ℕ → ℕ → ℕ → Finset ℕ := fun (x3 x4 x5 : ℕ) => {x6 ∈ x1 x3 | x6.Coprime x3 ∧ x4 < (x6 * (x3 - x6)).minFac ∧ (x6 * (x3 - x6)).minFac ≤ x5}; ∀ (x4 x5 x6 : ℕ), (64 : ℕ) ≤ x4 → (x3 x4 x5 x6).card = (2 : ℕ) * (x2 x4 x5 x6).card) := FareyMiddleSwitch.switched
