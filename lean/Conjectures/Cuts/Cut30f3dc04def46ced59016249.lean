import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

-- child 1 zh: 将中段首次命中精确变换为二倍的单侧素因子与粗糙余因子对数。
-- child 1 en: Factor the first hitting prime on one side; reflection doubles the count of pairs with no smaller prime dividing either cofactor.
-- child 2 zh: 对已抽取首个素因子的中段单侧余因子筛证明带终筛体积预算的上界。
-- child 2 en: Bound the one-sided cofactor sieve after extracting its first prime, with the terminal-volume allowance.

theorem Conjectures.Cuts.Cut30f3dc04def46ced59016249
  (hSwitch :
  let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3)
  let B := fun n z y : ℕ => ((Finset.Ioc z y).product (Finset.range (n+1))).filter fun v =>
    let p := v.1
    let k := v.2
    p.Prime ∧ p*k ∈ I n ∧ (p*k).Coprime n ∧
      ∀ d ∈ Finset.range p, d.Prime → ¬ d ∣ k*(n-p*k)
  let A := fun n z y : ℕ => (I n).filter fun u =>
    u.Coprime n ∧ z < (u*(n-u)).minFac ∧ (u*(n-u)).minFac ≤ y
  ∀ n z y : ℕ, 64 ≤ n → (A n z y).card = 2*(B n z y).card)
  (hBound :
  let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3)
  let B := fun n z y : ℕ => ((Finset.Ioc z y).product (Finset.range (n+1))).filter fun v =>
    let p := v.1
    let k := v.2
    p.Prime ∧ p*k ∈ I n ∧ (p*k).Coprime n ∧
      ∀ d ∈ Finset.range p, d.Prime → ¬ d ∣ k*(n-p*k)
  let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime
  let V := fun n z : ℕ => ((I n).card : ℝ) * (n.totient : ℝ) / n *
    ∏ p ∈ (P z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ))
  ∃ U₁ : ℕ, 8 ≤ U₁ ∧ ∀ U : ℕ, U₁ ≤ U → ∃ N₀ : ℕ, 64 ≤ N₀ ∧ ∀ n : ℕ,
    N₀ ≤ n → Even n →
    let z := ⌊(n:ℝ)^((1:ℝ)/(U:ℝ))⌋₊
    let y := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
    (2 : ℝ) * ((B n z y).card : ℝ) ≤ V n z - V n y + V n n.sqrt / 4) : (let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3); let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime; let V := fun n z : ℕ => ((I n).card:ℝ)*(n.totient:ℝ)/n * ∏ p ∈ (P z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ)); let Z₀ := fun n U : ℕ => ⌊(n:ℝ)^((1:ℝ)/(U:ℝ))⌋₊; let Z₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let Z₂ := Nat.sqrt; ∃ U₁ : ℕ, 8 ≤ U₁ ∧ ∀ U : ℕ, U₁ ≤ U → ∃ N₀ : ℕ, 64 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n → Even n → let L := ((I n).filter (fun u => u.Coprime n ∧ Z₀ n U < (u*(n-u)).minFac ∧ (u*(n-u)).minFac ≤ Z₁ n)).card; (L:ℝ) ≤ V n (Z₀ n U) - V n (Z₁ n) + V n (Z₂ n)/4) := by
  classical
  intro I P V Z₀ Z₁ Z₂
  obtain ⟨U₁, hU₁, h⟩ := hBound
  refine ⟨U₁,hU₁,?_⟩
  intro U hU
  obtain ⟨N₀, hN₀, hh⟩ := h U hU
  refine ⟨N₀,hN₀,?_⟩
  intro n hn he
  have hx := hSwitch n (Z₀ n U) (Z₁ n) (hN₀.trans hn)
  have hy := hh n hn he
  dsimp only
  rw [hx, Nat.cast_mul, Nat.cast_ofNat]
  exact hy
