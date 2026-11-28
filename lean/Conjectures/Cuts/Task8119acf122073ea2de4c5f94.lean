import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

theorem Conjectures.Cuts.Task8119acf122073ea2de4c5f94 : (∀ (x1 : Finset ℕ) (x2 : ℕ → Prop) [x3 : DecidablePred x2] (x4 : ℝ), (0 : ℝ) < x4 → x4 * ↑x1.card ≤ ↑(Finset.filter x2 x1).card → ↑{x7 ∈ x1 | ¬x2 x7}.card ≤ ((1 : ℝ) - x4) * ↑x1.card) := by
  intro s p _ c hc h
  have hpart := Finset.card_filter_add_card_filter_not (s := s) p
  have hR : ((Finset.filter p s).card : ℝ) + (({x ∈ s | ¬ p x}).card : ℝ) = (s.card : ℝ) := by
    exact_mod_cast hpart
  linarith
