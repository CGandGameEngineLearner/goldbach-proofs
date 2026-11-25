import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.ModEq

namespace PEqualNP.Outside

/-- A prime in the probe classes that divides the combined modulus divides both `d` and `n`. -/
theorem L_goldbach_finite_sieve_probe_nonunit :
    ∀ n d e p : ℕ, Nat.Prime p → p % d = n % d → p % e = 1 % e →
      p ∣ Nat.lcm d e → p ∣ d ∧ p ∣ n := by
  intro n d e p hp hpn hp1 hlcm
  change Nat.ModEq d p n at hpn
  change Nat.ModEq e p 1 at hp1
  have hpe : ¬ p ∣ e := fun h => hp.not_dvd_one ((hp1.dvd_iff h).mp (dvd_refl p))
  have hpd : p ∣ d := (hp.dvd_or_dvd_of_dvd_lcm hlcm).resolve_right hpe
  exact ⟨hpd, (hpn.dvd_iff hpd).mp (dvd_refl p)⟩

end PEqualNP.Outside
