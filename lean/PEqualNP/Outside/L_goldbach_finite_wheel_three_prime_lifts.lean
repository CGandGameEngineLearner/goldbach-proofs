import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime

namespace PEqualNP.Outside

theorem L_goldbach_finite_wheel_three_prime_lifts :
    ∀ r ∈ ({17,19,23,181,29,37,41,43,31,47,53,67} : Finset ℕ), ∃ S : Finset ℕ, S.card=3 ∧ (∀ p ∈ S, Nat.Prime p ∧ p ≤ 210233 ∧ p % 30030=r) ∧ (∀ p ∈ S, ∀ q ∈ S, p ≠ q → p % 17 ≠ q % 17 ∧ p % 19 ≠ q % 19) := by
  intro r hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨{17, 30047, 60077}, ?_⟩
    norm_num [Finset.forall_mem_insert, Finset.mem_singleton,
      Finset.card_insert_of_notMem, Finset.mem_insert]
  · refine ⟨{19, 150169, 210229}, ?_⟩
    norm_num [Finset.forall_mem_insert, Finset.mem_singleton,
      Finset.card_insert_of_notMem, Finset.mem_insert]
  · refine ⟨{23, 60083, 210233}, ?_⟩
    norm_num [Finset.forall_mem_insert, Finset.mem_singleton,
      Finset.card_insert_of_notMem, Finset.mem_insert]
  · refine ⟨{181, 30211, 90271}, ?_⟩
    norm_num [Finset.forall_mem_insert, Finset.mem_singleton,
      Finset.card_insert_of_notMem, Finset.mem_insert]
  · refine ⟨{29, 30059, 60089}, ?_⟩
    norm_num [Finset.forall_mem_insert, Finset.mem_singleton,
      Finset.card_insert_of_notMem, Finset.mem_insert]
  · refine ⟨{37, 90127, 120157}, ?_⟩
    norm_num [Finset.forall_mem_insert, Finset.mem_singleton,
      Finset.card_insert_of_notMem, Finset.mem_insert]
  · refine ⟨{41, 30071, 60101}, ?_⟩
    norm_num [Finset.forall_mem_insert, Finset.mem_singleton,
      Finset.card_insert_of_notMem, Finset.mem_insert]
  · refine ⟨{43, 60103, 120163}, ?_⟩
    norm_num [Finset.forall_mem_insert, Finset.mem_singleton,
      Finset.card_insert_of_notMem, Finset.mem_insert]
  · refine ⟨{31, 60091, 90121}, ?_⟩
    norm_num [Finset.forall_mem_insert, Finset.mem_singleton,
      Finset.card_insert_of_notMem, Finset.mem_insert]
  · refine ⟨{47, 60107, 120167}, ?_⟩
    norm_num [Finset.forall_mem_insert, Finset.mem_singleton,
      Finset.card_insert_of_notMem, Finset.mem_insert]
  · refine ⟨{53, 150203, 180233}, ?_⟩
    norm_num [Finset.forall_mem_insert, Finset.mem_singleton,
      Finset.card_insert_of_notMem, Finset.mem_insert]
  · refine ⟨{67, 30097, 60127}, ?_⟩
    norm_num [Finset.forall_mem_insert, Finset.mem_singleton,
      Finset.card_insert_of_notMem, Finset.mem_insert]

end PEqualNP.Outside
