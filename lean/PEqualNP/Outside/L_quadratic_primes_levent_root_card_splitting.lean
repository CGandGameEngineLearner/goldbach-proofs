import Mathlib

set_option linter.style.haveILetI false

theorem PEqualNP.Outside.L_quadratic_primes_levent_root_card_splitting :
    let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a); ∀ p : ℕ, Nat.Prime p → (roots 1 p).card = if p=2 then 1 else if p%4=1 then 2 else 0 := by
  dsimp only
  intro p hp
  by_cases hp2 : p = 2
  · subst hp2
    decide
  · haveI : NeZero p := ⟨hp.pos.ne'⟩
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    have hcard : ((Finset.range p).filter (fun r => p ∣ r^2+1)).card
        = (Finset.univ.filter (fun x : ZMod p => x^2 = -(1 : ZMod p))).card := by
      apply Finset.card_bij (fun (r : ℕ) (_ : r ∈ (Finset.range p).filter (fun r => p ∣ r^2+1)) => (r : ZMod p))
      · intro r hr
        simp only [Finset.mem_filter, Finset.mem_range] at hr
        obtain ⟨hrlt, hrdiv⟩ := hr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have h2 : ((r^2 + 1 : ℕ) : ZMod p) = 0 := by
          rw [ZMod.natCast_eq_zero_iff]; exact hrdiv
        push_cast at h2
        linear_combination h2
      · intro r1 hr1 r2 hr2 heq
        simp only [Finset.mem_filter, Finset.mem_range] at hr1 hr2
        have h := ZMod.natCast_eq_natCast_iff' r1 r2 p
        rw [h] at heq
        rw [Nat.mod_eq_of_lt hr1.1, Nat.mod_eq_of_lt hr2.1] at heq
        exact heq
      · intro x hx
        refine ⟨x.val, ?_, by rw [ZMod.natCast_zmod_val]⟩
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hx ⊢
        refine ⟨ZMod.val_lt x, ?_⟩
        have h2 : ((x.val^2 + 1 : ℕ) : ZMod p) = 0 := by
          push_cast
          rw [ZMod.natCast_zmod_val, hx]
          ring
        exact (ZMod.natCast_eq_zero_iff _ _).mp h2
    have key : (Finset.univ.filter (fun x : ZMod p => x^2 = -(1 : ZMod p))).card
        = ({x : ZMod p | x^2 = ((-1:ℤ) : ZMod p)}).toFinset.card := by
      rw [show ({x : ZMod p | x^2 = ((-1:ℤ) : ZMod p)}).toFinset
            = Finset.univ.filter (fun x : ZMod p => x^2 = ((-1:ℤ) : ZMod p)) from by ext x; simp]
      rw [show (((-1:ℤ) : ZMod p)) = -(1 : ZMod p) from by push_cast; ring]
    rw [ite_eq_right hp2, hcard, key]
    have hcs := legendreSym.card_sqrts p hp2 (-1)
    rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_eq_if_mod_four p] at hcs
    rw [hp.mod_two_eq_one_iff_ne_two.mpr hp2] at hcs
    simp only [Nat.one_ne_zero, ite_false] at hcs
    split_ifs with h4
    · have h1 : (({x : ZMod p | x^2 = ((-1:ℤ) : ZMod p)}).toFinset.card : ℤ) = 2 := by
        rw [hcs]; simp [h4]
      omega
    · have h2 : (({x : ZMod p | x^2 = ((-1:ℤ) : ZMod p)}).toFinset.card : ℤ) = 0 := by
        rw [hcs]; simp [h4]
      omega
