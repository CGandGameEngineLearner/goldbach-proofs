import Mathlib

namespace PEqualNP.Outside

/-- Only the prime 2 contributes to the even fibers of a dyadic layer. -/
theorem L_goldbach_dyadic_reflected_prime_two :
    ∀ (N k : ℕ), 4 ≤ N → Even N → 1 ≤ k →
      let q : ℕ := 2^k
      let A := fun r : ℕ => ∑ n ∈ (Finset.range (N+1)).filter (fun n => n % (2*q)=r ∧ n.Prime), Real.log (n : ℝ)
      let D := fun r : ℕ => A r - A (r+q)
      (∑ r ∈ (Finset.range q).filter (fun r => Even r),
        (if (N+2*q-r) % (2*q) < q then (1 : ℝ) else -1) * D r * D ((N+q-r) % q)) =
        (if N % (2*q)=4 % (2*q) then (1 : ℝ) else if N % (2*q)=(4+q) % (2*q) then -1 else 0) * (Real.log 2)^2 := by
  classical
  intro N k hN hNe hk
  dsimp only
  set q : ℕ := 2^k
  set A : ℕ → ℝ := fun r => ∑ n ∈ (Finset.range (N+1)).filter (fun n => n % (2*q) = r ∧ n.Prime), Real.log (n : ℝ) with hA
  let D : ℕ → ℝ := fun r => A r - A (r+q)
  change (∑ r ∈ (Finset.range q).filter Even,
      (if (N+2*q-r) % (2*q) < q then (1 : ℝ) else -1) * D r * D ((N+q-r) % q)) = _
  have hqe : Even q := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k-1, by omega⟩
    change Even (2^(j+1) : ℕ)
    rw [pow_succ]
    exact ⟨2^j, by omega⟩
  have hq : 2 ≤ q := by
    have hp : 0 < q := by dsimp [q]; positivity
    obtain ⟨j, hj⟩ := hqe
    omega
  have hd : q ∣ 2*q := ⟨2, by omega⟩
  have hAeq (s : ℕ) (hs : Even s) : A s = if s = 2 then Real.log 2 else 0 := by
    have htwo : 2 % (2*q) = 2 := Nat.mod_eq_of_lt (by omega)
    have hset : (Finset.range (N+1)).filter (fun n => n % (2*q) = s ∧ n.Prime) =
        if s = 2 then {2} else ∅ := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range]
      have he : n % (2*q) = s → n.Prime → n = 2 := by
        intro hn hp
        rcases hp.eq_two_or_odd with hn2 | ho
        · exact hn2
        · have hm := Nat.mod_mod_of_dvd n (show 2 ∣ 2*q from ⟨q, rfl⟩)
          rw [hn, ho] at hm
          obtain ⟨j, hj⟩ := hs
          omega
      by_cases hs2 : s = 2
      · subst s
        simp only [ite_true, Finset.mem_singleton]
        constructor
        · rintro ⟨_, hm, hp⟩
          exact he hm hp
        · rintro rfl
          exact ⟨by omega, htwo, Nat.prime_two⟩
      · simp only [ite_eq_right hs2, Finset.notMem_empty, iff_false]
        rintro ⟨_, hm, hp⟩
        exact hs2 (hm.symm.trans (by rw [he hm hp, htwo]))
    change (∑ n ∈ (Finset.range (N+1)).filter (fun n => n % (2*q) = s ∧ n.Prime), Real.log (n : ℝ)) = _
    rw [hset]
    split <;> simp
  let r : ℕ := 2 % q
  have hrq : r < q := Nat.mod_lt _ (by omega)
  have hrform : (q = 2 ∧ r = 0) ∨ (2 < q ∧ r = 2) := by
    by_cases H : q = 2
    · exact Or.inl ⟨H, by simp [r, H]⟩
    · exact Or.inr ⟨by omega, Nat.mod_eq_of_lt (by omega)⟩
  have hre : Even r := by
    rcases hrform with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> decide
  have hDz (s : ℕ) (hs : s < q) (hse : Even s) (hsr : s ≠ r) : D s = 0 := by
    have h₁ : s ≠ 2 := by
      rcases hrform with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    have h₂ : s+q ≠ 2 := by
      rcases hrform with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    simp [D, hAeq s hse, hAeq (s+q) (hse.add hqe), h₁, h₂]
  have hDr : D r * D r = (Real.log 2)^2 := by
    rw [show D r = A r - A (r+q) from rfl, hAeq r hre, hAeq (r+q) (hre.add hqe)]
    rcases hrform with ⟨hq2, hr0⟩ | ⟨hql, hr2⟩
    · rw [hq2, hr0]
      norm_num <;> ring
    · rw [hr2]
      simp [show q ≠ 0 by omega, pow_two]
  rw [Finset.sum_eq_single r]
  · let x : ℕ := (N+2*q-r) % (2*q)
    let y : ℕ := (N+q-r) % q
    change (if x < q then (1 : ℝ) else -1) * D r * D y = _
    have hyq : y < q := Nat.mod_lt _ (by omega)
    have hxe : x < 2*q := Nat.mod_lt _ (by omega)
    have hyx : x % q = y := by
      dsimp [x, y]
      rw [Nat.mod_mod_of_dvd _ hd, show N+2*q-r = (N+q-r)+q by omega, Nat.add_mod_right]
    have hye : Even y := by
      obtain ⟨a, ha⟩ := hNe
      obtain ⟨b, hb⟩ := hqe
      obtain ⟨c, hc⟩ := hre
      have hm := Nat.mod_mod_of_dvd (N+q-r) (show 2 ∣ q from ⟨b, by omega⟩)
      change y % 2 = (N+q-r) % 2 at hm
      exact ⟨y/2, by omega⟩
    have hxN : Nat.ModEq (2*q) (x+r) N := by
      calc
        x+r ≡ (N+2*q-r)+r [MOD 2*q] := (Nat.mod_modEq _ _).add_right r
        _ = N+2*q := by omega
        _ ≡ N [MOD 2*q] := Nat.add_mod_right _ _
    have h4 : Nat.ModEq (2*q) (r+r) 4 := by
      rcases hrform with ⟨hq2, hr0⟩ | ⟨_, hr2⟩
      · simp [hq2, hr0, Nat.ModEq]
      · simp [hr2, Nat.ModEq]
    have h4q : Nat.ModEq (2*q) (r+q+r) (4+q) := by
      simpa only [Nat.add_right_comm] using h4.add_right q
    have heq4 : N % (2*q) = 4 % (2*q) ↔ x = r := by
      constructor
      · intro h
        have hh : Nat.ModEq (2*q) (x+r) (r+r) := hxN.trans ((show Nat.ModEq (2*q) N 4 from h).trans h4.symm)
        have hh' := hh.add_right_cancel' r
        simpa [Nat.ModEq, Nat.mod_eq_of_lt hxe, Nat.mod_eq_of_lt (show r < 2*q by omega)] using hh'
      · intro h
        rw [h] at hxN
        exact hxN.symm.trans h4
    have heq4q : N % (2*q) = (4+q) % (2*q) ↔ x = r+q := by
      constructor
      · intro h
        have hh : Nat.ModEq (2*q) (x+r) (r+q+r) := hxN.trans ((show Nat.ModEq (2*q) N (4+q) from h).trans h4q.symm)
        have hh' := hh.add_right_cancel' r
        simpa [Nat.ModEq, Nat.mod_eq_of_lt hxe, Nat.mod_eq_of_lt (show r+q < 2*q by omega)] using hh'
      · intro h
        rw [h] at hxN
        exact hxN.symm.trans h4q
    simp only [heq4, heq4q]
    have hshift : (r+q) % q = r := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hrq]
    by_cases hy : y = r
    · rw [hy, mul_assoc, hDr]
      by_cases H : x < q
      · have hxr : x = r := (Nat.mod_eq_of_lt H).symm.trans (hyx.trans hy)
        simp [hxr, hrq]
      · have hm : x % q = x-q := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        have hxr : x = r+q := by omega
        have hn : x ≠ r := by omega
        simp only [ite_eq_right H, ite_eq_right hn, ite_eq_left hxr]
    · have hn : x ≠ r := by
        intro h
        apply hy
        rw [← hyx, h, Nat.mod_eq_of_lt hrq]
      have hnq : x ≠ r+q := by
        intro h
        apply hy
        rw [← hyx, h, hshift]
      simp [hDz y hyq hye hy, hn, hnq]
  · intro s hs hsr
    have h := Finset.mem_filter.mp hs
    rw [hDz s (Finset.mem_range.mp h.1) h.2 hsr, mul_zero, zero_mul]
  · intro h
    exact (h (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrq, hre⟩)).elim

end PEqualNP.Outside
