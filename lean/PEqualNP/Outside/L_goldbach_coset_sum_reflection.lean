import Mathlib

theorem PEqualNP.Outside.L_goldbach_coset_sum_reflection :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k%q=r); let j := fun n q r : ℕ => (n+q-r)%q; ∀ n q r : ℕ, 0<q → r<q → (F n q r).card=(F n q (j n q r)).card := by
  dsimp only
  intro n q r hq hr
  by_cases hrn : r ≤ n
  · have hq1 : n + q - r ≡ n - r [MOD q] := by
      have h : n + q - r = (n - r) + q := by omega
      rw [h]
      exact Nat.add_modulus_modEq_iff.mpr (Nat.ModEq.refl _)
    have key1 : ∀ x ≤ n, x % q = r → (n - x) % q = (n + q - r) % q := by
      intro x hx hxr
      have hrx : r ≤ x := by rw [← hxr]; exact Nat.mod_le x q
      have hxr' : x ≡ r [MOD q] := by rw [hxr, Nat.mod_eq_of_lt hr]
      have h1 : n - x ≡ n - r [MOD q] := Nat.ModEq.sub hx hrx (Nat.ModEq.refl n) hxr'
      exact h1.trans hq1.symm
    have key2 : ∀ x ≤ n, x % q = (n + q - r) % q → (n - x) % q = r := by
      intro x hx hxj
      have h1 : x ≡ n - r [MOD q] := hxj.trans hq1
      have h2 : n - x ≡ n - (n - r) [MOD q] := Nat.ModEq.sub hx (by omega) (Nat.ModEq.refl n) h1
      have h3 : n - (n - r) = r := by omega
      rw [h3] at h2
      rw [h2, Nat.mod_eq_of_lt hr]
    refine Finset.card_bij (fun a _ => n - a) ?_ ?_ ?_
    · intro a ha
      have ha' := Finset.mem_filter.mp ha
      have har : a % q = r := ha'.2
      have hax : a ≤ n := by
        have := Finset.mem_range.mp ha'.1
        omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), key1 a hax har⟩
    · intro a1 ha1 a2 ha2 heq
      have h1 := Finset.mem_filter.mp ha1
      have h2 := Finset.mem_filter.mp ha2
      have hax1 : a1 ≤ n := by
        have := Finset.mem_range.mp h1.1
        omega
      have hax2 : a2 ≤ n := by
        have := Finset.mem_range.mp h2.1
        omega
      omega
    · intro b hb
      have hb' := Finset.mem_filter.mp hb
      have hbj : b % q = (n + q - r) % q := hb'.2
      have hbx : b ≤ n := by
        have := Finset.mem_range.mp hb'.1
        omega
      refine ⟨n - b, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), key2 b hbx hbj⟩
      · omega
  · have hrn' : n < r := by omega
    have hempty1 : (Finset.range (n+1)).filter (fun k => k % q = r) = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro k hk
      have hk' := Finset.mem_filter.mp hk
      have hkx : k ≤ n := by
        have := Finset.mem_range.mp hk'.1
        omega
      have hkle : k % q ≤ k := Nat.mod_le k q
      omega
    have hj : (n + q - r) % q = n + q - r := by
      apply Nat.mod_eq_of_lt
      omega
    have hempty2 : (Finset.range (n+1)).filter (fun k => k % q = (n + q - r) % q) = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro k hk
      have hk' := Finset.mem_filter.mp hk
      have hkx : k ≤ n := by
        have := Finset.mem_range.mp hk'.1
        omega
      have hkle : k % q ≤ k := Nat.mod_le k q
      rw [hj] at hk'
      omega
    rw [hempty1, hempty2]
