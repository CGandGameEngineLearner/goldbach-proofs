import Mathlib

theorem PEqualNP.Outside.L_goldbach_coset_sum_reflection :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k%q=r);
    let j := fun n q r : ℕ => (n+q-r)%q;
    ∀ n q r : ℕ, 0<q → r<q → (F n q r).card=(F n q (j n q r)).card := by
  show ∀ n q r : ℕ, 0<q → r<q →
      ((Finset.range (n+1)).filter (fun k => k%q=r)).card
      = ((Finset.range (n+1)).filter (fun k => k%q=(n+q-r)%q)).card
  intro n q r hq hr
  have main : ∀ r' : ℕ, r' ≤ n → r' < q →
      ((Finset.range (n+1)).filter (fun k => k%q=r')).card =
      ((Finset.range (n+1)).filter (fun k => k%q=(n+q-r')%q)).card := by
    intro r' hr'n hr'q
    have hj : (n+q-r')%q = (n-r')%q := by
      have hs : n+q-r' = q+(n-r') := by omega
      rw [hs, Nat.add_mod_left]
    have himg : ((Finset.range (n+1)).filter (fun k => k%q=(n+q-r')%q))
        = ((Finset.range (n+1)).filter (fun k => k%q=r')).image (fun k => n-k) := by
      rw [hj]
      ext k
      rw [Finset.mem_filter, Finset.mem_image]
      constructor
      · intro hk
        obtain ⟨hkrange, hkmod⟩ := hk
        simp only [Finset.mem_range] at hkrange
        have hc : k ≡ (n-r') [MOD q] := hkmod
        have hd : n-k ≡ n-(n-r') [MOD q] := Nat.ModEq.sub_left (by omega) (by omega) hc
        have hsr : n-(n-r') = r' := by omega
        have hd' : (n-k)%q = r'%q := by rw [← hsr]; exact hd
        rw [Nat.mod_eq_of_lt hr'q] at hd'
        have hmem1 : n-k ∈ Finset.range (n+1) := Finset.mem_range.mpr (by omega)
        have hmem2 : n-k ∈ ((Finset.range (n+1)).filter (fun k => k%q=r')) :=
          Finset.mem_filter.mpr ⟨hmem1, hd'⟩
        have hmem3 : n-(n-k) = k := by omega
        exact ⟨n-k, hmem2, hmem3⟩
      · intro hk
        obtain ⟨k', hk', hkk'⟩ := hk
        obtain ⟨hk'range, hk'mod⟩ := Finset.mem_filter.mp hk'
        simp only [Finset.mem_range] at hk'range
        have hc : k'%q = r'%q := by rw [Nat.mod_eq_of_lt hr'q]; exact hk'mod
        have hd : n-k' ≡ n-r' [MOD q] := Nat.ModEq.sub_left (by omega) hr'n hc
        refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
        rw [← hkk']
        exact hd
    rw [himg, Finset.card_image_of_injOn (by
      intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
      have hab' : n-a = n-b := hab
      omega)]
  by_cases hnr : r ≤ n
  · exact main r hnr hr
  · have h1 : ((Finset.range (n+1)).filter (fun k => k%q=r)) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (by
        intro k hk
        intro hcon
        have hle : k%q ≤ k := Nat.mod_le k q
        rw [hcon] at hle
        simp only [Finset.mem_range] at hk
        omega)
    have h2 : ((Finset.range (n+1)).filter (fun k => k%q=(n+q-r)%q)) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (by
        intro k hk
        intro hcon
        have hj : (n+q-r)%q = n+q-r := Nat.mod_eq_of_lt (by omega)
        rw [hj] at hcon
        have hle : k%q ≤ k := Nat.mod_le k q
        rw [hcon] at hle
        simp only [Finset.mem_range] at hk
        omega)
    show ((Finset.range (n+1)).filter (fun k => k%q=r)).card
        = ((Finset.range (n+1)).filter (fun k => k%q=(n+q-r)%q)).card
    rw [h1, h2]
