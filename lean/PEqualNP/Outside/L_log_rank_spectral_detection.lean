import Mathlib

private lemma two_value_variance_le_quarter {α : Type} [DecidableEq α]
    (Y : Finset α) (f : α → ℝ) (c : ℝ) (hne : Y.Nonempty)
    (h2 : ∀ B ∈ Y, f B = c ∨ f B = c + 1) :
    (Finset.sum Y (fun B => (f B - Finset.sum Y f / (Y.card : ℝ)) ^ 2)) / (Y.card : ℝ)
      ≤ 1 / 4 := by
  classical
  have hNpos : (0 : ℝ) < (Y.card : ℝ) := by
    have hpos : 0 < Y.card := Finset.card_pos.mpr hne
    exact_mod_cast hpos
  set N : ℝ := (Y.card : ℝ) with hNdef
  set g : α → ℝ := fun B => f B - c with hgdef
  have hgtwo : ∀ B ∈ Y, g B = 0 ∨ g B = 1 := by
    intro B hB
    rcases h2 B hB with h | h
    · left
      have h' : f B - c = 0 := by rw [h]; ring
      exact h'
    · right
      have h' : f B - c = 1 := by rw [h]; ring
      exact h'
  set S : ℝ := Finset.sum Y g with hSdef
  have hSsq : Finset.sum Y (fun B => (g B) ^ 2) = S := by
    rw [hSdef]
    refine Finset.sum_congr rfl ?_
    intro B hB
    rcases hgtwo B hB with h | h <;> rw [h] <;> norm_num
  have hsumf : Finset.sum Y f = S + N * c := by
    calc Finset.sum Y f = Finset.sum Y (fun B => g B + c) := by
          refine Finset.sum_congr rfl ?_
          intro B hB
          simp only [hgdef]
          ring
      _ = S + N * c := by
          rw [Finset.sum_add_distrib, hSdef, Finset.sum_const, nsmul_eq_mul, hNdef]
  have havg : Finset.sum Y f / N = c + S / N := by
    rw [hsumf]
    field_simp
    ring
  have hpt : ∀ B ∈ Y, (f B - Finset.sum Y f / N) ^ 2 = (g B - S / N) ^ 2 := by
    intro B hB
    have hfB : f B = g B + c := by
      simp only [hgdef]
      ring
    rw [hfB, havg]
    ring
  have hkey : Finset.sum Y (fun B => (g B - S / N) ^ 2) = S - S ^ 2 / N := by
    have hpt2 : ∀ B ∈ Y, (g B - S / N) ^ 2 =
        (g B) ^ 2 - 2 * (S / N) * (g B) + (S / N) ^ 2 := by
      intro B hB
      ring
    calc Finset.sum Y (fun B => (g B - S / N) ^ 2)
        = Finset.sum Y (fun B => ((g B) ^ 2 - 2 * (S / N) * (g B) + (S / N) ^ 2)) :=
            Finset.sum_congr rfl hpt2
      _ = S - 2 * (S / N) * S + N * (S / N) ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hSsq]
            rw [← Finset.mul_sum]
            rw [← hSdef, Finset.sum_const, nsmul_eq_mul, ← hNdef]
      _ = S - S ^ 2 / N := by
            field_simp
            ring
  have hSlo : 0 ≤ S := by
    rw [hSdef]
    refine Finset.sum_nonneg ?_
    intro B hB
    rcases hgtwo B hB with h | h
    · have h' : f B - c = 0 := h
      linarith
    · have h' : f B - c = 1 := h
      linarith
  have hShi : S ≤ N := by
    rw [hSdef, hNdef]
    calc Finset.sum Y g ≤ Finset.sum Y (fun _ => (1 : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro B hB
          rcases hgtwo B hB with h | h
          · have h' : f B - c = 0 := h
            linarith
          · have h' : f B - c = 1 := h
            linarith
      _ = (Y.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  have hbound : S * (N - S) ≤ N ^ 2 / 4 := by
    nlinarith [sq_nonneg (N - 2 * S)]
  have hquarter : S * (N - S) / N ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < N ^ 2)]
    nlinarith
  calc (Finset.sum Y (fun B => (f B - Finset.sum Y f / N) ^ 2)) / N
      = (S - S ^ 2 / N) / N := by
        rw [Finset.sum_congr rfl hpt, hkey]
    _ = S * (N - S) / N ^ 2 := by
        field_simp
    _ ≤ 1 / 4 := hquarter

theorem PEqualNP.Outside.L_log_rank_spectral_detection :
    ∀ (n : ℕ) (Y : Finset (Finset (Fin n))) (l : ℝ), 4 ≤ n → Y.Nonempty → let adj := fun (A B : Finset (Fin n)) (a : ℤ) => ((A ∩ B).card : ℤ) = a ∨ ((A ∩ B).card : ℤ) = a+1; let detects := fun (Y : Finset (Finset (Fin n))) => ∀ A : Finset (Fin n), 2 ≤ A.card → A.card + 2 ≤ n → ∀ a : ℤ, ∃ B ∈ Y, ¬ adj A B a; let varY := fun (A : Finset (Fin n)) => let f := fun B : Finset (Fin n) => ((A ∩ B).card : ℝ); let avg := Finset.sum Y f / (Y.card : ℝ); Finset.sum Y (fun B => (f B - avg)^2) / (Y.card : ℝ); (n:ℝ)/(8*((n:ℝ)-2)) < l → (∀ A : Finset (Fin n), l*(A.card:ℝ)*((n:ℝ)-(A.card:ℝ))/(n:ℝ) ≤ varY A) → detects Y := by
  intro n Y l hn hYne
  dsimp only
  intro hlam hvar A hA2 hAn a
  by_contra hcon
  push Not at hcon
  set f : Finset (Fin n) → ℝ := fun B => ((A ∩ B).card : ℝ) with hf
  have h2 : ∀ B ∈ Y, f B = (a : ℝ) ∨ f B = (a : ℝ) + 1 := by
    intro B hB
    have hB' := hcon B hB
    rcases hB' with h | h
    · left
      have hft : f B = ((A ∩ B).card : ℝ) := by simp [hf]
      rw [hft]
      exact_mod_cast h
    · right
      have hft : f B = ((A ∩ B).card : ℝ) := by simp [hf]
      rw [hft]
      have hcast : ((A ∩ B).card : ℝ) = ((a + 1 : ℤ) : ℝ) := by exact_mod_cast h
      push_cast at hcast
      exact hcast
  have hvarub : (Finset.sum Y (fun B => (f B - Finset.sum Y f / (Y.card : ℝ)) ^ 2)) /
      (Y.card : ℝ) ≤ 1 / 4 :=
    two_value_variance_le_quarter Y f (a : ℝ) hYne h2
  have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hnm2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have hlpos : (0 : ℝ) < l := by
    have hden : (0 : ℝ) < 8 * ((n : ℝ) - 2) := by nlinarith
    have hpos : 0 < (n : ℝ) / (8 * ((n : ℝ) - 2)) := div_pos hnpos hden
    linarith
  have hm2 : (2 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hA2
  have hmn : (A.card : ℝ) ≤ (n : ℝ) - 2 := by
    have h : (A.card : ℝ) + 2 ≤ (n : ℝ) := by exact_mod_cast hAn
    linarith
  have hshape : 2 * ((n : ℝ) - 2) ≤ (A.card : ℝ) * ((n : ℝ) - (A.card : ℝ)) := by
    have h1 : 0 ≤ (A.card : ℝ) - 2 := by linarith
    have h2' : 0 ≤ (n : ℝ) - (A.card : ℝ) - 2 := by linarith
    have hprod : 0 ≤ ((A.card : ℝ) - 2) * ((n : ℝ) - (A.card : ℝ) - 2) :=
      mul_nonneg h1 h2'
    nlinarith
  have hquarter : (1 : ℝ) / 4 < l * ((A.card : ℝ) * ((n : ℝ) - (A.card : ℝ)) / (n : ℝ)) := by
    have hden : (0 : ℝ) < 8 * ((n : ℝ) - 2) := by nlinarith
    have hpos2 : (0 : ℝ) < 2 * ((n : ℝ) - 2) / (n : ℝ) :=
      div_pos (by linarith) hnpos
    have hmul := mul_lt_mul_of_pos_right hlam hpos2
    have hstep : l * (2 * ((n : ℝ) - 2) / (n : ℝ)) ≤
        l * ((A.card : ℝ) * ((n : ℝ) - (A.card : ℝ)) / (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hlpos.le
      exact div_le_div_of_nonneg_right hshape hnpos.le
    have hleft : (n : ℝ) / (8 * ((n : ℝ) - 2)) * (2 * ((n : ℝ) - 2) / (n : ℝ)) = 1 / 4 := by
      field_simp
      ring
    linarith
  have heq : l * (A.card : ℝ) * ((n : ℝ) - (A.card : ℝ)) / (n : ℝ) =
      l * ((A.card : ℝ) * ((n : ℝ) - (A.card : ℝ)) / (n : ℝ)) := by ring
  have hlow : l * (A.card : ℝ) * ((n : ℝ) - (A.card : ℝ)) / (n : ℝ) ≤
      (Finset.sum Y (fun B => (f B - Finset.sum Y f / (Y.card : ℝ)) ^ 2)) /
        (Y.card : ℝ) := hvar A
  linarith
