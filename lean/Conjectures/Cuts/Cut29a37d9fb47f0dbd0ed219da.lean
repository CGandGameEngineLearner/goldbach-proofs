import Mathlib

noncomputable section
-- child 1 zh: 存在固定截顶和分离参数，使中央窗内处于平方根端或标签近对角薄带的双半素数配对，最终至多占终筛体积的 1/1000。
-- child 1 en: There are fixed cap and separation parameters for which the square-root endpoint and the near-diagonal least-factor bands together eventually contribute at most 1/1000 of the terminal volume.
-- child 2 zh: 在中央窗内按较大的最小素因子定向。固定幂次截顶并隔开两侧标签后，恰有一侧最小素因子超过 n 的 2/5 次幂的配对，最终至多占终筛体积的 109/1000。
-- child 2 en: In the central window orient the pairs by the larger least prime factor. For every fixed power cap and separation as stated, the pairs with exactly one least prime factor above n to the power 2/5 eventually occupy at most 109/1000 of the terminal sieve volume.
-- child 3 zh: 同样定向、截顶并隔开标签。两侧最小素因子均超过 n 的 2/5 次幂的配对，最终至多占终筛体积的 159/2000。
-- child 3 en: With the stated orientation, fixed power cap and separation, the pairs with both least prime factors above n to the power 2/5 eventually occupy at most 159/2000 of the terminal sieve volume.
theorem Conjectures.Cuts.Cut29a37d9fb47f0dbd0ed219da
    (hthin :
      have window : ℕ → Finset ℕ := fun n => Finset.Icc ((n + 2) / 3) (2 * n / 3);
      have cubeCut : ℕ → ℕ := fun n => ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊;
      have pairs : ℕ → Finset ℕ := fun n =>
        (window n).filter fun m =>
          (cubeCut n < m.minFac ∧ Nat.Prime m.minFac ∧ Nat.Prime (m / m.minFac)) ∧
          (cubeCut n < (n - m).minFac ∧ Nat.Prime (n - m).minFac ∧
            Nat.Prime ((n - m) / (n - m).minFac));
      have volume : ℕ → ℝ := fun n =>
        ((window n).card : ℝ) * (n.totient : ℝ) / (n : ℝ) *
          ∏ p ∈ (Finset.Icc 2 n.sqrt).filter Nat.Prime with ¬p ∣ n, (1 - 2 / (p : ℝ));
      have powerCap : ℕ → ℝ → ℕ := fun n δ => ⌊(n : ℝ) ^ (1 / 2 - δ)⌋₊;

      have omitted : ℕ → ℝ → ℝ → Finset ℕ := fun n δ η =>
        (pairs n).filter fun m =>
          powerCap n δ < m.minFac ∨ powerCap n δ < (n - m).minFac ∨
          ((n - m).minFac : ℝ) ≤ (m.minFac : ℝ) * (n : ℝ) ^ η ∧
          (m.minFac : ℝ) ≤ ((n - m).minFac : ℝ) * (n : ℝ) ^ η;
      ∃ δ η : ℝ, 0 < δ ∧ δ < 1 / 10 ∧ 0 < η ∧
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
          ((omitted n δ η).card : ℝ) ≤ (1 / 1000 : ℝ) * volume n)
    (hone :
      have window : ℕ → Finset ℕ := fun n => Finset.Icc ((n + 2) / 3) (2 * n / 3);
      have cubeCut : ℕ → ℕ := fun n => ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊;
      have pairs : ℕ → Finset ℕ := fun n =>
        (window n).filter fun m =>
          (cubeCut n < m.minFac ∧ Nat.Prime m.minFac ∧ Nat.Prime (m / m.minFac)) ∧
          (cubeCut n < (n - m).minFac ∧ Nat.Prime (n - m).minFac ∧
            Nat.Prime ((n - m) / (n - m).minFac));
      have volume : ℕ → ℝ := fun n =>
        ((window n).card : ℝ) * (n.totient : ℝ) / (n : ℝ) *
          ∏ p ∈ (Finset.Icc 2 n.sqrt).filter Nat.Prime with ¬p ∣ n, (1 - 2 / (p : ℝ));
      have powerCap : ℕ → ℝ → ℕ := fun n δ => ⌊(n : ℝ) ^ (1 / 2 - δ)⌋₊;

      have twoFifths : ℕ → ℕ := fun n => ⌊(n : ℝ) ^ (2 / 5 : ℝ)⌋₊;
      have separated : ℕ → ℝ → ℝ → Finset ℕ := fun n δ η =>
        (pairs n).filter fun m =>
          m.minFac ≤ powerCap n δ ∧ (n - m).minFac ≤ powerCap n δ ∧
          twoFifths n < m.minFac ∧
          ((n - m).minFac : ℝ) * (n : ℝ) ^ η < (m.minFac : ℝ);
      ∀ δ η : ℝ, 0 < δ → δ < 1 / 10 → 0 < η →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
          (((separated n δ η).filter fun m => (n - m).minFac ≤ twoFifths n).card : ℝ) ≤
            (109 / 1000 : ℝ) * volume n)
    (htwo :
      have window : ℕ → Finset ℕ := fun n => Finset.Icc ((n + 2) / 3) (2 * n / 3);
      have cubeCut : ℕ → ℕ := fun n => ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊;
      have pairs : ℕ → Finset ℕ := fun n =>
        (window n).filter fun m =>
          (cubeCut n < m.minFac ∧ Nat.Prime m.minFac ∧ Nat.Prime (m / m.minFac)) ∧
          (cubeCut n < (n - m).minFac ∧ Nat.Prime (n - m).minFac ∧
            Nat.Prime ((n - m) / (n - m).minFac));
      have volume : ℕ → ℝ := fun n =>
        ((window n).card : ℝ) * (n.totient : ℝ) / (n : ℝ) *
          ∏ p ∈ (Finset.Icc 2 n.sqrt).filter Nat.Prime with ¬p ∣ n, (1 - 2 / (p : ℝ));
      have powerCap : ℕ → ℝ → ℕ := fun n δ => ⌊(n : ℝ) ^ (1 / 2 - δ)⌋₊;

      have twoFifths : ℕ → ℕ := fun n => ⌊(n : ℝ) ^ (2 / 5 : ℝ)⌋₊;
      have separated : ℕ → ℝ → ℝ → Finset ℕ := fun n δ η =>
        (pairs n).filter fun m =>
          m.minFac ≤ powerCap n δ ∧ (n - m).minFac ≤ powerCap n δ ∧
          twoFifths n < m.minFac ∧
          ((n - m).minFac : ℝ) * (n : ℝ) ^ η < (m.minFac : ℝ);
      ∀ δ η : ℝ, 0 < δ → δ < 1 / 10 → 0 < η →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
          (((separated n δ η).filter fun m => twoFifths n < (n - m).minFac).card : ℝ) ≤
            (159 / 2000 : ℝ) * volume n) :
    (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → Finset ℕ := fun (x2 : ℕ) => Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) x2); have x3 : ℕ → Finset ℕ := fun (x3 : ℕ) => {x4 ∈ x1 x3 | ⌊(↑x3 : ℝ) ^ (1 / 3 : ℝ)⌋₊ < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)}; have x4 : ℕ → ℝ := fun (x4 : ℕ) => (↑(x1 x4).card : ℝ) * (↑x4.totient : ℝ) / (↑x4 : ℝ) * ∏ x5 ∈ x2 x4.sqrt with ¬x5 ∣ x4, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ)); have x5 : ℕ → Finset ℕ := fun (x5 : ℕ) => {x6 ∈ x3 x5 | x5 - x6 ∈ x3 x5}; have x6 : ℕ → ℕ := fun (x6 : ℕ) => ⌊Real.exp (Real.log (↑x6 : ℝ) / (2 : ℝ) - (2 : ℝ) * Real.log (↑x6 : ℝ) ^ (2 / 3 : ℝ))⌋₊; have x7 : ℕ → ℕ := fun (x7 : ℕ) => ⌊(↑x7 : ℝ) ^ (2 / 5 : ℝ)⌋₊; ∃ (x8 : ℕ), ∀ (x9 : ℕ), x8 ≤ x9 → Even x9 → (↑{x12 ∈ x5 x9 | x12.minFac ≤ x6 x9 ∧ (x9 - x12).minFac ≤ x6 x9 ∧ (x7 x9 < x12.minFac ∨ x7 x9 < (x9 - x12).minFac)}.card : ℝ) ≤ (189 / 500 : ℝ) * x4 x9) := by
  obtain ⟨δ, η, hδ, hδ', hη, Nbad, hNbad⟩ := hthin
  obtain ⟨None, hNone⟩ := hone δ η hδ hδ' hη
  obtain ⟨Ntwo, hNtwo⟩ := htwo δ η hδ hδ' hη
  refine ⟨max 1 (max Nbad (max None Ntwo)), ?_⟩
  intro n hn he
  let window := Finset.Icc ((n + 2) / 3) (2 * n / 3)
  let rough (m : ℕ) : Prop :=
    ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ < m.minFac ∧
      Nat.Prime m.minFac ∧ Nat.Prime (m / m.minFac)
  let semiprimes := window.filter rough
  let pairs := window.filter fun m => rough m ∧ rough (n - m)
  let cap := ⌊(n : ℝ) ^ (1 / 2 - δ)⌋₊
  let endpoint := ⌊Real.exp (Real.log (n : ℝ) / 2 -
    2 * Real.log (n : ℝ) ^ (2 / 3 : ℝ))⌋₊
  let high := ⌊(n : ℝ) ^ (2 / 5 : ℝ)⌋₊
  let volume := (window.card : ℝ) * (n.totient : ℝ) / (n : ℝ) *
    ∏ p ∈ (Finset.Icc 2 n.sqrt).filter Nat.Prime with ¬p ∣ n, (1 - 2 / (p : ℝ))
  let omitted := pairs.filter fun m =>
    cap < m.minFac ∨ cap < (n - m).minFac ∨
      ((n - m).minFac : ℝ) ≤ (m.minFac : ℝ) * (n : ℝ) ^ η ∧
      (m.minFac : ℝ) ≤ ((n - m).minFac : ℝ) * (n : ℝ) ^ η
  let left := pairs.filter fun m =>
    m.minFac ≤ cap ∧ (n - m).minFac ≤ cap ∧ high < m.minFac ∧
      ((n - m).minFac : ℝ) * (n : ℝ) ^ η < (m.minFac : ℝ)
  let crossed := left.filter fun m => (n - m).minFac ≤ high
  let above := left.filter fun m => high < (n - m).minFac
  let target := (semiprimes.filter fun m => n - m ∈ semiprimes).filter fun m =>
    m.minFac ≤ endpoint ∧ (n - m).minFac ≤ endpoint ∧
      (high < m.minFac ∨ high < (n - m).minFac)
  change (target.card : ℝ) ≤ (189 / 500 : ℝ) * volume
  have hnpos : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hscale : (1 : ℝ) ≤ (n : ℝ) ^ η :=
    Real.one_le_rpow (by exact_mod_cast hnpos) hη.le
  have reflect {m : ℕ} (hm : m ∈ pairs) : n - m ∈ pairs := by
    obtain ⟨hw, hleft, hright⟩ := Finset.mem_filter.mp hm
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hw
    have hback : n - (n - m) = m := by omega
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hright, by simpa only [hback]⟩
  have chooseHigh {p r : ℕ} (hgap : (r : ℝ) * (n : ℝ) ^ η < (p : ℝ))
      (hhigh : high < p ∨ high < r) : high < p := by
    have hle : (r : ℝ) ≤ (r : ℝ) * (n : ℝ) ^ η := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hscale
        (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
    have hlt : r < p := by exact_mod_cast hle.trans_lt hgap
    exact hhigh.elim id fun h => h.trans hlt
  have cover : target ⊆ omitted ∪ (left ∪ left.image (fun m => n - m)) := by
    intro m hm
    by_cases hb : m ∈ omitted
    · exact Finset.mem_union_left _ hb
    obtain ⟨hboth, _, _, hhigh⟩ := Finset.mem_filter.mp hm
    obtain ⟨hl, hr⟩ := Finset.mem_filter.mp hboth
    have hleft := Finset.mem_filter.mp hl
    have hright := Finset.mem_filter.mp hr
    have hpairs : m ∈ pairs := Finset.mem_filter.mpr ⟨hleft.1, hleft.2, hright.2⟩
    have hcapL : m.minFac ≤ cap := by
      by_contra! hc
      exact hb (Finset.mem_filter.mpr ⟨hpairs, Or.inl hc⟩)
    have hcapR : (n - m).minFac ≤ cap := by
      by_contra! hc
      exact hb (Finset.mem_filter.mpr ⟨hpairs, Or.inr (Or.inl hc)⟩)
    apply Finset.mem_union_right
    by_cases hgap : ((n - m).minFac : ℝ) * (n : ℝ) ^ η < (m.minFac : ℝ)
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hpairs, hcapL, hcapR, chooseHigh hgap hhigh, hgap⟩)
    · have hother : (m.minFac : ℝ) * (n : ℝ) ^ η < ((n - m).minFac : ℝ) := by
        by_contra! h
        exact hb (Finset.mem_filter.mpr ⟨hpairs, Or.inr (Or.inr ⟨h, le_of_not_gt hgap⟩)⟩)
      have hhi : m ≤ 2 * n / 3 := (Finset.mem_Icc.mp hleft.1).2
      have hback : n - (n - m) = m := by omega
      have hin : n - m ∈ left := by
        refine Finset.mem_filter.mpr
          ⟨reflect hpairs, hcapR, ?_, chooseHigh hother hhigh.symm, ?_⟩
        · simpa only [hback] using hcapL
        · simpa only [hback] using hother
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨n - m, hin, hback⟩)
  have hcount : target.card ≤ omitted.card + 2 * left.card := by
    have h₁ := Finset.card_le_card cover
    have h₂ := Finset.card_union_le omitted (left ∪ left.image (fun m => n - m))
    have h₃ := Finset.card_union_le left (left.image (fun m => n - m))
    have h₄ : (left.image fun m => n - m).card ≤ left.card := Finset.card_image_le
    omega
  have hpart : crossed.card + above.card = left.card := by
    simpa only [crossed, above, not_le] using
      (Finset.card_filter_add_card_filter_not
        (fun m : ℕ => (n - m).minFac ≤ high) (s := left))
  have hcountR : (target.card : ℝ) ≤ (omitted.card : ℝ) + 2 * (left.card : ℝ) := by
    exact_mod_cast hcount
  have hpartR : (crossed.card : ℝ) + (above.card : ℝ) = (left.card : ℝ) := by
    exact_mod_cast hpart
  have hNbad' : Nbad ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hNone' : None ≤ n :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hNtwo' : Ntwo ≤ n :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have htail : (omitted.card : ℝ) ≤ (1 / 1000 : ℝ) * volume := by
    convert hNbad n hNbad' he using 1
  have hcrossed : (crossed.card : ℝ) ≤ (109 / 1000 : ℝ) * volume := by
    convert hNone n hNone' he using 1
  have habove : (above.card : ℝ) ≤ (159 / 2000 : ℝ) * volume := by
    convert hNtwo n hNtwo' he using 1
  linarith only [hcountR, hpartR, htail, hcrossed, habove]
end
