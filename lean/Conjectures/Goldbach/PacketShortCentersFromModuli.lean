import Mathlib

private theorem center_count_le (q : ℕ) (hq : 0 < q) (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range (q+1)).filter (fun a => a.Coprime q ∧ P a)).card ≤ 2*q.totient := by
  have hs : (Finset.range (q+1)).filter (fun a => a.Coprime q ∧ P a) ⊆
      insert q ((Finset.range q).filter (fun a => q.Coprime a)) := by
    intro a ha
    obtain ⟨ha, hc, _⟩ := Finset.mem_filter.mp ha
    have h := Finset.mem_range.mp ha
    by_cases he : a = q
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hc.symm⟩))
  have h := (Finset.card_le_card hs).trans (Finset.card_insert_le ..)
  rw [← Nat.totient_eq_card_coprime] at h
  have := Nat.totient_pos.mpr hq
  omega

theorem Conjectures.Goldbach.PacketShortCentersFromModuli :
    (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
     let smooth := fun n q : ℕ => ∀ p ∈ q.primeFactors, p ≤ (1+Nat.log 2 (Q n))^8;
     ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => smooth n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ))/(Nat.totient q:ℝ)) ≤ ε) →
    (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
     let o := fun n q : ℕ => q % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2)).filter (fun j => q ∣ 2^j-1)).Nonempty;
     let smooth := fun n q : ℕ => ∀ p ∈ q.primeFactors, p ≤ (1+Nat.log 2 (Q n))^8;
     ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => o n q ∧ ¬smooth n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ))/(Nat.totient q:ℝ)) ≤ ε) →
    (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
     let L := fun n : ℕ => max 1 (Nat.log 2 n / 2);
     let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ);
     let o := fun n q : ℕ => q % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2)).filter (fun j => q ∣ 2^j-1)).Nonempty;
     ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => o n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ)) * (((Finset.range (q+1)).filter (fun a => Nat.Coprime a q ∧ (1:ℝ)/3 < K n ((a:ℝ)/(q:ℝ)))).card:ℝ) / (Nat.totient q:ℝ)^2) ≤ ε) := by
  intro h₁ h₂ Q L K o ε hε
  obtain ⟨N₁, h₁⟩ := h₁ (ε/4) (by linarith)
  obtain ⟨N₂, h₂⟩ := h₂ (ε/4) (by linarith)
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  let S := Finset.Icc 1 ((Q n)^2)
  let sm := fun q : ℕ => ∀ p ∈ q.primeFactors, p ≤ (1+Nat.log 2 (Q n))^8
  let m := fun q : ℕ => min (1:ℝ) ((q:ℝ)/(Q n:ℝ))
  let w := fun q : ℕ => m q/(q.totient:ℝ)
  let P := fun (q a : ℕ) => (1:ℝ)/3 < K n ((a:ℝ)/(q:ℝ))
  have hm (q : ℕ) : 0 ≤ m q := le_min (by norm_num) (by positivity)
  have hw (q : ℕ) : 0 ≤ w q := div_nonneg (hm q) (by positivity)
  have hs : (∑ q ∈ S.filter sm, w q) ≤ ε/4 := h₁ n ((le_max_left ..).trans hn)
  have ht : (∑ q ∈ S.filter (fun q => o n q ∧ ¬sm q), w q) ≤ ε/4 :=
    h₂ n ((le_max_right ..).trans hn)
  have hsplit : (∑ q ∈ S.filter (o n), w q) ≤ ε/4 + ε/4 := by
    rw [← Finset.sum_filter_add_sum_filter_not (S.filter (o n)) sm]
    simp only [Finset.filter_filter]
    apply add_le_add _ ht
    exact (Finset.sum_le_sum_of_subset_of_nonneg (by
      intro q hq
      obtain ⟨hq, _, hsm⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hq, hsm⟩) (fun q _ _ => hw q)).trans hs
  calc
    _ ≤ ∑ q ∈ S.filter (o n), 2*w q := by
      apply Finset.sum_le_sum
      intro q hq
      have hq' := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
      have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq'
      have hc : (((Finset.range (q+1)).filter (fun a => a.Coprime q ∧ P q a)).card:ℝ)
          ≤ 2*(q.totient:ℝ) := by exact_mod_cast center_count_le q hq' (P q)
      change m q * _ / (q.totient:ℝ)^2 ≤ 2*(m q/(q.totient:ℝ))
      calc
        _ ≤ m q * (2*(q.totient:ℝ)) / (q.totient:ℝ)^2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc (hm q)) (sq_nonneg _)
        _ = _ := by field_simp
    _ = 2 * ∑ q ∈ S.filter (o n), w q := (Finset.mul_sum ..).symm
    _ ≤ ε := by linarith
