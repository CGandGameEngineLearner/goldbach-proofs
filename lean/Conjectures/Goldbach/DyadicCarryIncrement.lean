import Mathlib

private theorem residue_split (N q r : ℕ) (hq : 0 < q) (hr : r < q) :
    let s := (N + q - r) % q
    let t := (N + 2 * q - r) % (2 * q)
    t % q = s ∧ (t < q → t = s) ∧ (q ≤ t → t = s + q) := by
  dsimp
  have hbase : N + 2 * q - r = (N + q - r) + q := by omega
  rw [hbase]
  have hdiv : q ∣ 2 * q := ⟨2, by omega⟩
  have hmod : ((N + q - r + q) % (2 * q)) % q = (N + q - r) % q := by
    rw [Nat.mod_mod_of_dvd _ hdiv, Nat.add_mod_right]
  refine ⟨hmod, ?_, ?_⟩
  · intro ht
    rw [← hmod, Nat.mod_eq_of_lt ht]
  · intro ht
    rw [← hmod]
    have hlt : (N + q - r + q) % (2 * q) < 2 * q := Nat.mod_lt _ (by omega)
    have hsub : (N + q - r + q) % (2 * q) - q < q := by omega
    rw [Nat.mod_eq_sub_mod ht, Nat.mod_eq_of_lt hsub]
    omega

private theorem upper_reflection (N q r : ℕ) (hq : 0 < q) (hr : r < q) :
    (N + 2 * q - (r + q)) % (2 * q) =
      ((N + 2 * q - r) % (2 * q) + q) % (2 * q) := by
  have hleft : N + 2 * q - (r + q) = N + q - r := by omega
  have hright : N + 2 * q - r = (N + q - r) + q := by omega
  rw [hleft, hright]
  rw [Nat.mod_add_mod]
  have hadd : (N + q - r + q + q) = (N + q - r) + 2 * q := by omega
  rw [hadd, Nat.add_mod_right]

private theorem mod_fiber_split (n q r : ℕ) (hq : 0 < q) (hr : r < q) :
    n % q = r ↔ n % (2 * q) = r ∨ n % (2 * q) = r + q := by
  have hdiv : q ∣ 2 * q := ⟨2, by omega⟩
  have hmod : n % (2 * q) % q = n % q := Nat.mod_mod_of_dvd _ hdiv
  constructor
  · intro hn
    have hlt : n % (2 * q) < 2 * q := Nat.mod_lt _ (by omega)
    by_cases hsmall : n % (2 * q) < q
    · left
      rw [← hmod, Nat.mod_eq_of_lt hsmall] at hn
      exact hn
    · right
      have hlarge : q ≤ n % (2 * q) := by omega
      have hsub : n % (2 * q) - q < q := by omega
      rw [← hmod, Nat.mod_eq_sub_mod hlarge, Nat.mod_eq_of_lt hsub] at hn
      omega
  · rintro (hn | hn)
    · rw [← hmod, hn, Nat.mod_eq_of_lt hr]
    · rw [← hmod, hn, Nat.add_mod_right, Nat.mod_eq_of_lt hr]

private theorem fiber_sum_split (N q r : ℕ) (w : ℕ → ℝ)
    (hq : 0 < q) (hr : r < q) :
    (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n % q = r), w n) =
      (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n % (2 * q) = r), w n) +
      (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n % (2 * q) = r + q), w n) := by
  let first := (Finset.range (N + 1)).filter (fun n => n % (2 * q) = r)
  let second := (Finset.range (N + 1)).filter (fun n => n % (2 * q) = r + q)
  have hset : (Finset.range (N + 1)).filter (fun n => n % q = r) = first ∪ second := by
    ext n
    simp only [first, second, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hn, hmod⟩
      rcases (mod_fiber_split n q r hq hr).mp hmod with h | h
      · exact Or.inl ⟨hn, h⟩
      · exact Or.inr ⟨hn, h⟩
    · rintro (⟨hn, h⟩ | ⟨hn, h⟩)
      · exact ⟨hn, (mod_fiber_split n q r hq hr).mpr (Or.inl h)⟩
      · exact ⟨hn, (mod_fiber_split n q r hq hr).mpr (Or.inr h)⟩
  have hdisj : Disjoint first second := by
    apply Finset.disjoint_left.mpr
    intro n hnfirst hnsecond
    have hfirst : n % (2 * q) = r := (Finset.mem_filter.mp hnfirst).2
    have hsecond : n % (2 * q) = r + q := (Finset.mem_filter.mp hnsecond).2
    omega
  rw [hset, Finset.sum_union hdisj]

private theorem reflected_pair (N q r : ℕ) (hq : 0 < q) (hr : r < q) :
    let s := (N + q - r) % q
    let t := (N + 2 * q - r) % (2 * q)
    let u := (N + 2 * q - (r + q)) % (2 * q)
    if t < q then t = s ∧ u = s + q else t = s + q ∧ u = s := by
  dsimp
  have hsplit := residue_split N q r hq hr
  dsimp at hsplit
  have hupper := upper_reflection N q r hq hr
  have ht : (N + 2 * q - r) % (2 * q) < 2 * q := Nat.mod_lt _ (by omega)
  split_ifs with hsmall
  · refine ⟨hsplit.2.1 hsmall, ?_⟩
    rw [hupper, Nat.mod_eq_of_lt (by omega : (N + 2 * q - r) % (2 * q) + q < 2 * q)]
    rw [hsplit.2.1 hsmall]
  · have hlarge : q ≤ (N + 2 * q - r) % (2 * q) := by omega
    refine ⟨hsplit.2.2 hlarge, ?_⟩
    rw [hupper, Nat.mod_eq_sub_mod (by omega : 2 * q ≤
      (N + 2 * q - r) % (2 * q) + q)]
    have hlt : (N + 2 * q - r) % (2 * q) + q - 2 * q < 2 * q := by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega

private theorem pointwise_increment (N q r : ℕ) (a : ℕ → ℝ)
    (hq : 0 < q) (hr : r < q) :
    let s := (N + q - r) % q
    let t := (N + 2 * q - r) % (2 * q)
    let u := (N + 2 * q - (r + q)) % (2 * q)
    2 * (a r * a t + a (r + q) * a u) -
      (a r + a (r + q)) * (a s + a (s + q)) =
      (if t < q then (1 : ℝ) else -1) *
        (a r - a (r + q)) * (a s - a (s + q)) := by
  dsimp
  have hpair := reflected_pair N q r hq hr
  dsimp at hpair
  split_ifs with hsmall
  · simp only [ite_eq_left hsmall] at hpair
    obtain ⟨ht, hu⟩ := hpair
    rw [ht, hu]
    ring
  · simp only [ite_eq_right hsmall] at hpair
    obtain ⟨ht, hu⟩ := hpair
    rw [ht, hu]
    ring

private theorem abstract_increment (N q M : ℕ) (a : ℕ → ℝ) (hq : 0 < q) :
    (2 * q : ℕ) / (M : ℝ) *
      ∑ r ∈ Finset.range (2 * q), a r * a ((N + 2 * q - r) % (2 * q)) -
    (q : ℝ) / M *
      ∑ r ∈ Finset.range q,
        (a r + a (r + q)) *
          (a ((N + q - r) % q) + a ((N + q - r) % q + q)) =
    (q : ℝ) / M *
      ∑ r ∈ Finset.range q,
        (if (N + 2 * q - r) % (2 * q) < q then (1 : ℝ) else -1) *
          (a r - a (r + q)) *
          (a ((N + q - r) % q) - a ((N + q - r) % q + q)) := by
  have hsum :
      (∑ r ∈ Finset.range (2 * q), a r * a ((N + 2 * q - r) % (2 * q))) =
      ∑ r ∈ Finset.range q,
        (a r * a ((N + 2 * q - r) % (2 * q)) +
          a (r + q) * a ((N + 2 * q - (r + q)) % (2 * q))) := by
    conv_lhs => rw [show 2 * q = q + q by omega, Finset.sum_range_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [two_mul, add_comm q r]
  rw [hsum]
  have hcast : ((2 * q : ℕ) : ℝ) / M = 2 * ((q : ℝ) / M) := by
    push_cast
    ring
  rw [hcast]
  calc
    2 * ((q : ℝ) / M) *
        (∑ r ∈ Finset.range q,
          (a r * a ((N + 2 * q - r) % (2 * q)) +
            a (r + q) * a ((N + 2 * q - (r + q)) % (2 * q)))) -
        (q : ℝ) / M *
          (∑ r ∈ Finset.range q,
            (a r + a (r + q)) *
              (a ((N + q - r) % q) + a ((N + q - r) % q + q))) =
      (q : ℝ) / M *
        (∑ r ∈ Finset.range q,
          (2 * (a r * a ((N + 2 * q - r) % (2 * q)) +
            a (r + q) * a ((N + 2 * q - (r + q)) % (2 * q))) -
          (a r + a (r + q)) *
            (a ((N + q - r) % q) + a ((N + q - r) % q + q)))) := by
            rw [Finset.sum_sub_distrib]
            rw [← Finset.mul_sum]
            ring
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      exact pointwise_increment N q r a hq (Finset.mem_range.mp hr)

theorem Conjectures.Goldbach.DyadicCarryIncrement :
    ∀ (N q M : ℕ) (w : ℕ → ℝ), 0 < q → 0 < M →
      let A := fun (d r : ℕ) =>
        ∑ n ∈ (Finset.range (N + 1)).filter (fun n => n % d = r), w n
      let R := fun d : ℕ =>
        (d : ℝ) / M * ∑ r ∈ Finset.range d, A d r * A d ((N + d - r) % d)
      let D := fun r : ℕ => A (2 * q) r - A (2 * q) (r + q)
      R (2 * q) - R q = (q : ℝ) / M * ∑ r ∈ Finset.range q,
        (if (N + 2 * q - r) % (2 * q) < q then (1 : ℝ) else -1) *
          D r * D ((N + q - r) % q) := by
  intro N q M w hq hM
  let A := fun (d r : ℕ) =>
    ∑ n ∈ (Finset.range (N + 1)).filter (fun n => n % d = r), w n
  let R := fun d : ℕ =>
    (d : ℝ) / M * ∑ r ∈ Finset.range d, A d r * A d ((N + d - r) % d)
  let D := fun r : ℕ => A (2 * q) r - A (2 * q) (r + q)
  let a := A (2 * q)
  have hproj (r : ℕ) (hr : r < q) : A q r = a r + a (r + q) :=
    fiber_sum_split N q r w hq hr
  change R (2 * q) - R q = (q : ℝ) / M * ∑ r ∈ Finset.range q,
    (if (N + 2 * q - r) % (2 * q) < q then (1 : ℝ) else -1) *
      D r * D ((N + q - r) % q)
  have hcoarse : R q = (q : ℝ) / M * ∑ r ∈ Finset.range q,
      (a r + a (r + q)) *
        (a ((N + q - r) % q) + a ((N + q - r) % q + q)) := by
    unfold R
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    rw [hproj r (Finset.mem_range.mp hr),
      hproj ((N + q - r) % q) (Nat.mod_lt _ hq)]
  rw [hcoarse]
  change ((2 * q : ℕ) : ℝ) / M *
      (∑ r ∈ Finset.range (2 * q), a r * a ((N + 2 * q - r) % (2 * q))) -
      (q : ℝ) / M *
      (∑ r ∈ Finset.range q,
        (a r + a (r + q)) *
          (a ((N + q - r) % q) + a ((N + q - r) % q + q))) =
      (q : ℝ) / M *
      (∑ r ∈ Finset.range q,
        (if (N + 2 * q - r) % (2 * q) < q then (1 : ℝ) else -1) *
          (a r - a (r + q)) *
          (a ((N + q - r) % q) - a ((N + q - r) % q + q)))
  exact abstract_increment N q M a hq
