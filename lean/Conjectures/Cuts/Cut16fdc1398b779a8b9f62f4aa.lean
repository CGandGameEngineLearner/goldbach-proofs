import Mathlib

-- child 1 zh: 对次数至少为二的整系数多项式，控制同一有限支撑上的二元组等和碰撞数。
-- child 1 en: Bound ordered pair-sum collisions on an arbitrary finite support for integer polynomials of degree at least two.
-- child 2 zh: 两个三元组之间没有共享指标时，控制多项式值的等和碰撞数。
-- child 2 en: Bound ordered triple-sum collisions whose two triples have no common index.

theorem Conjectures.Cuts.Cut16fdc1398b779a8b9f62f4aa
  (hPairs : by
    classical
    exact ∀ P : Polynomial ℤ, 2 ≤ P.natDegree → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M →
        let w := fun x : Fin 2 → ↥A => ∑ j : Fin 2, P.eval ((x j : ℕ) : ℤ)
        let u : Finset ((Fin 2 → ↥A) × (Fin 2 → ↥A)) := Finset.univ
        ((u.filter (fun z => w z.1 = w z.2)).card : ℝ) ≤ C * (M : ℝ) ^ ε * (A.card : ℝ) ^ 2)
  (hSeparate : by
    classical
    exact ∀ P : Polynomial ℤ, 3 ≤ P.natDegree → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M →
        let w := fun x : Fin 3 → ↥A => ∑ j : Fin 3, P.eval ((x j : ℕ) : ℤ)
        let u : Finset ((Fin 3 → ↥A) × (Fin 3 → ↥A)) := Finset.univ
        let all := u.filter (fun z => w z.1 = w z.2)
        ((all.filter (fun z => ∀ i j : Fin 3, z.1 i ≠ z.2 j)).card : ℝ) ≤
          C * (M : ℝ) ^ ε * (A.card : ℝ) ^ 3) :
    (by
  classical
  exact ∀ P : Polynomial ℤ, 3 ≤ P.natDegree → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M →
    let weight := fun x : Fin 3 → (↥A) => ∑ j : Fin 3, P.eval ((x j : ℕ) : ℤ)
    (((Finset.univ : Finset ((Fin 3 → (↥A)) × (Fin 3 → (↥A)))).filter (fun z => weight z.1 = weight z.2)).card : ℝ) ≤ C*(M : ℝ)^ε*(A.card : ℝ)^3) := by
  classical
  intro P hP ε hε
  obtain ⟨C₂, hC₂, bound₂⟩ := hPairs P (by omega) ε hε
  obtain ⟨C₃, hC₃, bound₃⟩ := hSeparate P hP ε hε
  refine ⟨C₃ + 9 * C₂, by positivity, fun M hM A hA => ?_⟩
  let w₂ := fun x : Fin 2 → ↥A => ∑ j : Fin 2, P.eval ((x j : ℕ) : ℤ)
  let w₃ := fun x : Fin 3 → ↥A => ∑ j : Fin 3, P.eval ((x j : ℕ) : ℤ)
  let pairs := (Finset.univ : Finset ((Fin 2 → ↥A) × (Fin 2 → ↥A))).filter
    (fun z => w₂ z.1 = w₂ z.2)
  let all := (Finset.univ : Finset ((Fin 3 → ↥A) × (Fin 3 → ↥A))).filter
    (fun z => w₃ z.1 = w₃ z.2)
  let separate := fun z : (Fin 3 → ↥A) × (Fin 3 → ↥A) =>
    ∀ i j : Fin 3, z.1 i ≠ z.2 j
  let disjoint := all.filter separate
  let shared := all.filter fun z => ¬separate z
  let remove := fun (i : Fin 3) (u : Fin 3 → ↥A) (j : Fin 2) => u (i.succAbove j)
  let positions := fun z : (Fin 3 → ↥A) × (Fin 3 → ↥A) =>
    if h : ∃ p : Fin 3 × Fin 3, z.1 p.1 = z.2 p.2 then Classical.choose h else (0, 0)
  have chosen (z : (Fin 3 → ↥A) × (Fin 3 → ↥A)) (hz : z ∈ shared) :
      z.1 (positions z).1 = z.2 (positions z).2 := by
    have hs : ¬separate z := (Finset.mem_filter.mp hz).2
    have he : ∃ p : Fin 3 × Fin 3, z.1 p.1 = z.2 p.2 := by
      by_contra h
      exact hs (fun i j h' => h ⟨(i, j), h'⟩)
    simpa only [positions, dite_eq_left he] using Classical.choose_spec he
  let pack := fun z : (Fin 3 → ↥A) × (Fin 3 → ↥A) =>
    (positions z, z.1 (positions z).1, remove (positions z).1 z.1, remove (positions z).2 z.2)
  let target :=
    (Finset.univ : Finset (Fin 3 × Fin 3)).product ((Finset.univ : Finset ↥A).product pairs)
  have sum_remove (i : Fin 3) (u : Fin 3 → ↥A) :
      w₃ u = P.eval ((u i : ℕ) : ℤ) + w₂ (remove i u) :=
    Fin.sum_univ_succAbove (fun j => P.eval ((u j : ℕ) : ℤ)) i
  have pack_mem : Set.MapsTo pack shared target := by
    intro z hz
    change z ∈ shared at hz
    have hsum : w₃ z.1 = w₃ z.2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
    have heval := congrArg (fun a : ↥A => P.eval (a.val : ℤ)) (chosen z hz)
    rw [sum_remove (positions z).1 z.1, sum_remove (positions z).2 z.2, heval] at hsum
    have hpair := add_left_cancel hsum
    change pack z ∈ target
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_product.mpr
      ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpair⟩⟩⟩
  have restore (i : Fin 3) (u v : Fin 3 → ↥A)
      (h : u i = v i) (hrest : remove i u = remove i v) : u = v := by
    funext j
    by_cases hj : j = i
    · simpa only [hj] using h
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
      exact congrFun hrest k
  have pack_inj : (shared : Set ((Fin 3 → ↥A) × (Fin 3 → ↥A))).InjOn pack := by
    intro z hz z' hz' h
    have hp : positions z = positions z' := congrArg Prod.fst h
    have hfirst : z.1 (positions z).1 = z'.1 (positions z').1 :=
      congrArg (fun u => u.2.1) h
    have hleft : remove (positions z).1 z.1 = remove (positions z').1 z'.1 :=
      congrArg (fun u => u.2.2.1) h
    have hright : remove (positions z).2 z.2 = remove (positions z').2 z'.2 :=
      congrArg (fun u => u.2.2.2) h
    have hsecond : z.2 (positions z).2 = z'.2 (positions z').2 :=
      (chosen z hz).symm.trans (hfirst.trans (chosen z' hz'))
    rw [← hp] at hfirst hleft hright hsecond
    exact Prod.ext (restore (positions z).1 z.1 z'.1 hfirst hleft)
      (restore (positions z).2 z.2 z'.2 hsecond hright)
  have hshared : shared.card ≤ 9 * A.card * pairs.card := by
    calc
      shared.card ≤ target.card := Finset.card_le_card_of_injOn pack pack_mem pack_inj
      _ = 9 * A.card * pairs.card := by norm_num [target, mul_assoc]
  have hsplit : all.card = disjoint.card + shared.card :=
    (Finset.card_filter_add_card_filter_not (s := all) separate).symm
  have hbound₂ : (pairs.card : ℝ) ≤ C₂ * (M : ℝ) ^ ε * (A.card : ℝ) ^ 2 :=
    bound₂ M hM A hA
  have hbound₃ : (disjoint.card : ℝ) ≤ C₃ * (M : ℝ) ^ ε * (A.card : ℝ) ^ 3 :=
    bound₃ M hM A hA
  have hsharedCast : (shared.card : ℝ) ≤ 9 * (A.card : ℝ) * (pairs.card : ℝ) := by
    exact_mod_cast hshared
  change (all.card : ℝ) ≤ (C₃ + 9 * C₂) * (M : ℝ) ^ ε * (A.card : ℝ) ^ 3
  rw [hsplit, Nat.cast_add]
  calc
    _ ≤ C₃ * (M : ℝ) ^ ε * (A.card : ℝ) ^ 3 + 9 * (A.card : ℝ) * (pairs.card : ℝ) := by
      exact add_le_add hbound₃ hsharedCast
    _ ≤ C₃ * (M : ℝ) ^ ε * (A.card : ℝ) ^ 3 +
          9 * (A.card : ℝ) * (C₂ * (M : ℝ) ^ ε * (A.card : ℝ) ^ 2) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hbound₂ (show 0 ≤ 9 * (A.card : ℝ) by positivity))
    _ = _ := by ring
