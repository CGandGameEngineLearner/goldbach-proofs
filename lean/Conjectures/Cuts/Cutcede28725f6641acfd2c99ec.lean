import Mathlib

-- child 1 zh: 排除重排后，控制三元组等和碰撞数。三次多项式允许支撑大小四次幂，更高次数要求三次幂。
-- child 1 en: Bound non-permutation triple collisions by the fourth power of support size for cubics and the third power for higher degrees.
-- child 2 zh: 控制两组四元组完全没有共同指标时的多项式等和碰撞数。
-- child 2 en: Bound the off-diagonal quadruple collisions whose two quadruples have no common index.

theorem Conjectures.Cuts.Cutcede28725f6641acfd2c99ec
  (hTriples : by
    classical
    exact ∀ P : Polynomial ℤ, 3 ≤ P.natDegree → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M →
        let t := Fintype.piFinset (fun _ : Fin 3 => A)
        let w := fun x : Fin 3 → ℕ => ∑ j : Fin 3, P.eval (x j : ℤ)
        (((t.product t).filter (fun z => w z.1 = w z.2 ∧
          ∀ ρ : Equiv.Perm (Fin 3), z.2 ≠ z.1 ∘ ρ)).card : ℝ) ≤
          C * (M : ℝ) ^ ε * (A.card : ℝ) ^ (if P.natDegree = 3 then (4 : ℕ) else 3))
  (hSeparate : by
    classical
    exact ∀ P : Polynomial ℤ, 3 ≤ P.natDegree → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M →
        let t := Fintype.piFinset (fun _ : Fin 4 => A)
        let w := fun x : Fin 4 → ℕ => ∑ j : Fin 4, P.eval (x j : ℤ)
        let f := (t.product t).filter (fun z => w z.1 = w z.2 ∧
          ∀ ρ : Equiv.Perm (Fin 4), z.2 ≠ z.1 ∘ ρ)
        ((f.filter (fun z => ∀ i j : Fin 4, z.1 i ≠ z.2 j)).card : ℝ) ≤
          C * (M : ℝ) ^ ε * (A.card : ℝ) ^ (if P.natDegree = 3 then (5 : ℕ) else 4)) :
    (∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (x10 : Fin (4 : ℕ)) => x8;                   have x11 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x11 : Fin (4 : ℕ) → ℕ) => ∑ x12 : Fin (4 : ℕ), Polynomial.eval (↑(x11 x12)) x1;                   ↑{x12 ∈ x10.product x10 | x11 x12.1 = x11 x12.2 ∧ ∀ (x13 : Equiv.Perm (Fin (4 : ℕ))), x12.2 ≠ x12.1 ∘ ⇑x13}.card ≤ x5 * ↑x6 ^ x3 * ↑x8.card ^ if x1.natDegree = (3 : ℕ) then (5 : ℕ) else (4 : ℕ)) := by
  classical
  intro P hP ε hε
  obtain ⟨C₃, hC₃, bound₃⟩ := hTriples P hP ε hε
  obtain ⟨C₄, hC₄, bound₄⟩ := hSeparate P hP ε hε
  refine ⟨C₄ + 16 * C₃, by positivity, fun M hM A hA => ?_⟩
  let t₃ := Fintype.piFinset (fun _ : Fin 3 => A)
  let t₄ := Fintype.piFinset (fun _ : Fin 4 => A)
  let w₃ := fun x : Fin 3 → ℕ => ∑ j : Fin 3, P.eval (x j : ℤ)
  let w₄ := fun x : Fin 4 → ℕ => ∑ j : Fin 4, P.eval (x j : ℤ)
  let triples := (t₃.product t₃).filter (fun z => w₃ z.1 = w₃ z.2 ∧
    ∀ ρ : Equiv.Perm (Fin 3), z.2 ≠ z.1 ∘ ρ)
  let all := (t₄.product t₄).filter (fun z => w₄ z.1 = w₄ z.2 ∧
    ∀ ρ : Equiv.Perm (Fin 4), z.2 ≠ z.1 ∘ ρ)
  let separate := fun z : (Fin 4 → ℕ) × (Fin 4 → ℕ) => ∀ i j : Fin 4, z.1 i ≠ z.2 j
  let disjoint := all.filter separate
  let shared := all.filter fun z => ¬separate z
  let remove := fun (i : Fin 4) (u : Fin 4 → ℕ) (j : Fin 3) => u (i.succAbove j)

  have option_bijective (i : Fin 4) :
      Function.Bijective (fun a : Option (Fin 3) => a.elim i i.succAbove) := by
    constructor
    · intro a b heq
      cases a with
      | none =>
        cases b with
        | none => rfl
        | some b => exact (Fin.succAbove_ne i b heq.symm).elim
      | some a =>
        cases b with
        | none => exact (Fin.succAbove_ne i a heq).elim
        | some b =>
          have hpositions : i.succAbove a = i.succAbove b := heq
          exact congrArg some (Fin.succAbove_right_injective hpositions)
    · intro j
      by_cases hj : j = i
      · exact ⟨none, hj.symm⟩
      · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hj
        exact ⟨some k, hk⟩
  let positionEquiv (i : Fin 4) : Option (Fin 3) ≃ Fin 4 :=
    Equiv.ofBijective (fun a : Option (Fin 3) => a.elim i i.succAbove) (option_bijective i)
  have extend (i j : Fin 4) (u v : Fin 4 → ℕ) (h : u i = v j)
      (ρ : Equiv.Perm (Fin 3)) (hρ : remove j v = remove i u ∘ ρ) :
      ∃ σ : Equiv.Perm (Fin 4), v = u ∘ σ := by
    let σ : Equiv.Perm (Fin 4) :=
      (positionEquiv j).symm.trans ((Equiv.optionCongr ρ).trans (positionEquiv i))
    refine ⟨σ, ?_⟩
    funext k
    obtain ⟨a, rfl⟩ := (positionEquiv j).surjective k
    change v (positionEquiv j a) = u (σ (positionEquiv j a))
    have hσ : σ (positionEquiv j a) = positionEquiv i ((Equiv.optionCongr ρ) a) := by
      simp only [σ, Equiv.trans_apply, Equiv.symm_apply_apply]
    rw [hσ]
    cases a with
    | none => exact h.symm
    | some b => exact congrFun hρ b

  let positions := fun z : (Fin 4 → ℕ) × (Fin 4 → ℕ) =>
    if h : ∃ p : Fin 4 × Fin 4, z.1 p.1 = z.2 p.2 then Classical.choose h else (0, 0)
  have chosen (z : (Fin 4 → ℕ) × (Fin 4 → ℕ)) (hz : z ∈ shared) :
      z.1 (positions z).1 = z.2 (positions z).2 := by
    have hs : ¬separate z := (Finset.mem_filter.mp hz).2
    have he : ∃ p : Fin 4 × Fin 4, z.1 p.1 = z.2 p.2 := by
      by_contra h
      exact hs (fun i j h' => h ⟨(i, j), h'⟩)
    simpa only [positions, dite_eq_left he] using Classical.choose_spec he
  let pack := fun z : (Fin 4 → ℕ) × (Fin 4 → ℕ) =>
    (positions z, z.1 (positions z).1, remove (positions z).1 z.1, remove (positions z).2 z.2)
  let target := (Finset.univ : Finset (Fin 4 × Fin 4)).product (A.product triples)
  have sum_remove (i : Fin 4) (u : Fin 4 → ℕ) :
      w₄ u = P.eval (u i : ℤ) + w₃ (remove i u) :=
    Fin.sum_univ_succAbove (fun j => P.eval (u j : ℤ)) i
  have pack_mem : Set.MapsTo pack shared target := by
    intro z hz
    change z ∈ shared at hz
    have haz : z ∈ all := (Finset.mem_filter.mp hz).1
    have hm : z ∈ t₄.product t₄ := (Finset.mem_filter.mp haz).1
    have hleft := Fintype.mem_piFinset.mp (Finset.mem_product.mp hm).1
    have hright := Fintype.mem_piFinset.mp (Finset.mem_product.mp hm).2
    have hsum : w₄ z.1 = w₄ z.2 := ((Finset.mem_filter.mp haz).2).1
    have heval := congrArg (fun a : ℕ => P.eval (a : ℤ)) (chosen z hz)
    rw [sum_remove (positions z).1 z.1, sum_remove (positions z).2 z.2, heval] at hsum
    have htriple := add_left_cancel hsum
    have hno (ρ : Equiv.Perm (Fin 3)) :
        remove (positions z).2 z.2 ≠ remove (positions z).1 z.1 ∘ ρ := by
      intro h
      obtain ⟨σ, hσ⟩ := extend _ _ _ _ (chosen z hz) ρ h
      exact ((Finset.mem_filter.mp haz).2).2 σ hσ
    have hu : remove (positions z).1 z.1 ∈ t₃ := Fintype.mem_piFinset.mpr fun i => hleft _
    have hv : remove (positions z).2 z.2 ∈ t₃ := Fintype.mem_piFinset.mpr fun i => hright _
    change pack z ∈ target
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_product.mpr
      ⟨hleft _, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hv⟩, htriple, hno⟩⟩⟩
  have restore (i : Fin 4) (u v : Fin 4 → ℕ)
      (h : u i = v i) (hrest : remove i u = remove i v) : u = v := by
    funext j
    by_cases hj : j = i
    · simpa only [hj] using h
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
      exact congrFun hrest k
  have pack_inj : (shared : Set ((Fin 4 → ℕ) × (Fin 4 → ℕ))).InjOn pack := by
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
  have hshared : shared.card ≤ 16 * A.card * triples.card := by
    calc
      shared.card ≤ target.card := Finset.card_le_card_of_injOn pack pack_mem pack_inj
      _ = _ := by norm_num [target, mul_assoc]
  have hsplit : all.card = disjoint.card + shared.card :=
    (Finset.card_filter_add_card_filter_not (s := all) separate).symm
  let e₃ : ℕ := if P.natDegree = 3 then 4 else 3
  let e₄ : ℕ := if P.natDegree = 3 then 5 else 4
  have hex : e₃ + 1 = e₄ := by
    dsimp only [e₃, e₄]
    split_ifs <;> decide
  have hbound₃ : (triples.card : ℝ) ≤ C₃ * (M : ℝ) ^ ε * (A.card : ℝ) ^ e₃ :=
    bound₃ M hM A hA
  have hbound₄ : (disjoint.card : ℝ) ≤ C₄ * (M : ℝ) ^ ε * (A.card : ℝ) ^ e₄ :=
    bound₄ M hM A hA
  have hsharedCast : (shared.card : ℝ) ≤ 16 * (A.card : ℝ) * (triples.card : ℝ) := by
    exact_mod_cast hshared
  change (all.card : ℝ) ≤ (C₄ + 16 * C₃) * (M : ℝ) ^ ε * (A.card : ℝ) ^ e₄
  rw [hsplit, Nat.cast_add]
  calc
    _ ≤ C₄ * (M : ℝ) ^ ε * (A.card : ℝ) ^ e₄ + 16 * (A.card : ℝ) * (triples.card : ℝ) := by
      exact add_le_add hbound₄ hsharedCast
    _ ≤ C₄ * (M : ℝ) ^ ε * (A.card : ℝ) ^ e₄ +
          16 * (A.card : ℝ) * (C₃ * (M : ℝ) ^ ε * (A.card : ℝ) ^ e₃) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hbound₃ (show 0 ≤ 16 * (A.card : ℝ) by positivity))
    _ = _ := by rw [← hex, pow_succ]; ring
