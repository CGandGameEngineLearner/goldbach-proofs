import Mathlib

open scoped BigOperators

private noncomputable def pkE (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

private def kij (i j : ℕ) : ℤ := (2:ℤ)^(i+1) - (2:ℤ)^(j+1)

private lemma pkE_add (x y : ℝ) : pkE x * pkE y = pkE (x + y) := by
  unfold pkE
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma pkE_conj (x : ℝ) : (starRingEnd ℂ) (pkE x) = pkE (-x) := by
  unfold pkE
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

private lemma norm_cast_sq (z : ℂ) : ((‖z‖^2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']

private lemma natCast_ite (c : Prop) [Decidable c] (a b : ℕ) :
    ((if c then a else b : ℕ) : ℂ) = if c then (a:ℂ) else (b:ℂ) := by
  split_ifs <;> simp

private lemma kij_spec (q i j a : ℕ) :
    (((2:ℕ)^(i+1):ℕ):ℝ) * (a:ℝ) / (q:ℝ) + -((((2:ℕ)^(j+1):ℕ):ℝ) * (a:ℝ) / (q:ℝ))
      = ((kij i j : ℤ) : ℝ) * (a:ℝ) / (q:ℝ) := by
  unfold kij
  push_cast
  ring

private lemma dvd_kij_iff (q i j : ℕ) :
    ((q:ℤ) ∣ kij i j) ↔ ((2:ℕ)^(i+1) % q = (2:ℕ)^(j+1) % q) := by
  have h1 : ((kij i j : ℤ) : ZMod q)
      = ((2:ℕ)^(i+1) : ZMod q) - ((2:ℕ)^(j+1) : ZMod q) := by
    unfold kij
    push_cast
    ring
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, h1, sub_eq_zero, ← Nat.cast_pow, ← Nat.cast_pow,
    ZMod.natCast_eq_natCast_iff']

private lemma pair_term (q i j a : ℕ) :
    pkE ((((2:ℕ)^(i+1):ℕ):ℝ) * (a:ℝ) / (q:ℝ))
        * (starRingEnd ℂ) (pkE ((((2:ℕ)^(j+1):ℕ):ℝ) * (a:ℝ) / (q:ℝ)))
      = pkE ((kij i j : ℝ) * (a:ℝ) / (q:ℝ)) := by
  rw [pkE_conj, pkE_add, kij_spec]

private lemma norm_sum_sq_expand (q m a : ℕ) :
    ((‖∑ j ∈ Finset.range m, pkE ((((2:ℕ)^(j+1):ℕ):ℝ) * (a:ℝ) / (q:ℝ))‖^2 : ℝ) : ℂ)
      = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
          pkE ((kij i j : ℝ) * (a:ℝ) / (q:ℝ)) := by
  rw [norm_cast_sq]
  have hconj : (starRingEnd ℂ) (∑ j ∈ Finset.range m,
        pkE ((((2:ℕ)^(j+1):ℕ):ℝ) * (a:ℝ) / (q:ℝ)))
      = ∑ j ∈ Finset.range m,
          (starRingEnd ℂ) (pkE ((((2:ℕ)^(j+1):ℕ):ℝ) * (a:ℝ) / (q:ℝ))) := by
    simpa only [Complex.star_def] using star_sum (Finset.range m)
      (fun j => pkE ((((2:ℕ)^(j+1):ℕ):ℝ) * (a:ℝ) / (q:ℝ)))
  rw [hconj, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  exact pair_term q i j a

private lemma sum_range_eq_sum_zmod (q : ℕ) [NeZero q] (F : ℕ → ℂ) :
    ∑ a ∈ Finset.range q, F a = ∑ x : ZMod q, F (x.val) := by
  have hinj : Set.InjOn (fun a : ℕ => (a : ZMod q)) ↑(Finset.range q) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    rw [ZMod.natCast_eq_natCast_iff'] at hab
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hab
  have hcard : ((Finset.range q).image (fun a : ℕ => (a : ZMod q))).card = Fintype.card (ZMod q) := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, ZMod.card]
  have himg : (Finset.range q).image (fun a : ℕ => (a : ZMod q)) = Finset.univ :=
    Finset.eq_univ_of_card _ hcard
  calc ∑ a ∈ Finset.range q, F a
      = ∑ a ∈ Finset.range q, F ((a : ZMod q).val) := by
        refine Finset.sum_congr rfl (fun a ha => ?_)
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha)]
    _ = ∑ x ∈ (Finset.range q).image (fun a : ℕ => (a : ZMod q)), F (x.val) := by
        rw [Finset.sum_image hinj]
    _ = ∑ x : ZMod q, F (x.val) := by rw [himg]

private lemma sum_pkE_int (q : ℕ) [NeZero q] (k : ℤ) :
    ∑ a ∈ Finset.range q, pkE ((k : ℝ) * (a : ℝ) / (q : ℝ)) =
      if (q : ℤ) ∣ k then (q : ℂ) else 0 := by
  have hterm : ∀ a : ℕ, pkE ((k : ℝ) * (a : ℝ) / (q : ℝ))
      = ZMod.stdAddChar ((k * (a : ℤ) : ℤ) : ZMod q) := by
    intro a
    rw [ZMod.stdAddChar_coe]
    unfold pkE
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun a _ => hterm a)]
  rw [sum_range_eq_sum_zmod q
    (fun a => ZMod.stdAddChar ((k * (a : ℤ) : ℤ) : ZMod q))]
  have hx : ∀ x : ZMod q,
      ZMod.stdAddChar ((k * (x.val : ℤ) : ℤ) : ZMod q) = ZMod.stdAddChar (x * (k : ZMod q)) := by
    intro x
    congr 1
    push_cast
    rw [mul_comm]
    rw [ZMod.natCast_zmod_val]
  rw [Finset.sum_congr rfl (fun x _ => hx x)]
  rw [AddChar.sum_mulShift (k : ZMod q) (ZMod.isPrimitive_stdAddChar q), natCast_ite, ZMod.card]
  have hz : ((k : ZMod q) = 0) ↔ ((q : ℤ) ∣ k) := ZMod.intCast_zmod_eq_zero_iff_dvd k q
  simp only [hz]
  by_cases h : (q : ℤ) ∣ k <;> simp [h]

private lemma card_cond_sum (q m : ℕ) :
    (∑ x ∈ Finset.range m ×ˢ Finset.range m,
        (if ((2:ℕ)^(x.1+1) % q = (2:ℕ)^(x.2+1) % q) then (q:ℂ) else 0))
      = ↑((q:ℝ) * (((Finset.range m ×ˢ Finset.range m).filter
          (fun ij => (2:ℕ)^(ij.1+1)%q = (2:ℕ)^(ij.2+1)%q)).card:ℝ)) := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  push_cast
  ring

private lemma double_sum_cond (q m : ℕ) :
    (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
        (if ((2:ℕ)^(i+1) % q = (2:ℕ)^(j+1) % q) then (q:ℂ) else 0))
      = ∑ x ∈ Finset.range m ×ˢ Finset.range m,
        (if ((2:ℕ)^(x.1+1) % q = (2:ℕ)^(x.2+1) % q) then (q:ℂ) else 0) := by
  rw [Finset.sum_product]

theorem Conjectures.Goldbach.PacketBinaryOrbitSecondMoment :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I);
    ∀ q m : ℕ, 0<q → (∑ a ∈ Finset.range q, ‖∑ j ∈ Finset.range m, E ((((2:ℕ)^(j+1):ℕ):ℝ)*(a:ℝ)/(q:ℝ))‖^2) = (q:ℝ)*(((Finset.range m ×ˢ Finset.range m).filter (fun ij => (2:ℕ)^(ij.1+1)%q = (2:ℕ)^(ij.2+1)%q)).card:ℝ) := by
  intro E q m hq
  have hE : E = pkE := rfl
  rw [hE]
  haveI : NeZero q := ⟨hq.ne'⟩
  have key : ((∑ a ∈ Finset.range q,
        ‖∑ j ∈ Finset.range m, pkE ((((2:ℕ)^(j+1):ℕ):ℝ)*(a:ℝ)/(q:ℝ))‖^2 : ℝ) : ℂ)
      = ↑((q:ℝ) * (((Finset.range m ×ˢ Finset.range m).filter
          (fun ij => (2:ℕ)^(ij.1+1)%q = (2:ℕ)^(ij.2+1)%q)).card:ℝ)) := by
    have hswap : (∑ a ∈ Finset.range q, ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
          pkE ((kij i j : ℝ) * (a:ℝ) / (q:ℝ)))
        = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, ∑ a ∈ Finset.range q,
          pkE ((kij i j : ℝ) * (a:ℝ) / (q:ℝ)) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    calc ((∑ a ∈ Finset.range q,
          ‖∑ j ∈ Finset.range m, pkE ((((2:ℕ)^(j+1):ℕ):ℝ)*(a:ℝ)/(q:ℝ))‖^2 : ℝ) : ℂ)
        = ∑ a ∈ Finset.range q, ((‖∑ j ∈ Finset.range m,
            pkE ((((2:ℕ)^(j+1):ℕ):ℝ)*(a:ℝ)/(q:ℝ))‖^2 : ℝ) : ℂ) := by
          push_cast
          rfl
      _ = ∑ a ∈ Finset.range q, ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
            pkE ((kij i j : ℝ) * (a:ℝ) / (q:ℝ)) := by
          refine Finset.sum_congr rfl (fun a _ => norm_sum_sq_expand q m a)
      _ = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, ∑ a ∈ Finset.range q,
            pkE ((kij i j : ℝ) * (a:ℝ) / (q:ℝ)) := hswap
      _ = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
            (if (q:ℤ) ∣ kij i j then (q:ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          exact sum_pkE_int q (kij i j)
      _ = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
            (if ((2:ℕ)^(i+1) % q = (2:ℕ)^(j+1) % q) then (q:ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          simp only [dvd_kij_iff]
      _ = ∑ x ∈ Finset.range m ×ˢ Finset.range m,
            (if ((2:ℕ)^(x.1+1) % q = (2:ℕ)^(x.2+1) % q) then (q:ℂ) else 0) :=
          double_sum_cond q m
      _ = ↑((q:ℝ) * (((Finset.range m ×ˢ Finset.range m).filter
            (fun ij => (2:ℕ)^(ij.1+1)%q = (2:ℕ)^(ij.2+1)%q)).card:ℝ)) := card_cond_sum q m
  exact Complex.ofReal_inj.mp key
