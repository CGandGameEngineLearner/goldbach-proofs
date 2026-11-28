import Mathlib

private def digit (b n i : ℕ) := n / b^i % b

private def words (b : ℕ) (D : Finset ℕ) (k : ℕ) :=
  (Finset.range (b^k)).filter fun n =>
    (∀ i < k, digit b n i ∈ D) ∧ ∀ i < k-1, digit b n i ≠ digit b n (i+1)

private def fiber (b : ℕ) (D : Finset ℕ) (j a : ℕ) :=
  (words b D (j+1)).filter fun n => digit b n j = a

private theorem mem_words {b n k : ℕ} {D : Finset ℕ} :
    n ∈ words b D k ↔ n < b^k ∧ (∀ i < k, digit b n i ∈ D) ∧
      ∀ i < k-1, digit b n i ≠ digit b n (i+1) := by
  simp only [words, Finset.mem_filter, Finset.mem_range]

private theorem lower_digit (b n a k i : ℕ) (hi : i < k) :
    digit b (n+a*b^k) i = digit b n i := by
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le (show i+1 ≤ k by omega)
  unfold digit
  rw [hd, pow_add, pow_succ]
  have e : a * (b^i*b*b^d) = b^i * (b*(a*b^d)) := by ring
  rw [e]
  by_cases h : b=0
  · subst b; simp
  rw [Nat.add_mul_div_left _ _ (pow_pos (Nat.pos_of_ne_zero h) _), Nat.add_mul_mod_self_left]

private theorem top_digit (b n a k : ℕ) (hb : 0 < b) (hn : n < b^k) (ha : a < b) :
    digit b (n+a*b^k) k = a := by
  simp [digit, Nat.add_mul_div_right _ _ (pow_pos hb k), Nat.div_eq_of_lt hn, Nat.mod_eq_of_lt ha]

private theorem step_mem {b n a j : ℕ} {D : Finset ℕ} (hb : 0 < b)
    (hn : n < b^(j+1)) (ha : a ∈ D) (hab : a < b) :
    n+a*b^(j+1) ∈ fiber b D (j+1) a ↔
      n ∈ words b D (j+1) ∧ digit b n j ≠ a := by
  let K := b^(j+1)
  have htop := top_digit b n a (j+1) hb hn hab
  have hlt : n + a * b^(j+1) < b^(j+1+1) := by
    rw [pow_succ b (j+1), Nat.mul_comm (b^(j+1)) b]
    calc
      _ < (a+1)*b^(j+1) := by rw [Nat.succ_mul]; omega
      _ ≤ _ := Nat.mul_le_mul_right _ hab
  simp only [fiber, Finset.mem_filter, mem_words, htop, and_true]
  constructor
  · rintro ⟨_,hD,hneq⟩
    refine ⟨⟨hn,fun i hi => ?_,fun i hi => ?_⟩,?_⟩
    · simpa [lower_digit b n a _ i hi] using hD i (by omega)
    · simpa [lower_digit b n a _ i (by omega : i < j+1),
        lower_digit b n a _ (i+1) (by omega : i+1 < j+1)] using hneq i (by omega)
    · simpa [lower_digit b n a _ j (by omega : j < j+1),htop] using hneq j (by omega)
  · rintro ⟨⟨_,hD,hneq⟩,hlast⟩
    refine ⟨hlt,fun i hi => ?_,fun i hi => ?_⟩
    · by_cases h : i < j+1
      · simpa [lower_digit b n a _ i h] using hD i h
      · have : i=j+1 := by omega
        simpa [this,htop] using ha
    · by_cases h : i < j
      · simpa [lower_digit b n a _ i (by omega : i < j+1),
          lower_digit b n a _ (i+1) (by omega : i+1 < j+1)] using hneq i (by omega)
      · have : i=j := by omega
        simpa [this,lower_digit b n a _ j (by omega : j < j+1),htop] using hlast

private noncomputable def digitPhase (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (((2*Real.pi*((n:ℝ)*t):ℝ):ℂ)*Complex.I)

private theorem digitPhase_add (n m : ℕ) (t : ℝ) :
    digitPhase (n+m) t = digitPhase m t * digitPhase n t := by
  unfold digitPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem fiber_image {b j a : ℕ} {D : Finset ℕ} (hb : 0 < b) (ha : a ∈ D)
    (hab : a < b) :
    fiber b D (j+1) a =
      ((words b D (j+1)).filter fun n => digit b n j ≠ a).image (fun n => n+a*b^(j+1)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hw,ht⟩ := Finset.mem_filter.mp hx
    have hlt := (mem_words.mp hw).1
    have hk : 0 < b^(j+1) := pow_pos hb _
    have hq : x / b^(j+1) < b := (Nat.div_lt_iff_lt_mul hk).mpr (by simpa [pow_succ b (j+1),Nat.mul_comm] using hlt)
    have he : x / b^(j+1) = a := by simpa [digit,Nat.mod_eq_of_lt hq] using ht
    let n := x % b^(j+1)
    have hn : n < b^(j+1) := Nat.mod_lt _ hk
    have hx' : n+a*b^(j+1)=x := by simpa [n,← he,Nat.mul_comm] using Nat.mod_add_div x (b^(j+1))
    exact Finset.mem_image.mpr ⟨n, Finset.mem_filter.mpr ((step_mem hb hn ha hab).mp (hx' ▸ hx)), hx'⟩
  · rintro h
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hn,hn'⟩ := Finset.mem_filter.mp hn
    exact (step_mem hb (mem_words.mp hn).1 ha hab).mpr ⟨hn,hn'⟩

private noncomputable def row (b : ℕ) (D : Finset ℕ) : ℕ → ℕ → ℝ → ℂ :=
  Nat.rec digitPhase (fun i prev a t =>
    digitPhase (a*b^(i+1)) t * ∑ c ∈ D.filter (fun c => c ≠ a), prev c t)

private theorem fiber_sum {b : ℕ} {D : Finset ℕ} (hb : 0 < b) (hD : D ⊆ Finset.range b)
    (j : ℕ) (a : ℕ) (ha : a ∈ D) (t : ℝ) :
    ∑ n ∈ fiber b D j a, digitPhase n t = row b D j a t := by
  induction j generalizing a with
  | zero =>
    have ha' := Finset.mem_range.mp (hD ha)
    have h : fiber b D 0 a = {a} := by
      ext n
      simp only [fiber, Finset.mem_filter, mem_words, Finset.mem_singleton, zero_add, pow_one]
      constructor
      · rintro ⟨⟨hn,_,_⟩,he⟩
        simpa [digit,Nat.mod_eq_of_lt hn] using he
      · rintro rfl
        simp [digit,ha',Nat.mod_eq_of_lt ha',ha]
    simp [h,row]
  | succ j ih =>
    let S := (words b D (j+1)).filter (fun n => digit b n j ≠ a)
    let A := D.filter (fun c => c ≠ a)
    have maps : (S : Set ℕ).MapsTo (fun n => digit b n j) A := by
      intro n hn
      obtain ⟨hw,he⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨(mem_words.mp hw).2.1 j (by omega),he⟩
    have fibers (c : ℕ) (hc : c ∈ A) :
        S.filter (fun n => digit b n j = c) = fiber b D j c := by
      ext n
      have hca := (Finset.mem_filter.mp hc).2
      simp only [S,fiber,Finset.mem_filter]
      grind
    change _ = digitPhase (a*b^(j+1)) t * ∑ c ∈ A, row b D j c t
    rw [fiber_image hb ha (Finset.mem_range.mp (hD ha)), Finset.sum_image (by intro n _ m _ h; exact Nat.add_right_cancel h)]
    simp_rw [digitPhase_add]
    rw [← Finset.mul_sum]
    apply congrArg (fun z : ℂ => digitPhase (a*b^(j+1)) t * z)
    calc
      _ = ∑ c ∈ A, ∑ n ∈ S.filter (fun n => digit b n j = c), digitPhase n t :=
        (Finset.sum_fiberwise_of_maps_to maps _).symm
      _ = _ := Finset.sum_congr rfl (fun c hc => by
        rw [fibers c hc, ih c (Finset.mem_filter.mp hc).1])

private theorem row_zero {b : ℕ} {D : Finset ℕ} (j a : ℕ) (ha : a ∈ D) :
    row b D j a 0 = ((D.card-1 : ℕ) : ℂ)^j := by
  induction j generalizing a with
  | zero => simp [row,digitPhase]
  | succ j ih =>
    change digitPhase (a*b^(j+1)) 0 * (∑ c ∈ D.filter (fun c => c ≠ a), row b D j c 0) = _
    have he : D.filter (fun c => c ≠ a) = D.erase a := by ext; simp [and_comm]
    simp only [digitPhase, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
    rw [he, Finset.sum_congr (s₁ := D.erase a) rfl (fun c hc => ih c (Finset.mem_of_mem_erase hc))]
    simp [Finset.card_erase_of_mem ha, nsmul_eq_mul, pow_succ, mul_comm]

theorem Conjectures.Cuts.Task1a8aa0206aba2aaafc6f8c68 : (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => Complex.exp (↑((2 : ℝ) * Real.pi * (↑x1 * x2)) * Complex.I); have x2 : ℕ → Finset ℕ → ℕ → Finset ℕ := fun (x2 : ℕ) (x3 : Finset ℕ) (x4 : ℕ) => {x5 ∈ Finset.range (x2 ^ x4) | (∀ x6 < x4, x5 / x2 ^ x6 % x2 ∈ x3) ∧ ∀ x6 < x4 - (1 : ℕ), x5 / x2 ^ x6 % x2 ≠ x5 / x2 ^ (x6 + (1 : ℕ)) % x2}; have x3 : ℕ → Finset ℕ → ℕ → ℕ → ℝ → ℂ := fun (x3 : ℕ) (x4 : Finset ℕ) (x5 : ℕ) => Nat.rec (motive := fun (x6 : ℕ) => ℕ → ℝ → ℂ) x1 (fun (x6 : ℕ) (x7 : ℕ → ℝ → ℂ) (x8 : ℕ) (x9 : ℝ) => x1 (x8 * x3 ^ (x6 + (1 : ℕ))) x9 * ∑ x10 ∈ x4 with x10 ≠ x8, x7 x10 x9) x5; ∀ (x4 : ℕ), (2 : ℕ) ≤ x4 → ∀ x6 ⊆ Finset.range x4, (2 : ℕ) ≤ x6.card → ∀ (x9 : ℕ), (∀ (x10 : ℝ), ∑ x11 ∈ x2 x4 x6 (x9 + (1 : ℕ)), x1 x11 x10 = ∑ x11 ∈ x6, x3 x4 x6 x9 x11 x10) ∧ (x2 x4 x6 (x9 + (1 : ℕ))).card = x6.card * (x6.card - (1 : ℕ)) ^ x9) := by
  dsimp only
  intro b hb D hD _ j
  have hpos : 0 < b := by omega
  have maps : (words b D (j+1) : Set ℕ).MapsTo (fun n => digit b n j) D :=
    fun _ hn => (mem_words.mp hn).2.1 j (by omega)
  have hs (t : ℝ) : ∑ n ∈ words b D (j+1), digitPhase n t = ∑ a ∈ D, row b D j a t := by
    calc
      _ = ∑ a ∈ D, ∑ n ∈ fiber b D j a, digitPhase n t := (Finset.sum_fiberwise_of_maps_to maps _).symm
      _ = _ := Finset.sum_congr rfl (fun a ha => fiber_sum hpos hD j a ha t)
  refine ⟨hs,?_⟩
  have hz := hs 0
  rw [Finset.sum_congr rfl (fun a ha => row_zero (b := b) j a ha)] at hz
  simp [digitPhase, nsmul_eq_mul] at hz
  change (words b D (j+1)).card = _
  exact_mod_cast hz
