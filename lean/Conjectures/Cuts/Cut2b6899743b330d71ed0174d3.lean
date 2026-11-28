import Mathlib

open Finset

-- child 1 zh: 在每个十六进尺度，用有限覆盖引理选出少量候选元素并覆盖所有高次数目标。
-- child 1 en: A finite covering lemma selecting few vertices on each scale while covering every target with sufficient degree.
-- child 2 zh: 在题面允许的短区间上，估计中央素数表示数不足的偶数目标。
-- child 2 en: Bound the number of even targets with too few central prime representations in each allowed short interval.

theorem Conjectures.Cuts.Cut2b6899743b330d71ed0174d3
    (cover : ∀ (k : ℕ) (T P : Finset ℕ) (edge : ℕ → ℕ → Bool),
      T.card ≤ 16^(k+1) → P.card ≤ 16^(k+1) →
      (∀ n ∈ T, 8^k ≤ (P.filter (fun p => edge n p = true)).card) →
      ∃ B ⊆ P, B.card ≤ 80*4^k ∧ ∀ n ∈ T, ∃ p ∈ B, edge n p = true)
    (richness : (by
      let neighbors := fun n : ℕ => (Finset.range (n+1)).filter (fun p =>
        Nat.Prime p ∧ Nat.Prime (n-p) ∧ n ≤ 3*p ∧ 3*p ≤ 2*n)
      exact ∀ ε : ℝ, 0 < ε → ∀ A : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ,
        ∀ X H : ℕ, T ≤ X → H ≤ X → (X:ℝ)^((7:ℝ)/120+ε) ≤ (H:ℝ) →
        (((Finset.Icc (X-H) X).filter (fun n : ℕ =>
          Even n ∧ (neighbors n).card < 8^(Nat.log 16 n))).card : ℝ) ≤
          C*(H:ℝ)/(1+Real.log (X:ℝ))^A)) : (by
  classical
  exact ∃ B : Set ℕ, (∀ p ∈ B, Nat.Prime p) ∧ (∃ C : ℝ, 0<C ∧ ∀ X : ℕ, 2≤X → (((Finset.Icc 1 X).filter (fun n : ℕ => n ∈ B)).card:ℝ)≤C*Real.sqrt (X:ℝ)) ∧ ∀ ε : ℝ, 0<ε → ∀ A : ℕ, ∃ C : ℝ, 0<C ∧ ∃ T : ℕ, ∀ X H : ℕ, T≤X → H≤X → (X:ℝ)^((7:ℝ)/120+ε) ≤ (H:ℝ) → (((Finset.Icc (X-H) X).filter (fun n : ℕ => Even n ∧ ¬ ∃ p q : ℕ, p ∈ B ∧ Nat.Prime q ∧ p+q=n)).card:ℝ) ≤ C*(H:ℝ)/(1+Real.log (X:ℝ))^A) := by
  classical
  let neighbors := fun n : ℕ => (Finset.range (n+1)).filter (fun p =>
    Nat.Prime p ∧ Nat.Prime (n-p) ∧ n ≤ 3*p ∧ 3*p ≤ 2*n)
  let reservoir (B : ℕ → Finset ℕ) : Set ℕ := {p | ∃ k, p ∈ B k}
  have geom_four_bound (K : ℕ) :
      (∑ i ∈ range (K + 1), (4 : ℕ) ^ i) ≤ 2 * 4 ^ K := by
    induction K with
    | zero => norm_num
    | succ K hK =>
      rw [sum_range_succ]
      calc
        _ ≤ 2 * (4 : ℕ) ^ K + 4 ^ (K + 1) := Nat.add_le_add_right hK _
        _ ≤ _ := by rw [pow_succ]; omega

  have four_log_le_sqrt (X : ℕ) (hX : 2 ≤ X) :
      (4 : ℝ) ^ Nat.log 16 (3 * X) ≤ 2 * Real.sqrt (X : ℝ) := by
    let K := Nat.log 16 (3 * X)
    have hK : (16 : ℕ) ^ K ≤ 3 * X :=
      Nat.pow_log_le_self 16 (by omega)
    change (4 : ℝ) ^ K ≤ 2 * Real.sqrt (X : ℝ)
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    calc
      ((4 : ℝ) ^ K) ^ 2 = (16 : ℝ) ^ K := by
        rw [← pow_mul, Nat.mul_comm K 2, pow_mul]
        norm_num
      _ ≤ 3 * (X : ℝ) := by exact_mod_cast hK
      _ ≤ 4 * (X : ℝ) := by linarith only [(Nat.cast_nonneg X : 0 ≤ (X : ℝ))]
      _ = (2 * Real.sqrt (X : ℝ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg X)]
        norm_num

  -- A union of scale sets of size at most C times 4^k has square-root growth.
  have card_bound (C : ℕ) (B : ℕ → Finset ℕ)
      (hcard : ∀ k, (B k).card ≤ C * 4 ^ k)
      (hscale : ∀ k, ∀ p ∈ B k, 16 ^ k ≤ 3 * p)
      (X : ℕ) (hX : 2 ≤ X) :
      (((Icc 1 X).filter (fun p => p ∈ reservoir B)).card : ℝ) ≤
        4 * (C : ℝ) * Real.sqrt (X : ℝ) := by
    let K := Nat.log 16 (3 * X)
    let F := (Icc 1 X).filter (fun p => p ∈ reservoir B)
    have hF : F ⊆ (range (K + 1)).biUnion B := by
      intro p hp
      obtain ⟨hpIcc, hpB⟩ := mem_filter.mp hp
      obtain ⟨k, hpk⟩ := hpB
      have hpX : p ≤ X := (mem_Icc.mp hpIcc).2
      have hkBound : 16 ^ k ≤ 3 * X :=
        (hscale k p hpk).trans (Nat.mul_le_mul_left 3 hpX)
      have hk : k ≤ K := Nat.le_log_of_pow_le (by decide) hkBound
      exact mem_biUnion.mpr ⟨k, mem_range.mpr (Nat.lt_succ_of_le hk), hpk⟩
    have hNat : F.card ≤ C * (2 * 4 ^ K) := by
      calc
        _ ≤ ((range (K + 1)).biUnion B).card := card_le_card hF
        _ ≤ ∑ k ∈ range (K + 1), (B k).card := card_biUnion_le
        _ ≤ ∑ k ∈ range (K + 1), C * 4 ^ k := sum_le_sum fun k _ => hcard k
        _ = C * ∑ k ∈ range (K + 1), 4 ^ k := by rw [mul_sum]
        _ ≤ _ := Nat.mul_le_mul_left C (geom_four_bound K)
    have hReal : (F.card : ℝ) ≤ (C : ℝ) * (2 * (4 : ℝ) ^ K) :=
      by exact_mod_cast hNat
    have hRoot : (4 : ℝ) ^ K ≤ 2 * Real.sqrt (X : ℝ) := four_log_le_sqrt X hX
    calc
      (F.card : ℝ) ≤ (C : ℝ) * (2 * (4 : ℝ) ^ K) := hReal
      _ = (2 * (C : ℝ)) * (4 : ℝ) ^ K := by ring
      _ ≤ (2 * (C : ℝ)) * (2 * Real.sqrt (X : ℝ)) :=
        mul_le_mul_of_nonneg_left hRoot (by positivity)
      _ = _ := by ring
  have hBlocks :
      ∃ B : ℕ → Finset ℕ,
        (∀ k, (B k).card ≤ 80*4^k) ∧
        (∀ k p, p ∈ B k → Nat.Prime p) ∧
        (∀ k p, p ∈ B k → 16^k ≤ 3*p) ∧
        ∀ n, Even n → 8^(Nat.log 16 n) ≤ (neighbors n).card →
          ∃ p ∈ B (Nat.log 16 n), Nat.Prime (n-p) ∧ p ≤ n := by
    let targets (k : ℕ) := (range (16^(k+1))).filter
      (fun n => 16^k ≤ n ∧ Even n ∧ 8^k ≤ (neighbors n).card)
    let primes (k : ℕ) := (range (16^(k+1))).filter
      (fun p => Nat.Prime p ∧ 16^k ≤ 3*p)
    let edge (n p : ℕ) : Bool := decide (Nat.Prime (n-p) ∧ p ≤ n)
    have degree (k n : ℕ) (hn : n ∈ targets k) :
        8^k ≤ ((primes k).filter (fun p => edge n p = true)).card := by
      obtain ⟨hnRange, hnLower, _, hnDegree⟩ := mem_filter.mp hn
      refine hnDegree.trans (card_le_card ?_)
      intro p hp
      have hp' : p ∈ (range (n+1)).filter
          (fun p => Nat.Prime p ∧ Nat.Prime (n-p) ∧ n ≤ 3*p ∧ 3*p ≤ 2*n) := hp
      obtain ⟨hpRange, hpPrime, hComp, hpCenter, _⟩ := mem_filter.mp hp'
      have hpn : p ≤ n := Nat.le_of_lt_succ (mem_range.mp hpRange)
      have hpU : p < 16^(k+1) := hpn.trans_lt (mem_range.mp hnRange)
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr hpU, hpPrime, hnLower.trans hpCenter⟩, ?_⟩
      change decide (Nat.Prime (n-p) ∧ p ≤ n) = true
      exact decide_eq_true ⟨hComp,hpn⟩
    have chooseBlock (k : ℕ) :
        ∃ B ⊆ primes k, B.card ≤ 80*4^k ∧ ∀ n ∈ targets k, ∃ p ∈ B, edge n p = true := by
      have ht : (targets k).card ≤ 16^(k+1) := by
        unfold targets
        exact (card_filter_le _ _).trans_eq (card_range _)
      have hp : (primes k).card ≤ 16^(k+1) := by
        unfold primes
        exact (card_filter_le _ _).trans_eq (card_range _)
      exact cover k (targets k) (primes k) edge ht hp (degree k)
    choose B hsub hsize hhit using chooseBlock
    refine ⟨B, hsize, ?_, ?_, ?_⟩
    · intro k p hp
      exact (mem_filter.mp (hsub k hp)).2.1
    · intro k p hp
      exact (mem_filter.mp (hsub k hp)).2.2
    · intro n hn hDegree
      have hn0 : n ≠ 0 := by
        intro hn0
        subst n
        simp [neighbors, Nat.not_prime_zero] at hDegree
      let k := Nat.log 16 n
      have hlo : 16^k ≤ n := Nat.pow_log_le_self 16 hn0
      have hhi : n < 16^(k+1) := Nat.lt_pow_succ_log_self (by decide : 1 < 16) n
      have hmem : n ∈ targets k := mem_filter.mpr ⟨mem_range.mpr hhi, hlo, hn, hDegree⟩
      obtain ⟨p, hp, he⟩ := hhit k n hmem
      change decide (Nat.Prime (n-p) ∧ p ≤ n) = true at he
      exact ⟨p, hp, of_decide_eq_true he⟩
  obtain ⟨blocks, hCards, hPrimes, hSupport, hCovered⟩ := hBlocks
  let B : Set ℕ := {p | ∃ k, p ∈ blocks k}
  refine ⟨B, ?_, ⟨320, by norm_num, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨k,hp⟩ := hp
    exact hPrimes k p hp
  · intro X hX
    have h := card_bound 80 blocks hCards hSupport X hX
    simpa only [B, reservoir, Nat.cast_ofNat,show (4:ℝ)*80=320 by norm_num] using h
  · intro ε hε A
    obtain ⟨C,hC,T,hT⟩ := richness ε hε A
    refine ⟨C,hC,T,?_⟩
    intro X H hTX hHX hLen
    have hSub :
        (Finset.Icc (X-H) X).filter
            (fun n : ℕ => Even n ∧ ¬ ∃ p q : ℕ, p ∈ B ∧ Nat.Prime q ∧ p+q=n) ⊆
          (Finset.Icc (X-H) X).filter (fun n : ℕ =>
            Even n ∧ (neighbors n).card < 8^(Nat.log 16 n)) := by
      intro n hn
      obtain ⟨hn,hnEven,hnExc⟩ := Finset.mem_filter.mp hn
      refine Finset.mem_filter.mpr ⟨hn,hnEven,?_⟩
      by_contra! hRich
      obtain ⟨p,hp,hq,hpn⟩ := hCovered n hnEven hRich
      exact hnExc ⟨p,n-p,⟨Nat.log 16 n,hp⟩,hq,by omega⟩
    have hCard := Finset.card_le_card hSub
    exact (by exact_mod_cast hCard : (_:ℝ) ≤ _).trans (hT X H hTX hHX hLen)
