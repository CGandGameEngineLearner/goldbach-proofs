import Mathlib

-- Index the twelve base residues, three prime lifts for each residue, and
-- a triple of base residues suitable for each even residue modulo 210.
private def base (r : ℕ) : ℕ := ([17, 19, 23, 181, 29, 37, 41, 43, 31, 47, 53, 67] : List ℕ).getD r 0

private def lifted (r : ℕ) (i : Fin 3) : ℕ :=
  (([
  [17, 30047, 60077],
  [19, 150169, 210229],
  [23, 60083, 210233],
  [181, 30211, 90271],
  [29, 30059, 60089],
  [37, 90127, 120157],
  [41, 30071, 60101],
  [43, 60103, 120163],
  [31, 60091, 90121],
  [47, 60107, 120167],
  [53, 150203, 180233],
  [67, 30097, 60127]] : List (List ℕ)).getD r []).getD i.val 0

private def baseRow (a : Fin 105) (i : Fin 3) : ℕ :=
  let row := ([0, 1, 2, 0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 8, 1, 14, 0, 3, 15, 16, 17, 15, 18, 3, 4, 19, 9, 13, 0, 20, 2, 21, 22, 15, 23, 6, 15, 8, 3, 4, 19, 24, 13, 0, 25, 26, 15, 3, 13, 16, 27, 14, 23, 6, 4, 28, 9, 7, 0, 1, 2, 0, 25, 15, 21, 22, 29, 30, 3, 31, 19, 9, 32, 16, 17, 2, 18, 3, 15, 16, 6, 15, 8, 1, 4, 33, 34, 35, 19, 1, 32, 0, 36, 2, 16, 6, 15, 8, 3, 37, 19, 9, 13] : List ℕ).getD a.val 0
  (([
  [0, 1, 2],
  [1, 3, 7],
  [0, 2, 6],
  [1, 3, 5],
  [2, 4, 6],
  [2, 3, 4],
  [3, 5, 7],
  [0, 4, 9],
  [0, 1, 3],
  [1, 5, 7],
  [2, 6, 10],
  [2, 3, 5],
  [5, 7, 11],
  [0, 4, 6],
  [0, 2, 9],
  [0, 2, 4],
  [1, 2, 3],
  [3, 7, 8],
  [0, 1, 4],
  [0, 2, 3],
  [1, 7, 8],
  [1, 2, 4],
  [3, 5, 8],
  [1, 3, 4],
  [1, 7, 11],
  [1, 3, 8],
  [2, 6, 9],
  [5, 7, 8],
  [0, 3, 6],
  [2, 4, 9],
  [0, 3, 4],
  [4, 6, 10],
  [0, 6, 9],
  [0, 2, 5],
  [1, 5, 11],
  [4, 6, 9],
  [1, 5, 8],
  [2, 4, 10]] : List (List ℕ)).getD row []).getD i.val 0

private def separated (f : Fin 3 → ℕ) (q : ℕ) : Prop :=
  f 0 % q ≠ f 1 % q ∧ f 0 % q ≠ f 2 % q ∧ f 1 % q ≠ f 2 % q

private instance (f : Fin 3 → ℕ) (q : ℕ) : Decidable (separated f q) := by
  unfold separated
  infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem baseCertificate : ∀ a : Fin 105,
    (∀ i : Fin 3, baseRow a i < 12 ∧
      (2*a.val)%2 ≠ base (baseRow a i)%2 ∧ (2*a.val)%3 ≠ base (baseRow a i)%3 ∧
      (2*a.val)%5 ≠ base (baseRow a i)%5 ∧ (2*a.val)%7 ≠ base (baseRow a i)%7) ∧
    separated (fun i => base (baseRow a i)) 11 ∧ separated (fun i => base (baseRow a i)) 13 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem liftCertificate : ∀ r : Fin 12,
    (∀ i : Fin 3, lifted r.val i ≤ 210233 ∧
      lifted r.val i % 30030 = base r.val) ∧
    separated (lifted r.val) 17 ∧ separated (lifted r.val) 19 := by decide

private theorem liftPrime (r : Fin 12) (i : Fin 3) : Nat.Prime (lifted r.val i) := by
  have mem : ∀ (r : Fin 12) (i : Fin 3), lifted r.val i ∈ ([17, 30047, 60077, 19, 150169, 210229, 23, 60083, 210233, 181, 30211, 90271, 29, 30059, 60089, 37, 90127, 120157, 41, 30071, 60101, 43, 60103, 120163, 31, 60091, 90121, 47, 60107, 120167, 53, 150203, 180233, 67, 30097, 60127] : List ℕ) := by decide
  have h := mem r i
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> norm_num1

private theorem avoidTwo (f : Fin 3 → ℕ) (q s n : ℕ)
    (hq : separated f q) (hs : separated f s) :
    ∃ i : Fin 3, n % q ≠ f i % q ∧ n % s ≠ f i % s := by
  obtain ⟨hq01,hq02,hq12⟩ := hq
  obtain ⟨hs01,hs02,hs12⟩ := hs
  by_contra! h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  grind

private theorem excludeFactor {n p q : ℕ} (hp : p ≤ n) (hq : q.Prime)
    (hne : n % q ≠ p % q) : (n-p).Coprime q :=
  (hq.coprime_iff_not_dvd.mpr (fun h => hne ((Nat.modEq_iff_dvd' hp).mpr h).symm)).symm

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_goldbach_finite_wheel_rough_twentythree :
    ∀ n : ℕ, 210235 ≤ n → Even n → ∃ p : ℕ, Nat.Prime p ∧ p ≤ 210233 ∧ 2 ≤ n-p ∧ Nat.Coprime (n-p) 9699690 := by
  intro n hn hev
  obtain ⟨k,hk⟩ := hev
  let a : Fin 105 := ⟨(n % 210)/2, by omega⟩
  have ha : 2*a.val = n % 210 := by dsimp [a]; omega
  obtain ⟨hbase,h11,h13⟩ := baseCertificate a
  obtain ⟨i,hi11,hi13⟩ := avoidTwo _ _ _ n h11 h13
  obtain ⟨hr,h2,h3,h5,h7⟩ := hbase i
  let r : Fin 12 := ⟨baseRow a i, hr⟩
  obtain ⟨hlift,h17,h19⟩ := liftCertificate r
  obtain ⟨j,hj17,hj19⟩ := avoidTwo _ _ _ n h17 h19
  obtain ⟨hbound,hres⟩ := hlift j
  let p := lifted r.val j
  refine ⟨p, liftPrime r j, hbound, by dsimp [p]; omega, ?_⟩
  change p % 30030 = base (baseRow a i) at hres
  change n % 11 ≠ base (baseRow a i) % 11 at hi11
  change n % 13 ≠ base (baseRow a i) % 13 at hi13
  change n % 17 ≠ p % 17 at hj17
  change n % 19 ≠ p % 19 at hj19
  change p ≤ 210233 at hbound
  rw [ha, ← hres] at h2 h3 h5 h7
  rw [← hres] at hi11 hi13
  have hpn : p ≤ n := by omega
  change Nat.Coprime (n-p) (2*3*5*7*11*13*17*19)
  simp only [Nat.coprime_mul_iff_right]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · apply excludeFactor hpn (by decide)
    simpa only [Nat.mod_mod_of_dvd n (by decide : 2 ∣ 210), Nat.mod_mod_of_dvd p (by decide : 2 ∣ 30030)] using h2
  · apply excludeFactor hpn (by decide)
    simpa only [Nat.mod_mod_of_dvd n (by decide : 3 ∣ 210), Nat.mod_mod_of_dvd p (by decide : 3 ∣ 30030)] using h3
  · apply excludeFactor hpn (by decide)
    simpa only [Nat.mod_mod_of_dvd n (by decide : 5 ∣ 210), Nat.mod_mod_of_dvd p (by decide : 5 ∣ 30030)] using h5
  · apply excludeFactor hpn (by decide)
    simpa only [Nat.mod_mod_of_dvd n (by decide : 7 ∣ 210), Nat.mod_mod_of_dvd p (by decide : 7 ∣ 30030)] using h7
  · apply excludeFactor hpn (by decide)
    simpa only [Nat.mod_mod_of_dvd p (by decide : 11 ∣ 30030)] using hi11
  · apply excludeFactor hpn (by decide)
    simpa only [Nat.mod_mod_of_dvd p (by decide : 13 ∣ 30030)] using hi13
  · apply excludeFactor hpn (by decide)
    exact hj17
  · apply excludeFactor hpn (by decide)
    exact hj19
