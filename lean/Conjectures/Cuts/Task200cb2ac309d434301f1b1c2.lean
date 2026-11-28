import Mathlib

private def cubicCertificate : List (ℕ × ℕ × ℕ × ℕ) := [
  (1,90,1,4),
  (6,86,3,2),
  (1,1,1,1),
  (8,86,1,2),
  (22,73,1,2),
  (6,90,3,4),
  (0,0,0,0),
  (6,1,3,1),
  (20,79,3,1),
  (1,8,1,2),
  (15,86,1,2),
  (29,73,1,2),
  (20,83,3,7),
  (0,0,0,0),
  (6,8,3,2),
  (20,86,3,2),
  (8,8,1,2),
  (22,86,1,2),
  (36,73,1,2),
  (1,18,1,7),
  (0,0,0,0),
  (20,1,3,1),
  (27,86,3,2),
  (15,8,1,2),
  (6,18,3,7),
  (43,73,1,2),
  (1,25,1,4),
  (0,0,0,0),
  (1,27,1,1),
  (34,86,3,2),
  (22,8,1,2),
  (6,25,3,4),
  (1,31,1,7),
  (6,27,3,1),
  (0,0,0,0),
  (1,34,1,2),
  (41,86,3,2),
  (6,31,3,7),
  (20,18,3,7),
  (1,38,1,4),
  (6,34,3,2),
  (0,0,0,0),
  (8,34,1,2),
  (48,86,3,2),
  (6,38,3,4),
  (1,44,1,7),
  (8,38,1,4),
  (20,27,3,1),
  (0,0,0,0),
  (15,34,1,2),
  (6,44,3,7),
  (20,31,3,7),
  (1,51,1,4),
  (15,38,1,4),
  (1,53,1,1),
  (0,0,0,0),
  (22,34,1,2),
  (6,51,3,4),
  (1,57,1,7),
  (6,53,3,1),
  (22,38,1,4),
  (1,60,1,2),
  (0,0,0,0),
  (6,57,3,7),
  (20,44,3,7),
  (1,64,1,4),
  (6,60,3,2),
  (1,66,1,1),
  (8,60,1,2),
  (0,0,0,0),
  (6,64,3,4),
  (20,51,3,4),
  (6,66,3,1),
  (20,53,3,1),
  (1,73,1,2),
  (15,60,1,2),
  (0,0,0,0),
  (20,57,3,7),
  (27,51,3,4),
  (6,73,3,2),
  (1,79,1,1),
  (8,73,1,2),
  (22,60,1,2),
  (0,0,0,0),
  (1,83,1,7),
  (6,79,3,1),
  (20,66,3,1),
  (1,86,1,2),
  (15,73,1,2),
  (6,83,3,7),
  (0,0,0,0)]

private theorem cubicCertificate_spec : ∀ r : Fin 91, r.val % 7 ≠ 6 →
    let (a,b,u,v) := cubicCertificate.getD r 0
    a<91 ∧ b<91 ∧ (a*(a+2)*b*(b+2)).Coprime 91 ∧ (a+b) % 91=r.val ∧ u^3 % 7=a % 7 ∧ v^3 % 13=b % 13 := by
  decide

theorem Conjectures.Cuts.Task200cb2ac309d434301f1b1c2 : (let R : Finset ℕ := {4,10,16,22,28,40}
  ∀ n : ℕ, (n % 6=4 ∧ (∃ a b : ℕ, a<91 ∧ b<91 ∧ (a*(a+2)*b*(b+2)).Coprime 91 ∧ (a+b) % 91=n % 91 ∧ (∃ u : ℕ, u^3 % 7=a % 7) ∧ (∃ v : ℕ, v^3 % 13=b % 13))) ↔ n % 42 ∈ R) := by
  intro R n
  have mod7 (u : ℕ) : u^3 % 7 = 0 ∨ u^3 % 7 = 1 ∨ u^3 % 7 = 6 := by
    let t : Fin 7 := ⟨u % 7,Nat.mod_lt _ (by decide)⟩
    have h : ∀ i : Fin 7, i.val^3 % 7 = 0 ∨ i.val^3 % 7 = 1 ∨ i.val^3 % 7 = 6 := by decide
    simpa only [t,← Nat.pow_mod] using h t
  have class42 : n % 6=4 ∧ n % 7≠6 ↔ n % 42 ∈ ({4,10,16,22,28,40}:Finset ℕ) := by
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  rw [← class42]
  constructor
  · rintro ⟨h6,a,b,ha,hb,hcp,hs,⟨u,hu⟩,hv⟩
    refine ⟨h6,?_⟩
    intro h6mod
    have h7 : ¬7 ∣ a*(a+2)*b*(b+2) := by
      intro hd
      have hdiv := Nat.dvd_gcd hd (show 7∣91 by decide)
      rw [show (a*(a+2)*b*(b+2)).gcd 91=1 from hcp] at hdiv
      exact (by decide : ¬ (7:ℕ) ∣ 1) hdiv
    have divFactor (x : ℕ) (hx : x % 7=0) : 7∣x := Nat.dvd_of_mod_eq_zero hx
    have hr := mod7 u
    rw [hu] at hr
    rcases hr with h|h|h
    · exact h7 (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (divFactor a h) _) _) _)
    · have hb7 : (b+2) % 7=0 := by omega
      exact h7 (dvd_mul_of_dvd_right (divFactor (b+2) hb7) _)
    · have hb7 : b % 7=0 := by omega
      exact h7 (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (divFactor b hb7) _) _)
  · rintro ⟨h6,hn⟩
    let r : Fin 91 := ⟨n % 91,Nat.mod_lt _ (by decide)⟩
    have hr : r.val % 7≠6 := by dsimp [r]; omega
    have hw := cubicCertificate_spec r hr
    generalize hval : cubicCertificate.getD r 0 = z at hw
    obtain ⟨a,b,u,v⟩ := z
    exact ⟨h6,a,b,hw.1,hw.2.1,hw.2.2.1,hw.2.2.2.1,⟨u,hw.2.2.2.2.1⟩,⟨v,hw.2.2.2.2.2⟩⟩
