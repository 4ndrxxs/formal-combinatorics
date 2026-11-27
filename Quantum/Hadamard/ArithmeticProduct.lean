import Quantum.Hadamard.ArithmeticBase

/-! Two prime-product extensions of normalized greatest common divisor m.
The two extensions can use the same prime q. -/

namespace Hadamard.Arithmetic

structure ProductStep (m q p : ℕ) : Prop where
  prime : p.Prime
  modFour : p ≡ 3 [MOD 4]
  prodOne : p*q ≡ 1 [MOD m]

theorem prod_eq_step {m A : ℕ} (ha : 1 ≤ A) (c4 : (4 : ℕ).Coprime m)
    (ha4 : A ≡ 1 [MOD 4]) (ham : A ≡ 1 [MOD m]) :
    ∃ d, A = 4*m*d + 1 := by
  have d4 := (Nat.modEq_iff_dvd' ha).mp ha4.symm
  have dm := (Nat.modEq_iff_dvd' ha).mp ham.symm
  obtain ⟨d, hd⟩ := c4.mul_dvd_of_dvd_of_dvd d4 dm
  exact ⟨d, by omega⟩

theorem prod_normalized {m A d : ℕ} (h : A = 4*m*d+1) : (A-1)/4 = m*d := by
  rw [h, Nat.add_sub_cancel, show 4*m*d = (m*d)*4 by ring]
  simp

private theorem predecessor_residue {m r : ℕ} (hm : m.Prime) (hm2 : 2 < m)
    (hr : r%m ≠ 1) :
    ∃ a, a.Coprime m ∧ a+1 ≡ r [MOD m] := by
  let a := r + m - 1
  have ha : a+1 ≡ r [MOD m] := by
    have eq : a+1 = r+m := by dsimp [a]; omega
    simp [eq, Nat.ModEq]
  refine ⟨a, ?_, ha⟩
  apply Nat.Coprime.symm
  apply hm.coprime_iff_not_dvd.mpr
  intro d
  have h := ((Nat.modEq_zero_iff_dvd.mpr d).add_right 1).symm.trans ha
  apply hr
  simpa [Nat.ModEq, Nat.mod_eq_of_lt (show 1 < m by omega)] using h.symm

theorem product_steps_of_unit {m a : ℕ} (hm : 1 < m) (c2 : (2 : ℕ).Coprime m)
    (ca : a.Coprime m) :
    ∃ q p₁ p₂, q.Prime ∧ q ≡ 3 [MOD 4] ∧ q ≡ a [MOD m] ∧
      ProductStep m q p₁ ∧ ProductStep m q p₂ ∧
      ((p₁*q-1)/4).gcd ((p₂*q-1)/4) = m := by
  have nz : m ≠ 0 := by omega
  have c8 : (8 : ℕ).Coprime m := c2.pow_left 3
  have c4 : (4 : ℕ).Coprime m := c2.pow_left 2
  obtain ⟨q, hq2, hqp, q8, qa⟩ := prime_crt (by decide) nz c8
    (show (3 : ℕ).Coprime 8 by decide) ca 2
  have qm : q.Coprime m := coprime_of_modEq qa ca
  have qsql : 1 < m^2 := by nlinarith
  obtain ⟨u, _, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime (qm.pow_right 2) qsql
  have inv : q*u ≡ 1 [MOD m^2] := by simpa [Nat.ModEq, Nat.mod_eq_of_lt qsql] using hu
  have cu : u.Coprime (m^2) := Nat.coprime_of_mul_modEq_one q (by simpa [mul_comm] using inv)
  have cm : (m+1).Coprime m := by simp [Nat.coprime_self_add_left]
  obtain ⟨p₁, hp₁2, hp₁, p₁8, p₁sq⟩ :=
    prime_crt (by decide) (pow_ne_zero _ nz) (c8.pow_right 2)
      (show (7 : ℕ).Coprime 8 by decide) (cu.mul_left (cm.pow_right 2)) 2
  have hs : p₁*q ≡ m+1 [MOD m^2] := by
    calc
      p₁*q ≡ (u*(m+1))*q [MOD m^2] := p₁sq.mul_right _
      _ = (q*u)*(m+1) := by ring
      _ ≡ 1*(m+1) [MOD m^2] := inv.mul_right _
      _ = m+1 := one_mul _
  have him : m ∣ m^2 := by rw [pow_two]; exact dvd_mul_right _ _
  have hpm : p₁*q ≡ 1 [MOD m] := (hs.of_dvd him).trans (by simp [Nat.ModEq])
  have hp8 : p₁*q ≡ 5 [MOD 8] := (p₁8.mul q8).trans (by decide)
  have hp4 : p₁*q ≡ 1 [MOD 4] := (hp8.of_dvd (by decide : 4 ∣ 8)).trans (by decide)
  have p₁4 : p₁ ≡ 3 [MOD 4] := (p₁8.of_dvd (by decide : 4 ∣ 8)).trans (by decide)
  have q4 : q ≡ 3 [MOD 4] := q8.of_dvd (by decide : 4 ∣ 8)
  have hpq : 1 < p₁*q := by nlinarith
  obtain ⟨d, hd⟩ := prod_eq_step hpq.le c4 hp4 hpm
  have dpos : 0 < d := by
    by_contra! h
    rw [Nat.le_zero.mp h] at hd
    simp at hd
    omega
  have cd : d.Coprime m := by
    have le : m+1 ≤ p₁*q := by rw [hd]; nlinarith
    obtain ⟨s, hs'⟩ := (Nat.modEq_iff_dvd' le).mp hs.symm
    have hs'' : p₁*q = m^2*s+(m+1) := by omega
    have eq : m*(4*d) = m*(1+m*s) := by nlinarith [hd,hs'']
    have eq' := Nat.eq_of_mul_eq_mul_left (by omega : 0 < m) eq
    apply Nat.coprime_of_mul_modEq_one 4
    rw [Nat.mul_comm d 4,eq']
    simp [Nat.ModEq]
  have cd2 : d.Coprime 2 := by
    apply Nat.Coprime.symm
    apply Nat.prime_two.coprime_iff_not_dvd.mpr
    rintro ⟨t, ht⟩
    have eq : p₁*q = (m*t)*8 + 1 := by rw [hd, ht]; ring
    have h : (1 : ℕ) ≡ 5 [MOD 8] :=
      (show p₁*q ≡ 1 [MOD 8] by simp [Nat.ModEq, eq]).symm.trans hp8
    exact (by decide : ¬ (1 : ℕ) ≡ 5 [MOD 8]) h
  have p₁qd : p₁*q ≡ 1 [MOD d] := by
    rw [hd]
    simp [Nat.ModEq]
  have p₁d : p₁.Coprime d := Nat.coprime_of_mul_modEq_one _ p₁qd
  have pred : (d-1).Coprime d :=
    (Nat.coprime_self_sub_left (show 1 ≤ d by omega)).mpr (by simp)
  have p₁4m : p₁.Coprime (4*m) :=
    (coprime_of_modEq p₁4 (by decide)).mul_right (Nat.coprime_of_mul_modEq_one _ hpm)
  have c4d : (4 : ℕ).Coprime d := cd2.symm.pow_left 2
  obtain ⟨p₂, hp₂2, hp₂, hp₂a, hp₂b⟩ := prime_crt (by positivity : 4*m ≠ 0)
    dpos.ne' (c4d.mul_left cd.symm) p₁4m (p₁d.mul_left pred) 2
  have hp₂4 := (hp₂a.of_dvd (dvd_mul_right 4 m)).trans p₁4
  have hp₂m := ((hp₂a.of_dvd (dvd_mul_left m 4)).mul_right q).trans hpm
  have hp₂q : 1 < p₂*q := by nlinarith
  have hp₂q4 : p₂*q ≡ 1 [MOD 4] := (hp₂4.mul q4).trans (by decide)
  obtain ⟨e, he⟩ := prod_eq_step hp₂q.le c4 hp₂q4 hp₂m
  have dplus : d ∣ p₂*q+1 := Nat.modEq_zero_iff_dvd.mp <| calc
    p₂*q+1 ≡ (p₁*(d-1))*q+1 [MOD d] := (hp₂b.mul_right q).add_right _
    _ = (p₁*q)*(d-1)+1 := by ring
    _ ≡ 1*(d-1)+1 [MOD d] := (p₁qd.mul_right _).add_right _
    _ = d := by omega
    _ ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr dvd_rfl
  have ede : e ∣ p₂*q-1 := by
    rw [he, Nat.add_sub_cancel]
    exact dvd_mul_left _ _
  have de : d.Coprime e := (coprime_sub_one (by omega) cd2 dplus).of_dvd_right ede
  refine ⟨q, p₁, p₂, hqp, q4, qa,
    ⟨hp₁, p₁4, hpm⟩, ⟨hp₂, hp₂4, hp₂m⟩, ?_⟩
  rw [prod_normalized hd, prod_normalized he, Nat.gcd_mul_left, de.gcd_eq_one, Nat.mul_one]

theorem product_steps {m r : ℕ} (hm : m.Prime) (hm2 : 2 < m) (hr : r%m ≠ 1) :
    ∃ q p₁ p₂, q.Prime ∧ q ≡ 3 [MOD 4] ∧ q+1 ≡ r [MOD m] ∧
      ProductStep m q p₁ ∧ ProductStep m q p₂ ∧
      ((p₁*q-1)/4).gcd ((p₂*q-1)/4) = m := by
  obtain ⟨a,ca,ha⟩ := predecessor_residue hm hm2 hr
  obtain ⟨q,p₁,p₂,hq,q4,qa,h₁,h₂,gcd⟩ :=
    product_steps_of_unit (by omega : 1 < m) (two_coprime_prime hm hm2) ca
  exact ⟨q,p₁,p₂,hq,q4,(qa.add_right 1).trans ha,h₁,h₂,gcd⟩

end Hadamard.Arithmetic
