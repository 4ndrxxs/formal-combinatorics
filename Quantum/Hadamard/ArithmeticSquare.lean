import Quantum.Hadamard.ArithmeticBase

/-! In residue one, doubled Paley orders give regular-square extensions. -/

namespace Hadamard.Arithmetic

def squareOrder (q : ℕ) : ℕ := 2*(q+1)

def squareIncrement (q : ℕ) : ℕ := (squareOrder q)^2-1

structure SquareSeed (m q : ℕ) : Prop where
  prime : q.Prime
  modFour : q ≡ 3 [MOD 4]
  orderOne : squareOrder q ≡ 1 [MOD m]

theorem square_steps {m : ℕ} (hm : m.Prime) (hm2 : 2 < m) :
    ∃ q₁ q₂, SquareSeed m q₁ ∧ SquareSeed m q₂ ∧
      (squareIncrement q₁).gcd (squareIncrement q₂) = m := by
  obtain ⟨a, ha⟩ := hm.odd_of_ne_two (by omega)
  have hhalf : 2*(a+1) = m+1 := by omega
  have ca : a.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).symm
  have c4 := four_coprime_prime hm hm2
  obtain ⟨q₁, hq₁2, hq₁, q₁4, q₁sq⟩ := prime_crt (by decide)
    (pow_ne_zero _ hm.ne_zero) (c4.pow_right 2) (show (3 : ℕ).Coprime 4 by decide)
    (ca.pow_right 2) 2
  have h₁sq : squareOrder q₁ ≡ m+1 [MOD m^2] := by
    simpa [squareOrder, hhalf] using (q₁sq.add_right 1).mul_left 2
  have him : m ∣ m^2 := by rw [pow_two]; exact dvd_mul_right _ _
  have h₁m : squareOrder q₁ ≡ 1 [MOD m] :=
    (h₁sq.of_dvd him).trans (by simp [Nat.ModEq])
  have hsq : (squareOrder q₁)^2 ≡ 2*m+1 [MOD m^2] := by
    calc
      (squareOrder q₁)^2 ≡ (m+1)^2 [MOD m^2] := h₁sq.pow 2
      _ = 2*m+1 + m^2 := by ring
      _ ≡ 2*m+1 [MOD m^2] := by simp [Nat.ModEq]
  have hlarge : 1 < (squareOrder q₁)^2 := by dsimp [squareOrder]; nlinarith
  have ds := (Nat.modEq_iff_dvd' hlarge.le).mp (by simpa using (h₁m.pow 2).symm)
  obtain ⟨d, hd⟩ := ds
  have hde : (squareOrder q₁)^2 = m*d+1 := by omega
  have cd := coprime_quotient hm (show 1 < 2*m+1 by omega) (by nlinarith)
    hsq (k := 1) (by simpa using hde)
  have dpos : 0 < d := by
    by_contra! le
    rw [Nat.le_zero.mp le, Nat.mul_zero, Nat.zero_add] at hde
    exact hlarge.ne' hde
  have cd2 : d.Coprime 2 := by
    apply Nat.Coprime.symm
    apply Nat.prime_two.coprime_iff_not_dvd.mpr
    rintro ⟨t, ht⟩
    have odd : (squareOrder q₁)^2 ≡ 1 [MOD 2] := by
      rw [hde, ht, show m*(2*t)+1 = (m*t)*2+1 by ring]
      simp [Nat.ModEq]
    have even : (squareOrder q₁)^2 ≡ 0 [MOD 2] := by
      simp [Nat.ModEq, squareOrder, Nat.pow_mod]
    exact (by decide : ¬(0 : ℕ) ≡ 1 [MOD 2]) (even.symm.trans odd)
  have pred : (d-1).Coprime d :=
    (Nat.coprime_self_sub_left (show 1 ≤ d by omega)).mpr (by simp)
  have cq : q₁.Coprime (4*m) :=
    (coprime_of_modEq q₁4 (by decide)).mul_right (coprime_of_modEq (q₁sq.of_dvd him) ca)
  have c4d : (4 : ℕ).Coprime d := cd2.symm.pow_left 2
  obtain ⟨q₂, hq₂2, hq₂, q₂a, q₂b⟩ := prime_crt (by positivity : 4*m ≠ 0)
    dpos.ne' (c4d.mul_left cd.symm) cq pred 2
  have q₂4 := (q₂a.of_dvd (dvd_mul_right 4 m)).trans q₁4
  have h₂m : squareOrder q₂ ≡ 1 [MOD m] :=
    (((q₂a.of_dvd (dvd_mul_left m 4)).add_right 1).mul_left 2).trans h₁m
  have h₂large : 1 < (squareOrder q₂)^2 := by dsimp [squareOrder]; nlinarith
  have es := (Nat.modEq_iff_dvd' h₂large.le).mp (by simpa using (h₂m.pow 2).symm)
  obtain ⟨e, he⟩ := es
  have dh : squareOrder q₂ ≡ 0 [MOD d] := by
    calc
      squareOrder q₂ ≡ 2*((d-1)+1) [MOD d] := (q₂b.add_right 1).mul_left 2
      _ = 2*d := by rw [Nat.sub_add_cancel dpos]
      _ ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left _ _)
  have dsq : d ∣ (squareOrder q₂)^2 :=
    Nat.modEq_zero_iff_dvd.mp (by simpa using dh.pow 2)
  have csq : ((squareOrder q₂)^2-1).Coprime ((squareOrder q₂)^2) :=
    (Nat.coprime_self_sub_left h₂large.le).mpr (by simp)
  have ed : e ∣ (squareOrder q₂)^2-1 := by rw [he]; exact dvd_mul_left _ _
  have de : d.Coprime e := (csq.symm.of_dvd_left dsq).of_dvd_right ed
  refine ⟨q₁, q₂, ⟨hq₁, q₁4, h₁m⟩, ⟨hq₂, q₂4, h₂m⟩, ?_⟩
  rw [squareIncrement, squareIncrement, hd, he, Nat.gcd_mul_left, de.gcd_eq_one, Nat.mul_one]

end Hadamard.Arithmetic
