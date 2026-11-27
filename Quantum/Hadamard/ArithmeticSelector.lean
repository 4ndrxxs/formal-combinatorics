import Quantum.Hadamard.FiniteFieldAffine
import Quantum.Hadamard.ArithmeticComposite

/-! An affine plane over a sufficiently large prime-power field provides
odd-square orders for arbitrary odd moduli. Tensor products select zero
and unit-square factors of any odd composite modulus. -/

namespace HadamardMod

open Hadamard.Arithmetic

theorem prime_power_affine {m p e : ℕ} [Fact p.Prime] (hm : 1 < m)
    (odd : (2 : ℕ).Coprime m) (he : e ≠ 0) (big : m ≤ p^e) :
    AtOrder m ((p^e)^2) := by
  classical
  let F := GaloisField p e
  let : Fintype F := Fintype.ofFinite F
  have card : Fintype.card F = p^e := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p e he
  obtain ⟨i,_,inv⟩ := Nat.exists_mul_mod_eq_one_of_coprime odd hm
  let t := (p^e*i)%m
  have ht : t < m := Nat.mod_lt _ (by omega)
  obtain ⟨T,_,size⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F))
    (n := t) (by simpa [card] using ht.le.trans big)
  have ii : 2*i ≡ 1 [MOD m] := by simpa [Nat.ModEq,Nat.mod_eq_of_lt hm] using inv
  have tg : 2*t ≡ p^e [MOD m] := calc
    2*t ≡ 2*(p^e*i) [MOD m] := (Nat.mod_modEq _ _).mul_left _
    _ = (2*i)*(p^e) := by ring
    _ ≡ 1*(p^e) [MOD m] := ii.mul_right _
    _ = p^e := one_mul _
  have ch : 2*(T.card : ZMod m) = (Fintype.card F : ZMod m) := by
    rw [size,card]
    simpa using (ZMod.natCast_eq_natCast_iff _ _ m).mpr tg
  simpa only [card] using Hadamard.FiniteFieldAffine.at_square_order T ch

private theorem seed_one (m : ℕ) : AtOrder m 1 :=
  ⟨fun _ _ => 1, ⟨fun _ _ => Or.inl rfl, fun i j ne => (ne (Subsingleton.elim i j)).elim⟩⟩

/-- An order divisible by A, and congruent to one modulo b, where A is
coprime to b. The affine matrices are all built at the full modulus m. -/
theorem selector {m b : ℕ} (hm : 1 < m) (odd : (2 : ℕ).Coprime m) (hb : 0 < b)
    (A : ℕ) (pos : 0 < A) (cop : A.Coprime b) :
    ∃ h > 0, AtOrder m h ∧ A ∣ h ∧ h ≡ 1 [MOD b] := by
  induction A using Nat.strong_induction_on with
  | ind A IH =>
    by_cases A1 : A=1
    · subst A
      exact ⟨1,by decide,seed_one m,dvd_refl _,Nat.ModEq.refl _⟩
    obtain ⟨p,hp,pA⟩ := Nat.exists_prime_and_dvd A1
    obtain ⟨d,Ad⟩ := pA
    have pp : p ∣ A := ⟨d,Ad⟩
    have dd : d ∣ A := by rw [Ad]; exact dvd_mul_left _ _
    have dp : 0 < d := by by_contra! le; rw [Nat.le_zero.mp le,mul_zero] at Ad; omega
    have da : d < A := by rw [Ad]; have := hp.two_le; nlinarith
    obtain ⟨j,jpos,J,dj,j1⟩ := IH d da dp (cop.of_dvd_left dd)
    let : Fact p.Prime := ⟨hp⟩
    let e := b.totient*m
    have tot := Nat.totient_pos.mpr hb
    have em : m ≤ e := by dsimp [e]; nlinarith
    have ep : 0 < e := by omega
    have big : m ≤ p^e := by
      exact em.trans (e.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hp.two_le e))
    have H := prime_power_affine (p := p) (e := e) hm odd ep.ne' big
    have cp : p.Coprime b := cop.of_dvd_left pp
    have one : p^e ≡ 1 [MOD b] := by
      simpa [e,pow_mul] using (Nat.ModEq.pow_totient cp).pow m
    have pd : p ∣ (p^e)^2 := (dvd_pow_self p ep.ne').trans (dvd_pow_self _ (by decide : 2 ≠ 0))
    refine ⟨(p^e)^2*j, Nat.mul_pos (pow_pos (pow_pos hp.pos _) _) jpos, at_mul H J, ?_, ?_⟩
    · rw [Ad]
      exact Nat.mul_dvd_mul pd dj
    · simpa using (one.pow 2).mul j1

theorem four_seed_odd {m : ℕ} (hm : 0 < m) (c2 : (2 : ℕ).Coprime m) (c : ℕ) :
    ∃ k > 0, AtOrder m k ∧ k ≡ c [MOD 4] ∧ k ≡ 4 [MOD m] := by
  obtain ⟨z,z4,zm⟩ := Nat.chineseRemainder (c2.pow_left 2 : (4:ℕ).Coprime m) c 4
  let k := z+4*m
  have c4 : k ≡ c [MOD 4] := (show k ≡ z [MOD 4] by simp [k,Nat.ModEq]).trans z4
  have cm : k ≡ 4 [MOD m] := (show k ≡ z [MOD m] by simp [k,Nat.ModEq]).trans zm
  exact ⟨k,by dsimp [k]; omega,
    offdiag_four (by simpa using (ZMod.natCast_eq_natCast_iff _ _ m).mpr cm),c4,cm⟩

/-- Residue r vanishes modulo A and is four times a unit square modulo B.
There is a seed in each of the four parity classes at the entire modulus A*B. -/
theorem mixed_square_seeds {A B r s : ℕ} (hm : 1 < A*B)
    (c2 : (2:ℕ).Coprime (A*B)) (cab : A.Coprime B) (cs : s.Coprime B)
    (zero : A ∣ r) (square : r ≡ 4*s^2 [MOD B]) (c : ℕ) :
    ∃ k > 0, AtOrder (A*B) k ∧ k ≡ c [MOD 4] ∧ k ≡ r [MOD A*B] := by
  have pos : 0 < A*B := by omega
  have apos : 0 < A := Nat.pos_of_mul_pos_right pos
  have bpos : 0 < B := Nat.pos_of_mul_pos_left pos
  have a2 : A.Coprime 2 := (c2.of_dvd_right (dvd_mul_right _ _)).symm
  have b2 : (2:ℕ).Coprime B := c2.of_dvd_right (dvd_mul_left _ _)
  obtain ⟨h,hpos,H,dh,h1⟩ := selector hm c2 (show 0 < 4*B by positivity)
    A apos ((a2.pow_right 2).mul_right cab)
  have h4 := h1.of_dvd (dvd_mul_right 4 B)
  have hb := h1.of_dvd (dvd_mul_left B 4)
  obtain ⟨q,big,qp,q4,qb⟩ := prime_crt (by decide) bpos.ne'
    (b2.pow_left 2 : (4:ℕ).Coprime B) (show (1:ℕ).Coprime 4 by decide) cs (A*B)
  let : Fact q.Prime := ⟨qp⟩
  have Q : AtOrder (A*B) (q^2) := by
    simpa using prime_power_affine (p:=q) (e:=1) hm c2 (by decide) (by simpa using big.le)
  obtain ⟨j,jpos,J,j4,jm⟩ := four_seed_odd pos c2 c
  let k := h*q^2*j
  have dvdA : A ∣ k := (dh.trans (dvd_mul_right _ _)).trans (dvd_mul_right _ _)
  have kb : k ≡ r [MOD B] := by
    have E := (hb.mul (qb.pow 2)).mul (jm.of_dvd (dvd_mul_left B A))
    apply Nat.ModEq.trans (b := 4*s^2) _ square.symm
    simpa [k,Nat.mul_comm] using E
  refine ⟨k, Nat.mul_pos (Nat.mul_pos hpos (pow_pos qp.pos _)) jpos, at_mul (at_mul H Q) J, ?_, ?_⟩
  · simpa [k] using (h4.mul (q4.pow 2)).mul j4
  · exact (Nat.modEq_and_modEq_iff_modEq_mul cab).mp
      ⟨(Nat.modEq_zero_iff_dvd.mpr dvdA).trans (Nat.modEq_zero_iff_dvd.mpr zero).symm,kb⟩

theorem mixed_square_large {A B r s a : ℕ} (hm : 1 < A*B)
    (c2 : (2:ℕ).Coprime (A*B)) (cab : A.Coprime B) (cs : s.Coprime B)
    (zero : A ∣ r) (square : r ≡ 4*s^2 [MOD B]) (ca : a.Coprime (A*B))
    (res : r ≡ a+1 [MOD A*B]) :
    ∃ N, ∀ n ≥ N, n ≡ r [MOD A*B] → AtOrder (A*B) n :=
  composite_class_large hm c2 ca res
    (fun c => mixed_square_seeds hm c2 cab cs zero square c.val)

theorem mixed_105_39 : ∃ N, ∀ n ≥ N, n ≡ 39 [MOD 105] → AtOrder 105 n := by
  exact mixed_square_large (A:=3) (B:=35) (r:=39) (s:=1) (a:=38)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The explicit composite-modulus test class highlighted by Kline. -/
theorem mixed_105_51 : ∃ N, ∀ n ≥ N, 4 ∣ n → n ≡ 51 [MOD 105] → AtOrder 105 n := by
  obtain ⟨N,hN⟩ := mixed_105_39
  refine ⟨4*N, ?_⟩
  intro n hn four hr
  obtain ⟨s,rfl⟩ := four
  have res : s ≡ 39 [MOD 105] := by
    have h4 : 4*s ≡ 4*39 [MOD 105] := hr.trans (by decide)
    exact Nat.ModEq.cancel_left_of_coprime (by decide : (105:ℕ).gcd 4 = 1) h4
  have H4 : AtOrder 105 4 := by simpa using at_mul (order_two 105) (order_two 105)
  exact at_mul H4 (hN s (by omega) res)

#print axioms mixed_square_large
#print axioms mixed_105_51
end HadamardMod
