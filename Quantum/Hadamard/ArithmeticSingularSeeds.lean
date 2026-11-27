import Quantum.Hadamard.ArithmeticAffineNet
import Quantum.Hadamard.ArithmeticOddUnits

/-! Every square class of every odd modulus has a sign orthogonal
matrix in each of the four physical order classes, including singular
square classes with exact, intermediate prime-adic valuation. -/
noncomputable section
namespace HadamardMod
open Hadamard.Arithmetic

theorem net_prime_seed {m p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (pq : p ≤ q) (qr : q ≡ 2 [MOD m]) : AtOrder m ((p*q)^2) := by
  classical
  let lift (s:ZMod p) : ZMod q := (s.val:ZMod q)
  have inj : Function.Injective lift := by
    intro s t eq
    have h := congrArg ZMod.val eq
    simp only [lift,ZMod.val_natCast,Nat.mod_eq_of_lt ((ZMod.val_lt s).trans_le pq),
      Nat.mod_eq_of_lt ((ZMod.val_lt t).trans_le pq)] at h
    exact ZMod.val_injective p h
  let f (s:ZMod p) : ZMod p×ZMod q := (s,lift s)
  have diff (s t:ZMod p) (ne:s≠t) : IsUnit (f s-f t) :=
    Prod.isUnit_iff.mpr ⟨isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr ne),
      isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (fun eq => ne (inj eq)))⟩
  have q2 : (q:ZMod m)=2 := by simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr qr
  apply (by simpa only [Fintype.card_prod,ZMod.card] using
    (Hadamard.AffineNet.at_square (m:=m) (f:=f) diff))
  simp [q2,mul_comm]

private theorem odd_sq_mod_four {v : ℕ} (hv : Odd v) : v^2 ≡ 1 [MOD 4] := by
  obtain ⟨j,hj⟩ := hv
  rw [hj,show (2*j+1)^2=1+4*(j^2+j) by ring]
  simp [Nat.ModEq]

private theorem prime_square_seed {m p : ℕ} (mp:1 < m) (odd:(2:ℕ).Coprime m)
    (pp:p.Prime) (op:Odd p) :
    ∃ h>0, AtOrder m h ∧ h ≡ 1 [MOD 4] ∧ h ≡ p^2 [MOD m] := by
  obtain ⟨q,hq,pq,q2⟩ := Nat.forall_exists_prime_gt_and_modEq (max p 2) (by omega:m≠0) odd
  obtain ⟨a,_,ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime odd mp
  have inv : 2*a ≡ 1 [MOD m] := by simpa [Nat.ModEq,Nat.mod_eq_of_lt mp] using ha
  have ca : a.Coprime m := Nat.coprime_of_mul_modEq_one 2 (by rw [mul_comm]; exact inv)
  obtain ⟨s,hs,ps,sa⟩ := Nat.forall_exists_prime_gt_and_modEq (max m 2) (by omega:m≠0) ca
  let : Fact p.Prime := ⟨pp⟩
  let : Fact q.Prime := ⟨pq⟩
  let : Fact s.Prime := ⟨ps⟩
  have A := net_prime_seed (m:=m) (p:=p) (q:=q) (by omega) q2
  have B : AtOrder m (s^2) := by
    simpa using prime_power_affine (p:=s) (e:=1) mp odd (by decide) (by simp; omega)
  have con : (p*q)*s ≡ p [MOD m] := by
    rw [mul_assoc]; simpa using ((q2.mul sa).trans inv).mul_left p
  have opqs := (op.mul (pq.odd_of_ne_two (by omega:q≠2))).mul (ps.odd_of_ne_two (by omega:s≠2))
  refine ⟨(p*q)^2*s^2,Nat.mul_pos (pow_pos (Nat.mul_pos pp.pos pq.pos) _) (pow_pos ps.pos _),at_mul A B,?_,?_⟩
  · simpa only [mul_pow] using odd_sq_mod_four opqs
  · simpa only [mul_pow] using con.pow 2

theorem odd_square_seed {m : ℕ} (mp:1 < m) (odd:(2:ℕ).Coprime m) (x:ℕ) (ox:Odd x) :
    ∃ h>0, AtOrder m h ∧ h ≡ 1 [MOD 4] ∧ h ≡ x^2 [MOD m] := by
  induction x using Nat.strong_induction_on with
  | ind x IH =>
    by_cases one : x=1
    · subst x
      have H : AtOrder m 1 :=
        ⟨fun _ _ => 1, ⟨fun _ _ => Or.inl rfl, fun i j ne => (ne (Subsingleton.elim i j)).elim⟩⟩
      exact ⟨1,by decide,H,Nat.ModEq.refl _,by simpa using (Nat.ModEq.refl 1 : 1 ≡ 1 [MOD m])⟩
    obtain ⟨p,pp,d,eq⟩ := Nat.exists_prime_and_dvd one
    have op : Odd p ∧ Odd d := Nat.odd_mul.mp (eq ▸ ox)
    have dp : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at op)
    have dx : d < x := by rw [eq]; have := pp.two_le; nlinarith
    obtain ⟨a,ap,A,a4,am⟩ := prime_square_seed mp odd pp op.1
    obtain ⟨b,bp,B,b4,bm⟩ := IH d dx op.2
    refine ⟨a*b,Nat.mul_pos ap bp,at_mul A B,by simpa using a4.mul b4,?_⟩
    simpa only [eq,mul_pow] using am.mul bm

/-- The physical order is independently prescribed modulo four. -/
theorem square_seed_each_mod_four {m r : ℕ} (mp:1 < m) (odd:(2:ℕ).Coprime m)
    (square:IsSquare (r:ZMod m)) (c:Fin 4) :
    ∃ h > 0, AtOrder m h ∧ h ≡ c.val [MOD 4] ∧ h ≡ r [MOD m] := by
  let : NeZero m := ⟨by omega⟩
  obtain ⟨s,hs⟩ := square
  obtain ⟨a,_,ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime odd mp
  have inv : 2*a ≡ 1 [MOD m] := by simpa [Nat.ModEq,Nat.mod_eq_of_lt mp] using ha
  have rs : s.val^2 ≡ r [MOD m] := (ZMod.natCast_eq_natCast_iff _ _ _).mp (by simp [pow_two,hs])
  have four : (4:ℕ).Coprime m := odd.pow_left 2
  let x := (Nat.chineseRemainder odd 1 (s.val*a)).val
  have ox : Odd x := Nat.odd_iff.mpr ((Nat.chineseRemainder odd 1 (s.val*a)).property.1)
  have xm : x ≡ s.val*a [MOD m] := (Nat.chineseRemainder odd 1 (s.val*a)).property.2
  obtain ⟨k,kp,K,k4,km⟩ := odd_square_seed mp odd x ox
  let t := (Nat.chineseRemainder four c.val 4).val
  let j := t+4*m
  have j4 : j ≡ c.val [MOD 4] := by
    apply Nat.ModEq.trans _ (Nat.chineseRemainder four c.val 4).property.1
    simp [j,t,Nat.ModEq]
  have jm : j ≡ 4 [MOD m] := by
    apply Nat.ModEq.trans _ (Nat.chineseRemainder four c.val 4).property.2
    simp [j,t,Nat.ModEq]
  have J : AtOrder m j := offdiag_four (by simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr jm)
  refine ⟨k*j,Nat.mul_pos kp (by dsimp [j]; omega),at_mul K J,by simpa using k4.mul j4,?_⟩
  apply ((km.trans (xm.pow 2)).mul jm).trans
  apply Nat.ModEq.trans _ rs
  have rel := (inv.pow 2).mul_left (s.val^2)
  convert rel using 1 <;> ring

theorem all_large_prime_power_squares {p : ℕ} (pp:p.Prime) (po:2 < p) (e:ℕ) :
    ∃ B : ℕ, ∀ n : ℕ, n≥B → IsSquare (n:ZMod (p^e)) → AtOrder (p^e) n := by
  classical
  let m := p^e
  have mp : 0 < m := pow_pos pp.pos _
  have odd : (2:ℕ).Coprime m := (two_coprime_prime pp po).pow_right e
  by_cases one : m=1
  · change ∃ B:ℕ, ∀ n:ℕ, n≥B → IsSquare (n:ZMod m) → AtOrder m n
    rw [one]
    exact ⟨0,fun _ _ _ => ones (Subsingleton.elim _ _)⟩
  have mh : 1 < m := by omega
  obtain ⟨U,hu⟩ := all_large_unit_squares mp odd
  have cls (i:Fin m) : ∃ B, ∀ n ≥ B, n ≡ i.val [MOD m] → IsSquare (n:ZMod m) → AtOrder m n := by
    by_cases ci : i.val.Coprime m
    · exact ⟨U,fun n hn ni sq => hu n hn (coprime_of_modEq ni ci) sq⟩
    by_cases square : IsSquare (i.val:ZMod m)
    · let a := i.val+m-1
      have ri : i.val ≡ a+1 [MOD m] := by rw [show a+1=i.val+m by dsimp [a];omega]; simp [Nat.ModEq]
      have pi : p ∣ i.val := by by_contra h; exact ci ((pp.coprime_iff_not_dvd.mpr h).symm.pow_right e)
      have pm : p ∣ m := dvd_pow_self p (by rintro rfl; apply one; simp [m])
      have pa : ¬p∣a := by
        intro dv
        have ds : p∣a+1 := by rw [show a+1=i.val+m by dsimp [a];omega]; exact dvd_add pi pm
        exact pp.not_dvd_one (by simpa using Nat.dvd_sub ds dv)
      obtain ⟨B,hB⟩ := composite_class_large mh odd ((pp.coprime_iff_not_dvd.mpr pa).symm.pow_right e) ri
        (square_seed_each_mod_four mh odd square)
      exact ⟨B,fun n hn ni _ => hB n hn ni⟩
    · exact ⟨0,fun n _ ni sq => (square ((ZMod.natCast_eq_natCast_iff _ _ _).mpr ni ▸ sq)).elim⟩
  choose B hB using cls
  refine ⟨Finset.univ.sup B,?_⟩
  intro n hn
  let i : Fin m := ⟨n%m,Nat.mod_lt _ mp⟩
  exact hB i n ((Finset.le_sup (Finset.mem_univ i)).trans hn) (Nat.mod_modEq n m).symm

#print axioms all_large_prime_power_squares
end HadamardMod
