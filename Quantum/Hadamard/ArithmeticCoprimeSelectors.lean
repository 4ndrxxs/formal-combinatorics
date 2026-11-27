import Quantum.Hadamard.CompositeLift
import Quantum.Hadamard.ArithmeticBrouwer
import Quantum.Hadamard.ArithmeticSelector
import Mathlib.Data.Nat.Factorization.Induction

/-! A zero residue on any positive odd factor and four on its coprime
complement has every sufficiently large physical order. -/
noncomputable section
namespace HadamardMod
open Hadamard.Arithmetic Hadamard.PG

private theorem cf_geom_pair (q k : ℕ) :
    geom q (2*k)=(q+1)*geom (q^2) k := by
  induction k with
  | zero => simp [geom]
  | succ k ih =>
    rw [show 2*(k+1)=2*k+1+1 by ring,geom_succ q (2*k+1),
      geom_succ q (2*k),ih,geom_succ (q^2) k]
    ring

private theorem cf_geom_one {q m : ℕ} (h : q ≡ 1 [MOD m]) (k : ℕ) :
    geom q k ≡ k [MOD m] := by
  induction k with
  | zero => simpa [geom] using (Nat.ModEq.refl 0 : 0 ≡ 0 [MOD m])
  | succ k ih =>
    rw [geom_succ]
    simpa [add_comm] using (ih.mul h).add_left 1

theorem prime_product_affine {m e:ℕ} (mh:1 < m) (om:(2:ℕ).Coprime m)
    (em:m≤e) (x:ℕ) : AtOrder m ((x^e)^2) := by
  have ep : e≠0 := by omega
  induction x using Nat.recOnMul with
  | zero => simpa [zero_pow ep] using (ones (m:=m) (n:=0) (by simp))
  | one =>
    simpa using (show AtOrder m 1 from
      ⟨fun _ _ => 1,⟨fun _ _ => Or.inl rfl,fun i j ne => (ne (Subsingleton.elim i j)).elim⟩⟩)
  | prime p pp =>
    have : Fact p.Prime := ⟨pp⟩
    exact prime_power_affine mh om ep (em.trans (e.lt_two_pow_self.le.trans (Nat.pow_le_pow_left pp.two_le e)))
  | mul a b ha hb => simpa only [mul_pow] using at_mul ha hb

private theorem cf_prime {p b : ℕ} (pm : 1 < p) (op : (2:ℕ).Coprime p) (bp : 0<b)
    (odd : (2:ℕ).Coprime b) (cop : p.Coprime b) :
    ∃ q>p, q.Prime ∧ q ≡ 3 [MOD 4] ∧ q ≡ p-1 [MOD p^2] ∧ q ≡ 1 [MOD b] := by
  obtain ⟨a,ap,ab⟩ := Nat.chineseRemainder (cop.pow_left 2) (p-1) 1
  have cp : (p-1).Coprime p := (Nat.coprime_self_sub_left (by omega : 1≤p)).mpr (by simp)
  have ca : a.Coprime (p^2*b) := (coprime_of_modEq ap (cp.pow_right 2)).mul_right
    (coprime_of_modEq ab (by simp))
  have c4 : (4:ℕ).Coprime (p^2*b) := ((op.pow_left 2 : (4:ℕ).Coprime p).pow_right 2).mul_right (odd.pow_left 2)
  obtain ⟨q,big,prime,q4,qa⟩ := prime_crt (by decide : 4≠0) (by positivity : p^2*b≠0)
    c4 (by decide : (3:ℕ).Coprime 4) ca p
  exact ⟨q,big,prime,q4,(qa.of_dvd (dvd_mul_right _ _)).trans ap,
    (qa.of_dvd (dvd_mul_left _ _)).trans ab⟩

/-- All sufficiently large orders zero on an arbitrary nontrivial odd factor and four on the coprime odd complement. -/
theorem all_large_coprime_zero_four {p B : ℕ} (pm : 1 < p) (op : (2:ℕ).Coprime p) (bp : 0<B)
    (odd : (2:ℕ).Coprime B) (cop : p.Coprime B) :
    ∃ N, ∀ n ≥ N, p ∣ n → n ≡ 4 [MOD B] → AtOrder (p*B) n := by
  have pp0 : 0 < p := by omega
  have mh : 1<p*B := by nlinarith
  let e := B.totient*(p*B)
  have tot := Nat.totient_pos.mpr bp
  have em : p*B ≤ e := by dsimp [e]; nlinarith
  have ep : 0<e := by omega
  let h := (p^e)^2
  have A : AtOrder (p*B) h := prime_product_affine mh (op.mul_right odd) em p
  have hp : 0<h := pow_pos (pow_pos pp0 _) _
  have ph : p ∣ h := (dvd_pow_self p ep.ne').trans (dvd_pow_self _ (by decide : 2≠0))
  have h1 : h ≡ 1 [MOD B] := by
    have z : p^e ≡ 1 [MOD B] := by simpa [e,pow_mul] using (Nat.ModEq.pow_totient cop).pow (p*B)
    simpa [h] using z.pow 2
  obtain ⟨q,qp,pq,q4,qpp,qb⟩ := cf_prime pm op bp odd cop
  letI : Fact q.Prime := ⟨pq⟩
  let n := 2*(B-1)
  have dim : n+2=2*B := by dsimp [n]; omega
  have q1 : q+1 ≡ p [MOD p^2] := by simpa [Nat.sub_add_cancel (by omega : 1≤p)] using qpp.add_right 1
  obtain ⟨w,hw⟩ := (Nat.modEq_iff_dvd' (by omega : p≤q+1)).mp q1.symm
  have fact : q+1=p*(1+p*w) := by rw [mul_add,mul_one,← mul_assoc,← sq]; omega
  have qp1 : p ∣ q+1 := ⟨_,fact⟩
  have qc : q.Coprime p := pq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt pp0 qp)
  have qpmod : q^2 ≡ 1 [MOD p] := by
    have z := (ZMod.natCast_eq_zero_iff _ _).mpr qp1
    have neg : (q:ZMod p) = -1 := by push_cast at z; linear_combination z
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simp [neg]
  let s := geom q (2*B)
  let u := geom (q^2) B
  have sp : s=(q+1)*u := cf_geom_pair q B
  have uc : u.Coprime p := coprime_of_modEq (cf_geom_one qpmod B) cop.symm
  have sb : B ∣ s := by
    apply Nat.modEq_zero_iff_dvd.mp
    exact (cf_geom_one qb (2*B)).trans (by simp [Nat.ModEq])
  have ps : p ∣ s := by rw [sp]; exact dvd_mul_of_dvd_left qp1 _
  have ms : p*B ∣ s := cop.mul_dvd_of_dvd_of_dvd ps sb
  have me : p*B ∣ 2*q*s := dvd_mul_of_dvd_right ms _
  obtain ⟨t,step⟩ := me
  let f := 2*q*(1+p*w)*u
  have ec : 2*q*s = p*f := by rw [sp,fact]; dsimp [f]; ring
  have tf : f=B*t := by
    apply Nat.eq_of_mul_eq_mul_left pp0
    rw [← ec,step]; ring
  have cf : f.Coprime p := ((op.mul_left qc).mul_left
    ((Nat.coprime_add_mul_left_left 1 p w).mpr (by simp))).mul_left uc
  have ct : t.Coprime p := cf.of_dvd_left (tf ▸ dvd_mul_left _ _)
  have ht : h.Coprime t := (ct.symm.pow_left e).pow_left 2
  have gc : (p*B*h).gcd (2*q*s)=p*B := by rw [step,Nat.gcd_mul_left,ht.gcd_eq_one,mul_one]
  have rzP : 2*(q+1)*q^(n+1) ≡ 0 [MOD p] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right qp1 _) _)
  have rzB : 2*(q+1)*q^(n+1) ≡ 4 [MOD B] := by
    simpa using ((qb.add_right 1).mul_left 2).mul (qb.pow (n+1))
  have hzP : 4*h ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right ph _)
  have hzB : 4*h ≡ 4 [MOD B] := by simpa using h1.mul_left 4
  have congr : 4*h ≡ 2*(q+1)*q^(n+1) [MOD p*B] :=
    (Nat.modEq_and_modEq_iff_modEq_mul cop).mp ⟨hzP.trans rzP.symm,hzB.trans rzB.symm⟩
  have seed : ((4*h:ℕ):ZMod (p*B))=2*((q:ZMod (p*B))+1)*q^(n+1) := by
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr congr
  have sz : (geom q (n+2):ZMod (p*B))=0 := by
    rw [dim]; exact (ZMod.natCast_eq_zero_iff _ _).mpr ms
  obtain ⟨D⟩ := Hadamard.Brouwer.extender (n:=n) (m:=p*B) q4 (by rw [sz,mul_zero])
  have posS : 0<s := by
    rw [sp]
    have up : 0<u := by
      dsimp [u]
      rw [show B=(B-1)+1 by omega,geom_succ]
      omega
    positivity
  have eqv : 1+2*q*geom q (n+2)-1=2*q*s := by rw [dim]; dsimp [s]; omega
  obtain ⟨K,all⟩ := tensor_splice_progression A hp D
    (by rw [dim]; change 1<1+2*q*s; have := Nat.mul_pos (show 0<2*q by omega) posS; omega)
    (by rw [eqv]; exact gc) (by positivity : 0<p*B) seed
  exact ⟨K,fun k big kd kb => all k big ((Nat.modEq_and_modEq_iff_modEq_mul cop).mp
    ⟨(Nat.modEq_zero_iff_dvd.mpr kd).trans hzP.symm,kb.trans hzB.symm⟩)⟩

#print axioms all_large_coprime_zero_four
end HadamardMod
