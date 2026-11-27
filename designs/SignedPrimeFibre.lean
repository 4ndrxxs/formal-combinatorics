import SignedSelfVariance
import SignedSelfConjugacy

/-! A row of nonzero augmentation is invertible modulo the prime order of its fibre. -/

namespace Signed39.Contraction

open Finset

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {q : ℕ} [Fact q.Prime]

theorem prime_fibre_invertible (A B : H → ℤ) (hm : Fintype.card H=q)
    (unit : ¬(q:ℤ)∣mass A) (vanish : ∀t, (q:ℤ)∣cross A B t) : ∀x, (q:ℤ)∣B x := by
  let a : H → ZMod q := fun x=>(A x:ZMod q)
  let b : H → ZMod q := fun x=>(B x:ZMod q)
  have product : forward b*backward a=0 := by
    apply AddMonoidAlgebra.ext; ext t
    rw [cross_coeff]
    simpa [a,b,cross,mul_comm,add_comm] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (vanish t)
  have torsion (x:H) : q • x=0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp (hm ▸ (addOrderOf_dvd_card (x:=x)))
  have power : (backward a)^q=AddMonoidAlgebra.single 0 (mass A:ZMod q) := by
    have h:=frobenius_backward a 1
    rw [pow_one] at h
    rw [h]
    simp only [torsion,neg_zero]
    apply AddMonoidAlgebra.ext; ext t
    by_cases zero:t=0 <;> simp [zero,AddMonoidAlgebra.coeff_sum,a,mass]
  have all : forward b*(backward a)^q=0 := by
    obtain ⟨d,hd⟩:=Nat.exists_eq_succ_of_ne_zero (Fact.out:q.Prime).ne_zero
    have peq : (backward a)^q=(backward a)^(d+1) := congrArg (fun n:ℕ=>(backward a)^n) hd
    rw [peq,pow_succ',←mul_assoc,product,zero_mul]
  rw [power] at all
  have nz : (mass A:ZMod q)≠0 := fun z=>unit ((ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp z)
  intro x
  have scalar:=congrArg (fun f:AddMonoidAlgebra (ZMod q) H=>f.coeff x) all
  simp only [AddMonoidAlgebra.coeff_mul_single_apply,neg_zero,add_zero,forward_coeff] at scalar
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp ((mul_eq_zero.mp scalar).resolve_right nz)

variable {p : ℕ} [Fact p.Prime]

theorem two_excess_bound {k l s inv w : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k l f)
    (hn : k-l=(p:ℤ)*s) (hs : ¬(p:ℤ)∣s) (cop : p.Coprime (Fintype.card H))
    (hu : (p:ℤ)*inv=1+(Fintype.card H:ℤ)*w) (i j : ZMod p) (ij : i≠j) :
    let R (t : ZMod p) := (p:ℤ)^2*residueCost inv (Fintype.card H) (rowMass f i) (rowMass f t)
    let E (t : ZMod p) := variance (cross (row f i) (row f t))
    (E i-R i)+(E j-R j)≤(k-l)*variance (row f i)-(∑ t,R t) := by
  dsimp only
  let R (t : ZMod p) := (p:ℤ)^2*residueCost inv (Fintype.card H) (rowMass f i) (rowMass f t)
  let E (t : ZMod p) := variance (cross (row f i) (row f t))
  let F:=fun t=>E t-R t
  have non (t : ZMod p) : 0≤F t := sub_nonneg.mpr (mixed_pair_lower hf hn hs cop hu i t)
  have h := sum_le_sum_of_subset_of_nonneg (f:=F) (show ({i,j}:Finset (ZMod p))⊆univ by simp)
    (fun t _ _=>non t)
  have left : (∑ t∈({i,j}:Finset (ZMod p)), F t)=F i+F j := by simp [ij]
  rw [left] at h
  simp only [F,sum_sub_distrib] at h
  have e : (∑t,E t)=(k-l)*variance (row f i) := mixed_total_variance hf _
  rw [e] at h
  exact h

#print axioms prime_fibre_invertible

end Signed39.Contraction
