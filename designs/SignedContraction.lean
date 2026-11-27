import SignedBasic

/-! Modular contraction for an abelian product with a cyclic prime factor. -/

noncomputable section

namespace Signed39.Contraction

open Finset

variable {G R : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] [CommRing R]

def forward (f : G → R) : AddMonoidAlgebra R G := ∑ x : G, AddMonoidAlgebra.single x (f x)
def backward (f : G → R) : AddMonoidAlgebra R G := ∑ x : G, AddMonoidAlgebra.single (-x) (f x)

omit [AddCommGroup G] in
@[simp] theorem forward_coeff (f : G → R) (x : G) : (forward f).coeff x = f x := by
  simp [forward,Finsupp.single_apply]

theorem cross_coeff (f g : G → R) (x : G) :
    (forward f * backward g).coeff x = ∑ y : G, f (x+y)*g y := by
  simp [backward,mul_sum,AddMonoidAlgebra.coeff_sum,AddMonoidAlgebra.coeff_mul_single_apply]

variable {p : ℕ} [Fact p.Prime]

omit [DecidableEq G] in
theorem frobenius_backward (f : G → ZMod p) (r : ℕ) :
    (backward f)^(p^r) = ∑ x : G, AddMonoidAlgebra.single (-(p^r • x)) (f x) := by
  have : ExpChar (AddMonoidAlgebra (ZMod p) G) p :=
    expChar_of_injective_ringHom (algebraMap (ZMod p) (AddMonoidAlgebra (ZMod p) G)).injective p
  rw [← iterateFrobenius_def]
  simp only [backward,map_sum,iterateFrobenius_def,AddMonoidAlgebra.single_pow,
    smul_neg,ZMod.pow_card_pow]

theorem flat_mod {k lam : ℤ} {f : G → ℤ} (h : IsSDS k lam f) (hp : (p:ℤ) ∣ k-lam) (t : G) :
    (corr f t : ZMod p) = (lam:ZMod p) := by
  have hk : (k:ZMod p) = (lam:ZMod p) := by
    apply sub_eq_zero.mp
    simpa only [Int.cast_sub] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hp
  rw [h.flat]
  split <;> simp_all

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def fiber {P : Type} [Fintype P] (f : P × H → ℤ) (x : H) : ℤ := ∑ i : P, f (i,x)
def matched (a s : H → ℤ) (z : H) : ℤ := ∑ x : H, a x * s (x-z)

omit [DecidableEq H] in
theorem matched_shift (a s : H → ℤ) (z : H) :
    matched a s z = ∑ y : H, a (z+y)*s y := by
  symm
  apply Fintype.sum_equiv (Equiv.addLeft z)
  intro y
  simp

omit [DecidableEq H] in
theorem nsmul_contract (hc : p.Coprime (Fintype.card H)) (z : ZMod p × H) :
    (p^(Fintype.card H).totient) • z = (0,z.2) := by
  have ht : 0 < (Fintype.card H).totient := Nat.totient_pos.mpr Fintype.card_pos
  apply Prod.ext
  · change p^(Fintype.card H).totient • z.1 = 0
    simp [nsmul_eq_mul,ht.ne']
  · change p^(Fintype.card H).totient • z.2 = z.2
    exact (nsmul_eq_nsmul_iff_modEq.mpr ((Nat.ModEq.pow_totient hc).of_dvd (addOrderOf_dvd_card (x := z.2)))).trans
      (one_nsmul _)

theorem mass_dvd {k lam : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f)
    (hp : (p:ℤ) ∣ k-lam) : (p:ℤ) ∣ ∑ x, f x := by
  have mass2 := congrArg (fun x : ℤ => (x : ZMod p)) (mass_sq f)
  simp only [Int.cast_pow,Int.cast_sum] at mass2
  simp_rw [flat_mod hf hp] at mass2
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  simpa [Fintype.card_prod,ZMod.card] using mass2

theorem matched_dvd {k lam : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f)
    (hp : (p:ℤ) ∣ k-lam) (hc : p.Coprime (Fintype.card H)) (i : ZMod p) (z : H) :
    (p:ℤ) ∣ matched (fun x => f (i,x)) (fiber f) z := by
  let g := fun x : ZMod p × H => (f x : ZMod p)
  have hm : (∑ x, g x) = 0 := by
    simpa [g] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (mass_dvd hf hp)
  have hpair : forward g * backward g = forward (fun _ : ZMod p × H => (lam:ZMod p)) := by
    apply AddMonoidAlgebra.ext; ext t
    rw [cross_coeff, forward_coeff]
    simpa [g,corr,add_comm,mul_comm] using flat_mod hf hp t
  have hconst : forward (fun _ : ZMod p × H => (lam:ZMod p)) * backward g = 0 := by
    apply AddMonoidAlgebra.ext; ext t
    rw [cross_coeff, ← mul_sum, hm]
    simp
  let r := (Fintype.card H).totient
  have hr : 0 < r := Nat.totient_pos.mpr Fintype.card_pos
  have hpow : 2 ≤ p^r := by have hpr := (Fact.out : p.Prime).two_le; exact hpr.trans (Nat.le_pow hr)
  obtain ⟨l,hl⟩ := Nat.exists_eq_add_of_le hpow
  have hz : forward g * (backward g)^(p^r) = 0 := by
    rw [hl,pow_add,pow_two, ← mul_assoc, ← mul_assoc,hpair,hconst,zero_mul]
  rw [frobenius_backward] at hz
  simp only [r,nsmul_contract hc,Prod.neg_mk,neg_zero,mul_sum] at hz
  have h := congrArg (fun u : AddMonoidAlgebra (ZMod p) (ZMod p × H) => u.coeff (i,z)) hz
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_mul_single_apply,
    Prod.neg_mk, neg_zero, neg_neg, Prod.mk_add_mk, add_zero, forward_coeff] at h
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  rw [matched_shift]
  simp only [Int.cast_sum,Int.cast_mul,fiber,mul_sum]
  rw [sum_comm]
  simpa [Fintype.sum_prod_type, g] using h

end Signed39.Contraction
