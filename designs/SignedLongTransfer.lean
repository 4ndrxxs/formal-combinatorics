import SignedLongCertificate
import SignedSplit

/-! Transport cyclic or two-prime direct-product exclusions to the catalogue's group models. -/

namespace Signed39.Contraction

theorem long_cyclic_transfer (p m:ℕ) [NeZero p] [NeZero m] {k l:ℤ} (hc:p.Coprime m)
    (bad:¬∃f:ZMod p×ZMod m→ℤ,IsSDS k l f) : ¬∃f:ZMod (p*m)→ℤ,IsSDS k l f := by
  rintro ⟨f,hf⟩
  exact bad ⟨_,pullback hf (ZMod.chineseRemainder hc).toAddEquiv.symm⟩

theorem long_prime_pair_transfer (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (p m:ℕ) [Fact p.Prime] [Fact m.Prime] {k l:ℤ} (hc:p.Coprime m) (hg:Fintype.card G=p*m)
    (bad:¬∃f:ZMod p×ZMod m→ℤ,IsSDS k l f) : ¬∃f:G→ℤ,IsSDS k l f := by
  classical
  rintro ⟨f,hf⟩
  obtain ⟨K,hK,⟨E⟩⟩:=split_prime_factor hg hc
  let eK:ZMod m≃+Additive K:= (ZMod.ringEquivCongr hK.symm).toAddEquiv.trans
    (zmodAddCyclicAddEquiv (isAddCyclic_of_prime_card (show Nat.card (Additive K)=m from hK)))
  exact bad ⟨_,pullback hf (((AddEquiv.refl _).prodCongr eK).trans E)⟩

theorem long_transfer_11_33 {k l:ℤ} (bad:¬∃f:ZMod 3×(ZMod 11×ZMod 11)→ℤ,IsSDS k l f) :
    ¬∃f:ZMod 11×ZMod 33→ℤ,IsSDS k l f := by
  let E:ZMod 3×(ZMod 11×ZMod 11)≃+ZMod 11×ZMod 33:=
    AddEquiv.prodComm.trans (AddEquiv.prodAssoc.trans
      ((AddEquiv.refl _).prodCongr (ZMod.chineseRemainder (by decide:Nat.Coprime 11 3)).toAddEquiv.symm))
  rintro ⟨f,hf⟩
  exact bad ⟨_,pullback hf E⟩

end Signed39.Contraction
