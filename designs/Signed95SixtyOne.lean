import SignedMixedCertificate

/-! A mixed-row proof of the cyclic (95,61,6) nonexistence case. -/

namespace Signed39.NinetyFiveSixtyOne

open Finset Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def doomed (v : List ℤ) (a : ℤ) : Prop :=
  ∀ b : Fin 20, let B := (b.val:ℤ)
    admissibleRow 5 19 11 6 5 a B → admissibleShift 5 19 a B → admissibleFull 5 19 a B →
    11*(19*B-a^2)<5*(v.map (residueCost 4 19 a)).sum

private instance (v : List ℤ) (a : ℤ) : Decidable (doomed v a) := by unfold doomed; infer_instance

private theorem possible : ∀ A B C D : Fin 13,
    let x := (A.val:ℤ)-1; let y := (B.val:ℤ)-1; let z := (C.val:ℤ)-1; let w := (D.val:ℤ)-1
    let u := 25-x-y-z-w; let v := [x,y,z,w,u]
    (-1:ℤ)≤u → u≤11 → x^2+y^2+z^2+w^2+u^2=169 → x*y+y*z+z*w+w*u+u*x=114 →
    ([0,4,6,9].map v.count=[1,1,2,1] ∧ 9∈v ∧ doomed v 9) ∨
    ([1,4,6,10].map v.count=[1,2,1,1] ∧ 10∈v ∧ doomed v 10) := by decide +kernel

private theorem sumFive (a : ZMod 5 → ℤ) : (∑ i, a i)=a 0+a 1+a 2+a 3+a 4 := by
  have U : (univ : Finset (ZMod 5))={0,1,2,3,4} := by decide
  rw [U]
  simp (config:={ decide := true })
  ring

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

private theorem impossible {f : ZMod 5 × H → ℤ} (hf : IsSDS 61 6 f) (hm : Fintype.card H=19)
    (hmass : mass f=25) : False := by
  let a := rowMass f
  have cop : Nat.Coprime 5 (Fintype.card H) := hm ▸ (by decide : Nat.Coprime 5 19)
  have hn : (61:ℤ)-6=(5:ℤ)*11 := by decide
  have bounds (i : ZMod 5) : -1≤a i ∧ a i≤11 := by
    have e := (centered_row_bounds (c:=5) hf hn hmass (q:=1) (e:=0) (Or.inl rfl) i).2
    change (a i-5)^2≤44 at e
    constructor
    · by_contra! h
      nlinarith [mul_nonneg (show 0≤ -2-a i by omega) (show 0≤12-a i by omega)]
    · by_contra! h
      nlinarith [mul_nonneg (show 0≤a i-12 by omega) (show 0≤a i+2 by omega)]
  let code (i : ZMod 5) : Fin 13 := ⟨(a i+1).toNat,by have := bounds i; omega⟩
  have dec (i : ZMod 5) : ((code i).val:ℤ)-1=a i := by dsimp [code]; have := bounds i; omega
  have mass5 := (mass_rowmass f).trans hmass
  change (∑ i,a i)=25 at mass5
  rw [sumFive] at mass5
  have u : 25-a 0-a 1-a 2-a 3=a 4 := by omega
  have sq : (∑ i,(a i)^2)=169 := by
    change energy (rowMass f)=_
    simpa [energy_zero,hm] using rowmass_corr hf 0
  rw [sumFive] at sq
  have neig : (∑ i, a i*a (i+1))=114 := by
    change corr (rowMass f) 1=_
    simpa [hm] using rowmass_corr hf 1
  rw [sumFive] at neig
  have e1 : (1:ZMod 5)+1=2 := by decide
  have e2 : (2:ZMod 5)+1=3 := by decide
  have e3 : (3:ZMod 5)+1=4 := by decide
  have e4 : (4:ZMod 5)+1=0 := by decide
  simp only [zero_add,e1,e2,e3,e4] at neig
  have h := possible (code 0) (code 1) (code 2) (code 3)
  simp only [dec,u] at h
  have classified := h (bounds 4).1 (bounds 4).2 sq neig
  obtain ⟨A,mem,blocked⟩ : ∃ A∈[a 0,a 1,a 2,a 3,a 4], doomed [a 0,a 1,a 2,a 3,a 4] A := by
    rcases classified with ⟨_,mem,cut⟩|⟨_,mem,cut⟩
    · exact ⟨9,mem,cut⟩
    · exact ⟨10,mem,cut⟩
  obtain ⟨i,hi⟩ : ∃ i : ZMod 5, a i=A := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
    · exact ⟨4,rfl⟩
  let b := energy (row f i)
  have raw := row_admissible (c:=5) hf hn hmass cop i
  have sh := row_shift_admissible hf hn (by decide) cop i
  have four := full_row_admissible hf hn (by decide) cop (hm ▸ (by decide : Nat.Coprime (4*5) 19))
    (by decide : IsCoprime (4:ℤ) 5) i
  rw [hm] at raw sh four
  change admissibleRow 5 19 11 6 5 (a i) b at raw
  change admissibleShift 5 19 (a i) b at sh
  change admissibleFull 5 19 (a i) b at four
  rw [hi] at raw sh four
  have b0 := raw.2.2.1
  have b19 := raw.2.2.2.1
  let B : Fin 20 := ⟨b.toNat,by omega⟩
  have ev : (B.val:ℤ)=b := Int.toNat_of_nonneg b0
  have cut := blocked B
  simp only [ev] at cut
  have bad := cut raw sh four
  have inverse : (5:ℤ)*4=1+(Fintype.card H:ℤ)*1 := by rw [hm]; decide
  have both := mixed_anchor_bound hf hn (by decide) cop inverse i
  rw [hm,sumFive] at both
  change 5*(_+_+_+_+_)≤11*((Fintype.card H:ℤ)*b-(a i)^2) at both
  rw [hm] at both
  change rowMass f i=A at hi
  rw [hi] at both
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] at bad
  dsimp only [a] at bad both
  simp only [hi,Nat.cast_ofNat,add_assoc] at both
  exact (not_lt_of_ge both) bad

theorem no_abelian_95_61_6 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=95) : ¬∃ f : G → ℤ, IsSDS 61 6 f := by
  classical
  rintro ⟨f,hf⟩
  obtain ⟨K,hK,⟨e⟩⟩ := split_prime_factor (p:=5) (m:=19) hG (by decide)
  have hH : Fintype.card (Additive K)=19 := Nat.card_eq_fintype_card.symm.trans hK
  have h := pullback hf e
  have mass := sds_mass h
  norm_num [Fintype.card_prod,ZMod.card,hH] at mass
  have eq : (Signed39.Contraction.mass (fun x => f (e x)))^2=(25:ℤ)^2 := by simpa using mass
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp eq with hp|hn
  · exact impossible h hH hp
  · exact impossible h.neg hH (by simpa only [Signed39.Contraction.mass,sum_neg_distrib,neg_eq_iff_eq_neg] using hn)

#print axioms no_abelian_95_61_6

end Signed39.NinetyFiveSixtyOne
