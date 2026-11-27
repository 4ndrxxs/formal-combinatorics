import SignedSpectrum11

namespace Signed39.Template

open Finset Contraction

def bits (n:Fin 32) (j:Fin 5) : Bool := n.val.testBit j.val

theorem all_masks : ∀b:Fin 5→Bool,∃n:Fin 32,∀j,b j=bits n j := by decide +kernel

structure Case where
  W : Word
  plus : P
  minus : P

def Wmass (T:Case) (sg:ℤ) (i:P) : ℤ := 7+sg*word T.W i

def doomed (T:Case) (sg:ℤ) (i:P) : Prop :=
  let a:=Wmass T sg i
  ∀b:Fin 44,(2:ℤ)∣(b.val:ℤ)-a → (11:ℤ)∣23*(b.val:ℤ)+12*a^2 →
    23*(43*(b.val:ℤ)-a^2)<11*(∑j:P,residueCost 4 43 a (Wmass T sg j))

instance (T:Case) (sg:ℤ) (i:P) : Decidable (doomed T sg i) := by unfold doomed; infer_instance

def checked (T:Case) (n:Fin 32) : Prop := valid T.W (bits n) ∧ doomed T 1 T.plus ∧ doomed T (-1) T.minus
instance (T:Case) (n:Fin 32) : Decidable (checked T n) := by unfold checked; infer_instance

theorem no_473_of_templates (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hg:Fintype.card G=473) (T:Fin 32→Case) (cert:∀n,checked (T n) n) :
    ¬∃f:G→ℤ,IsSDS 265 12 f := by
  classical
  let : Fact (Nat.Prime 11):=⟨by decide⟩
  rintro ⟨F,hF⟩
  obtain ⟨K,hK,⟨E⟩⟩:=split_prime_factor (p:=11) (m:=43) hg (by decide)
  let H:=Additive K
  have hm : Fintype.card H=43 := Nat.card_eq_fintype_card.symm.trans hK
  have h0:=pullback hF E
  have sq:=sds_mass h0
  rw [Fintype.card_prod,ZMod.card,show Fintype.card (Additive K)=43 from hm] at sq
  let F':P×H→ℤ:=fun x=>F (E x)
  have sq':(mass F')^2=77^2 := by norm_num at sq ⊢; exact sq
  obtain ⟨f,hf,ms⟩ : ∃f:P×H→ℤ, IsSDS 265 12 f ∧ mass f=77 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp sq' with pos|neg
    · exact ⟨F',h0,pos⟩
    · exact ⟨fun x=> -F' x,h0.neg,by simpa only [mass,sum_neg_distrib,neg_eq_iff_eq_neg] using neg⟩
  let A:=rowMass f
  let u (i:P):=A i-7
  have norm : (265:ℤ)-12=(11:ℤ)*23 := by decide
  obtain ⟨c,mc,_,_,cor⟩:=centered_row_corr hf norm
  have eqc:c=7 := by rw [ms] at mc; omega
  subst c
  have flat (t:P) : corr u t=(if t=0 then 253 else 0)-23 := cor t
  have mu : mass u=0 := by
    have mA:= (mass_rowmass f).trans ms
    change (∑i,A i)=77 at mA
    simp [mass,u,sum_sub_distrib,mA,ZMod.card]
  have eu : energy u=230 := by rw [energy_zero,flat]; decide
  obtain ⟨b,hb⟩:=choose_roots u flat
  obtain ⟨n,bn⟩:=all_masks b
  have be:b=bits n:=funext bn
  subst b
  let C:=T n
  obtain ⟨v,dplus,dminus⟩:=cert n
  have dm:=template_modulus u flat (bits n) hb C.W v
  obtain ⟨t,sg,hsg,form⟩:=template_match_11 u (word C.W) mu eu v.1 v.2.1 dm
  have mass_form (i:P) : A i=Wmass C sg (i-t) := by have e:=form i; change A i-7=sg*word C.W (i-t) at e; dsimp [Wmass]; omega
  obtain ⟨i,doom⟩ : ∃i:P,doomed C sg i := by
    rcases hsg with rfl|rfl
    · exact ⟨C.plus,dplus⟩
    · exact ⟨C.minus,dminus⟩
  let j:=i+t
  let a:=Wmass C sg i
  let B:=energy (row f j)
  have aj : A j=a := by simpa [j,a] using mass_form (i+t)
  have ph : Nat.Coprime 11 (Fintype.card H) := hm ▸ (by decide : Nat.Coprime 11 43)
  have raw:=row_admissible (s:=23) (c:=7) hf norm ms ph j
  change admissibleRow 11 (Fintype.card H) 23 12 7 (A j) B at raw
  rw [hm,aj] at raw
  obtain ⟨_,_,lo,hi,even,disc,_⟩:=raw
  let b':Fin 44:=⟨B.toNat,by omega⟩
  have bval:(b'.val:ℤ)=B:=Int.toNat_of_nonneg lo
  have no:=doom b'
  change (2:ℤ)∣(b'.val:ℤ)-a → (11:ℤ)∣23*(b'.val:ℤ)+12*a^2 → _ at no
  rw [bval] at no
  have forbidden:=no even disc
  have bound:=mixed_anchor_bound (inv:=4) (w:=1) hf norm (by decide) ph (by rw [hm]; decide) j
  change (11:ℤ)*(∑z:P,residueCost 4 (Fintype.card H) (A j) (A z)) ≤ 23*((Fintype.card H:ℤ)*B-(A j)^2) at bound
  rw [hm,aj] at bound
  change 11*(∑z:P,residueCost 4 43 a (A z))≤23*(43*B-a^2) at bound
  have translate : (∑z:P,residueCost 4 43 a (A z))=∑z:P,residueCost 4 43 a (Wmass C sg z) := by
    simp only [mass_form]
    simpa only [sub_eq_add_neg] using sum_translate (fun z=>residueCost 4 43 a (Wmass C sg z)) (-t)
  rw [translate] at bound
  exact (not_lt_of_ge bound) forbidden

end Signed39.Template
