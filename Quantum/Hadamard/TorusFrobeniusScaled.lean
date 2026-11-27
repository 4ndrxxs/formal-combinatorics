import Quantum.Hadamard.TorusFrobeniusScaledBlocks
import Quantum.Hadamard.InvolutionOrbits

/-! Frobenius inflation of the Paley conference blocks with an arbitrary even
modular Hadamard matrix. The exact formula also records the change of order. -/
noncomputable section
namespace HadamardMod.TorusFrobenius

private def fixedAffine {E:Type} (f:E≃E) :
    Option {x:E // f x=x} ≃ {x:Option E // f.optionCongr x=x} where
  toFun
    | none => ⟨none,rfl⟩
    | some x => ⟨some x.val,congrArg some x.property⟩
  invFun
    | ⟨none,_⟩ => none
    | ⟨some x,h⟩ => some ⟨x,Option.some.inj h⟩
  left_inv y := by rcases y with _|⟨x,h⟩ <;> rfl
  right_inv y := by rcases y with ⟨_|x,h⟩ <;> rfl

private def fixedProduct {O I:Type} (e:O≃O) :
    ({x:O // e x=x} × I) ≃ {x:O×I // (e.prodCongr (Equiv.refl I)) x=x} where
  toFun
    | (x,i) => ⟨(x.val,i),Prod.ext x.property rfl⟩
  invFun x := (⟨x.val.1,congrArg Prod.fst x.property⟩,x.val.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem scaled_exact {m v:ℕ} (H:AtOrder m (2*v)) (t:ℕ) [Fact t.Prime] (ht:t%4=3) :
    AtOrder m (2*v*(t^2+1)+m*(v*t*(t-1))) := by
  let E := GaloisField t 2
  letI : Fintype E := Fintype.ofFinite E
  classical
  have card : Fintype.card E=t^2 := Nat.card_eq_fintype_card.symm.trans (GaloisField.card t 2 (by decide))
  let f := frobeniusEquiv E t
  have fApply (x:E) : f x=x^t := rfl
  have fTwice (x:E) : f (f x)=x := by
    rw [fApply,fApply,←pow_mul,←sq,←card]
    exact FiniteField.pow_card x
  have fFix : Nat.card {x:E // f x=x}=t :=
    (Nat.card_congr (Equiv.subtypeEquivRight (fun x:E => (Subfield.mem_bot_iff_pow_eq_self E t).symm))).trans
      (Subfield.natCard_bot E t)
  let e:=f.toEquiv.optionCongr
  have half : Nat.card {x:Option E // e x=x}=t+1 := by
    rw [←Nat.card_congr (fixedAffine f.toEquiv),Finite.card_option]
    exact congrArg (·+1) fFix
  let I := Fin v⊕Fin v
  let ec : I ≃ Fin (2*v) := Fintype.equivFinOfCardEq (by simp [I,two_mul])
  obtain ⟨A,g⟩ := H
  let σ := e.prodCongr (Equiv.refl I)
  have twice (x:Option E × I) : σ (σ x)=x := by
    rcases x with ⟨_|x,i⟩
    · rfl
    · exact Prod.ext (congrArg some (fTwice x)) rfl
  have fc : Nat.card {x:Option E × I // σ x=x}=2*v*(t+1) := by
    rw [←Nat.card_congr (fixedProduct (I:=I) e),Nat.card_prod,half]
    have cI : Nat.card I=2*v := by simp [I,Nat.card_sum,two_mul]
    rw [cI,Nat.mul_comm]
  have tc : Fintype.card (Option E × I)=2*v*(t^2+1) := by
    simp [I,card,two_mul,Nat.mul_comm]
  have char : ringChar E≠2 := by rw [ringChar.eq E t]; omega
  have res : Fintype.card E%4≠3 := by rw [card,pow_two,Nat.mul_mod,ht]; decide
  let C := conference char
  let D : Conference m (Option E) := reduce C
  have sym (i j:Option E) : D.entry i j=D.entry j i :=
    congrArg (fun z:ℤ => (z:ZMod m)) (conference_sym char res i j)
  have inv (i j:Option E) : D.entry (e i) (e j)=D.entry i j :=
    congrArg (fun z:ℤ => (z:ZMod m)) (conference_equivariant char f i j)
  obtain ⟨B,good,cov⟩ := conference_scaled D sym e inv _ (g.transport ec)
  obtain ⟨k,size,P⟩ := InvolutionStretch.inflate_involution (Q:=m+2) σ twice B good cov (by omega) (by simp)
  rw [fc,tc] at size
  rw [fc] at P
  have base : 2*v*(t+1)+2*(v*t*(t-1))=2*v*(t^2+1) := by
    zify [show 1≤t by omega]
    ring
  have ke : k=v*t*(t-1) := by omega
  rw [ke] at P
  convert P using 1
  calc
    _ = (2*v*(t+1)+2*(v*t*(t-1)))+m*(v*t*(t-1)) := by rw [base]
    _ = _ := by ring

theorem scaled_seed {m v : ℕ} (mp : 0 < m) (om:(2:ℕ).Coprime m) (hv:Odd v)
    (H:AtOrder m (2*v)) (t:ℕ) [Fact t.Prime] (ht:t%4=3) :
    ∃ h>0, AtOrder m h ∧ h ≡ 2 [MOD 4] ∧ h ≡ 2*v*(t^2+1) [MOD m] := by
  let k := v*t*(t-1)
  have ot : Odd t := Nat.odd_iff.mpr (by omega)
  have init : 2*v*(t^2+1) ≡ 0 [MOD 4] := by
    obtain ⟨z,hz⟩ := ot.pow (n:=2)
    apply Nat.modEq_zero_iff_dvd.mpr
    exact ⟨v*(z+1),by rw [hz];ring⟩
  have prod : Odd (m*v*t) := ((Nat.coprime_two_left.mp om).mul hv).mul ot
  have last : t-1 ≡ 2 [MOD 4] := by change (t-1)%4=2;omega
  have oddTwo : 2*(m*v*t) ≡ 2 [MOD 4] := by
    obtain ⟨z,hz⟩ := prod
    rw [hz]
    change (2*(2*z+1))%4=2
    omega
  have step : m*k ≡ 2 [MOD 4] := by
    change m*(v*t*(t-1)) ≡ _ [MOD _]
    rw [show m*(v*t*(t-1))=(t-1)*(m*v*t) by ring]
    exact (last.mul_right _).trans oddTwo
  refine ⟨2*v*(t^2+1)+m*k,?_,scaled_exact H t ht,by simpa using init.add step,?_⟩
  · have vp : 0 < v := by obtain ⟨z,hz⟩ := hv;omega
    positivity
  · simp [Nat.ModEq]

#print axioms scaled_exact
#print axioms scaled_seed
end HadamardMod.TorusFrobenius
