module
public import Quantum.FractionalImpossibleData

/-! Every exterior symbol occupies one perfect matching of the three type sets. -/
@[expose] public section
noncomputable section
namespace ImpossibleSudoku
open QuantumSudoku FractionalLayouts Finset

set_option maxRecDepth 80000
set_option maxHeartbeats 0

private def go (a : Fin 37) (r : I) : I := Fin.ofNat 39 (rcGo[a.val*39+r.val]!)
private def back (a : Fin 37) (c : I) : I := Fin.ofNat 39 (rcBack[a.val*39+c.val]!)

private theorem rc_good : ∀ (a : Fin 37) (r : I),rcClass[r.val*39+(go a r).val]! = a.val := by decide +kernel
private theorem rc_inv : ∀ (a : Fin 37) (c : I),go a (back a c)=c := by decide +kernel
private theorem rc_diag : ∀ r : I,rcClass[r.val*39+r.val]! = 37 := by decide +kernel
private theorem rc_pair : ∀ r : I,rcClass[r.val*39+(partner r).val]! = 38 := by decide +kernel
private theorem pair_inv : ∀ c : I,partner (Fin.ofNat 39 (partnerInverse[c.val]!))=c := by decide +kernel

private def finalIndex (j : Fin 10) : U := ⟨1507+j.val,by omega⟩
private theorem residual : ∀ d r (j : Fin 10),face tag d r (outsidePos d r (finalIndex j))=24+(finalIndex j).val := by
  intro d
  cases d <;> decide +kernel

private theorem shift_go (r : I) {d : ℕ} (hd : d<39) : shift (plusShift r d) r=d := by
  unfold shift plusShift
  simp only [Fin.val_ofNat]
  omega

private theorem shift_back (t : I) {d : ℕ} (hd : d<39) : plusShift (minusShift t d) d=t := by
  apply Fin.ext
  simp only [plusShift,minusShift,Fin.val_ofNat]
  omega

private theorem atGo (u : U) (r : I) (hu : u.val<1507) :
    tag r (extGo u r).1 (extGo u r).2=24+u.val := by
  by_cases hl : u.val<1443
  · let a : Fin 37 := ⟨u.val/39,by omega⟩
    change tag r (extGo u r).1 (extGo u r).2=_
    simp only [extGo,hl,if_true]
    change tag r (go a r) (plusShift r (u.val%39))=_
    simp only [tag,rc_good,Fin.is_lt,if_true,shift_go _ (Nat.mod_lt _ (by decide : 0<39))]
    dsimp [a]
    omega
  · have hd : 4+(u.val-1443)%32<36 := by omega
    have h39 : 4+(u.val-1443)%32<39 := by omega
    by_cases hhalf : u.val<1475
    · simp only [extGo,hl,if_false,hu,if_true,hhalf,tag,rc_diag,shift_go _ h39]
      simp only [show ¬37<37 by decide,if_false,show 4≤4+(u.val-1443)%32 by omega,hd,and_self,if_true]
      omega
    · simp only [extGo,hl,if_false,hu,if_true,hhalf,tag,rc_pair,shift_go _ h39]
      simp only [show ¬38<37 by decide,if_false,show 4≤4+(u.val-1443)%32 by omega,hd,and_self,if_true]
      omega

private theorem col_inv (u : U) (c : I) (hu : u.val<1507) : (extGo u (atColumn u c)).1=c := by
  by_cases hl : u.val<1443
  · let a : Fin 37 := ⟨u.val/39,by omega⟩
    simpa [extGo,atColumn,hl,go,back,a] using rc_inv a c
  · by_cases hhalf : u.val<1475
    · simp [extGo,atColumn,hl,hu,hhalf]
    · simpa [extGo,atColumn,hl,hu,hhalf] using pair_inv c

private theorem type_inv (u : U) (t : I) (hu : u.val<1507) : (extGo u (atType u t)).2=t := by
  by_cases hl : u.val<1443
  · simpa [extGo,atType,hl] using shift_back t (Nat.mod_lt u.val (by decide : 0<39))
  · simpa [extGo,atType,hl,hu] using shift_back t (show 4+(u.val-1443)%32<39 by omega)

theorem outside_tag (d : Direction) (k : I) (u : U) : face tag d k (outsidePos d k u)=24+u.val := by
  by_cases hu : u.val<1507
  · cases d with
    | row => exact atGo u k hu
    | column =>
      have h := atGo u (atColumn u k) hu
      rw [col_inv u k hu] at h
      exact h
    | block =>
      have h := atGo u (atType u k) hu
      rw [type_inv u k hu] at h
      exact h
  · let j : Fin 10 := ⟨u.val-1507,by omega⟩
    have eq : finalIndex j=u := by apply Fin.ext; dsimp [finalIndex,j]; omega
    simpa [eq] using residual d k j

theorem index_correct (d : Direction) (k : I) (s : Word) :
    face tag d k (placement d k s)=expected d k s := by
  cases s with
  | inl i => exact active_tag d k i
  | inr u => exact outside_tag d k u

theorem expected_inj (d : Direction) (k : I) : Function.Injective (expected d k) := by
  have h : ∀ d k, Function.Injective (frame d k) := by intro i; cases i <;> decide +kernel
  rintro (a|a) (b|b) e
  · exact congrArg Sum.inl (h d k (Fin.ext e))
  · change (frame d k a).val=24+b.val at e
    have := (frame d k a).isLt
    omega
  · change 24+a.val=(frame d k b).val at e
    have := (frame d k b).isLt
    omega
  · exact congrArg Sum.inr (Fin.ext (Nat.add_left_cancel e))

def symbol : Word ≃ Pair := Fintype.equivOfCardEq (by simp [Word,Pair,I,U])

theorem placement_inj (d : Direction) (k : I) : Function.Injective (placement d k) := by
  intro a b e
  apply expected_inj d k
  rw [←index_correct,←index_correct,e]

def ordered (d : Direction) (k : I) : Word ≃ Pair := by
  let f := fun i : Pair => placement d k (symbol.symm i)
  have hi : Function.Injective f := (placement_inj d k).comp symbol.symm.injective
  exact symbol.trans (Equiv.ofBijective f (Finite.injective_iff_bijective.mp hi))

@[simp] theorem ordered_apply (d : Direction) (k : I) (s : Word) :
    ordered d k s=placement d k s := by simp [ordered]

#print axioms index_correct
end ImpossibleSudoku
