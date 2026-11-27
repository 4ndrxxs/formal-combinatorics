import Quantum.Hadamard.NearHadamardBorders
import Quantum.Hadamard.ProjectiveSupportCorrelations

/-! Compare a core with the signed incidences in Theorem 4.1 on the actual
field-indexed Paley matrix. The zero and infinity points supply its border. -/

noncomputable section
open Matrix Finset
open Hadamard.NearBorder Hadamard.ProjectiveSigning
namespace Hadamard.MSXCore

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

abbrev SquareIndex (F : Type) [Field F] [Fintype F] [DecidableEq F] := {x : F // quadraticChar F x=1}

def fieldPoint (w : F) (e : Fin m ≃ SquareIndex F) : Index m → Option F
  | .inl (false,k) => some (e k).val
  | .inl (true,k) => some (w*(e k).val)
  | .inr false => some 0
  | .inr true => none

private theorem eq_of_coords (e : Fin m ≃ SquareIndex F) {k l : Fin m}
    (h : (e k).val=(e l).val) : k=l := e.injective (Subtype.ext h)

def chart (w : F) (hw : quadraticChar F w= -1) (e : Fin m ≃ SquareIndex F) : Index m ≃ Option F := by
  have zero (k : Fin m) : (e k).val≠0 := by
    intro h
    have h' := (e k).property
    rw [h] at h'; norm_num at h'
  have wn : w≠0 := by intro h; subst w; simp at hw
  have opposite (k l : Fin m) : (e k).val≠w*(e l).val := by
    intro h
    have a := congrArg (quadraticChar F) h
    rw [map_mul,hw,(e l).property,(e k).property] at a
    norm_num at a
  refine Equiv.ofBijective (fieldPoint w e) ⟨?_,?_⟩
  · rintro (⟨b,k⟩|b) (⟨c,l⟩|c) h
    · cases b <;> cases c
      · have eq := eq_of_coords e (Option.some.inj h)
        simp [eq]
      · exact (opposite k l (Option.some.inj h)).elim
      · exact (opposite l k (Option.some.inj h).symm).elim
      · have eq := eq_of_coords e (mul_left_cancel₀ wn (Option.some.inj h))
        simp [eq]
    · cases b <;> cases c <;> simp [fieldPoint,zero,wn] at h
    · cases b <;> cases c <;> simp [fieldPoint,wn,zero] at h
      exact (zero l h.symm).elim
    · cases b <;> cases c <;> simp_all [fieldPoint]
  · intro x
    cases x with
    | none => exact ⟨rim true,rfl⟩
    | some x =>
      by_cases z : x=0
      · subst x; exact ⟨rim false,rfl⟩
      rcases quadraticChar_dichotomy z with h|h
      · refine ⟨bulk false (e.symm ⟨x,h⟩),?_⟩
        simp [fieldPoint]
      · have one : quadraticChar F (x/w)=1 := by
          have t := congrArg (quadraticChar F) (show w*(x/w)=x by field_simp)
          rw [map_mul,hw,h] at t; omega
        refine ⟨bulk true (e.symm ⟨x/w,one⟩),?_⟩
        simp [fieldPoint]
        field_simp

@[simp] theorem chart_apply (w : F) (hw : quadraticChar F w= -1) (e : Fin m ≃ SquareIndex F) (t) :
    chart w hw e t=fieldPoint w e t := rfl

def splitSign (i : Bool) : Option F → Bool
  | none => false
  | some x => if x=0 then true else decide (quadraticChar F x= -cosetSign i)

def signInt (i : Bool) (p : Option F) : ℤ := if splitSign i p then 1 else -1

theorem split_nonzero (i : Bool) (x : F) (nz : x≠0) :
    signInt i (some x) = -cosetSign i*quadraticChar F x := by
  rcases quadraticChar_dichotomy nz with h|h <;> cases i <;>
    simp only [signInt,splitSign,ite_eq_right nz,cosetSign,h] <;> decide

theorem split_resolves (i : Bool) :
    (∀t : Option F, quadraticValue 0 1 0 t≠0 → signInt i t= -cosetSign i*quadraticChar F (quadraticValue 0 1 0 t)) ∧
    (∑t : Option F, if quadraticValue 0 1 0 t=0 then signInt i t else 0)=0 := by
  constructor
  · rintro (_|x)
    · simp [quadraticValue]
    · simpa [quadraticValue] using split_nonzero i x
  · rw [Fintype.sum_option]
    simp [quadraticValue,signInt,splitSign]

def reference (i : Bool) : Matrix (Option F) (Option F) ℝ :=
  realPaley+diagonal (fun t ↦ (signInt i t:ℝ))


theorem reference_gram (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (i : Bool) (x y : Option F) :
    (reference (F:=F) i*(reference (F:=F) i).transpose) x y =
      if x=y then (Fintype.card F:ℝ)+1 else
        ((signInt i x:ℝ)+(signInt i y:ℝ))*realPaley x y := by
  let C : Matrix (Option F) (Option F) ℝ := realPaley
  let d (t : Option F) : ℝ := signInt i t
  let P := HadamardMod.TorusFrobenius.conference (F:=F) hc
  have sy (u v : Option F) : C u v=C v u := by
    have h := HadamardMod.TorusFrobenius.conference_sym hc (by omega) u v
    change (HadamardMod.TorusFrobenius.entry u v:ℤ)=(HadamardMod.TorusFrobenius.entry v u:ℤ) at h
    dsimp [C,realPaley]
    exact_mod_cast h
  have diag (u : Option F) : C u u=0 := by
    have eq := P.diag u
    change (HadamardMod.TorusFrobenius.entry u u:ℤ)=0 at eq
    change ((HadamardMod.TorusFrobenius.entry u u:ℤ):ℝ)=0
    exact_mod_cast eq
  have val (u k : Option F) : C u k * C u k=1-(if k=u then 1 else 0) := by
    by_cases eq : k=u
    · subst k; simp [diag]
    · rcases P.sign u k (Ne.symm eq) with a|a
      · have t : C u k=1 := by change ((HadamardMod.TorusFrobenius.entry u k:ℤ):ℝ)=1; exact_mod_cast a
        simp [eq,t]
      · have t : C u k= -1 := by change ((HadamardMod.TorusFrobenius.entry u k:ℤ):ℝ)= -1; exact_mod_cast a
        simp [eq,t]
  have square : C*C.transpose=(Fintype.card F:ℝ) • (1 : Matrix (Option F) (Option F) ℝ) := by
    ext u v
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
    by_cases eq : u=v
    · subst v; simp [val,sum_sub_distrib,Fintype.card_option]
    · have h := P.off u v eq
      change (∑ k:Option F,(HadamardMod.TorusFrobenius.entry u k:ℤ)*HadamardMod.TorusFrobenius.entry v k)=0 at h
      simp only [ite_eq_right eq,mul_zero]
      dsimp [C,realPaley]
      exact_mod_cast h
  change ((C+diagonal d)*(C+diagonal d).transpose) x y=_
  rw [transpose_add,diagonal_transpose,add_mul,mul_add,mul_add,square,diagonal_mul_diagonal]
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,mul_diagonal,diagonal_mul,
    diagonal_apply,transpose_apply]
  by_cases eq : x=y
  · subst y
    simp only [ite_true,mul_one,diag,mul_zero,zero_mul,add_zero]
    unfold d signInt
    split <;> norm_num
  · simp only [ite_eq_right eq,mul_zero,zero_add,add_zero]
    rw [sy y x]
    change C x y*d y+d x*C x y=(d x+d y)*C x y
    ring

#print axioms reference_gram


private def bit (b : Bool) : ℝ := if b then 1 else -1

/-- Any regular sign-border completion with the Gram data of the two signed
incidences has the absolute determinant of the split Paley completion.
The near-Hadamard partition need not be supplied in Paley order. -/
theorem compare_incidence_border (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (hm : 2 ≤ m) (w : F) (hw : quadraticChar F w= -1) (e : Fin m ≃ SquareIndex F)
    (i j : Bool) (A : Matrix (Core m) (Core m) ℝ) (T L H : Matrix Bool Bool ℝ)
    (ht : Signs T) (hl : Signs L) (hh : Signs H) (reg : Regular A)
    (blocks : ∀ a k l, (A*A.transpose) (a,k) (a,l)=
      (incidenceGram w i j (e k).val (e l).val:ℝ))
    (pm : Partition (bordered A T L H*(bordered A T L H).transpose)) :
    |(bordered A T L H).det|=|(reference (F:=F) i).det| := by
  let E := chart w hw e
  let N := (reference (F:=F) i).submatrix E E
  let g (t : Index m) := splitSign i (E t)
  have size : Fintype.card (Core m)+2=Fintype.card F+1 := by
    have d := Fintype.card_congr E
    simpa only [Index,Fintype.card_sum,Fintype.card_bool,Fintype.card_option] using d
  have wn : w≠0 := by intro h; subst w; simp at hw
  have xn (k : Fin m) : (e k).val≠0 := by
    intro eq; have h := (e k).property; rw [eq] at h; norm_num at h
  have colour (a : Bool) (k : Fin m) : g (bulk a k)=(if a then !i else i) := by
    cases a <;> cases i <;> simp only [g,E,chart_apply,fieldPoint,splitSign,
      ite_eq_right (xn k),ite_eq_right (mul_ne_zero wn (xn k)),map_mul,hw,(e k).property,cosetSign] <;> decide
  have endColour (b : Bool) : g (rim b)= !b := by
    cases b <;> simp [g,E,fieldPoint,splitSign]
  have gram (u v : Index m) : (N*N.transpose) u v =
      if u=v then (Fintype.card F:ℝ)+1 else (bit (g u)+bit (g v))*realPaley (E u) (E v) := by
    have re : (N*N.transpose) u v=(reference (F:=F) i*(reference (F:=F) i).transpose) (E u) (E v) :=
      E.sum_comp (fun t ↦ reference i (E u) t*reference i (E v) t)
    rw [re,reference_gram hc q4]
    simp only [E.injective.eq_iff,bit,g,signInt,Int.cast_ite,Int.cast_neg,Int.cast_one]
  have off (u v : Index m) (ne : u≠v) : realPaley (E u) (E v)=1 ∨ realPaley (E u) (E v)= -1 := by
    rcases (HadamardMod.TorusFrobenius.conference (F:=F) hc).sign (E u) (E v) (E.injective.ne ne) with h|h
    · left; unfold realPaley; exact_mod_cast h
    · right; unfold realPaley; exact_mod_cast h
  let pn : Partition (N*N.transpose) := {
    part := g
    count := by
      intro b
      simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool]
      change (∑ k,if g (bulk true k)=b then 1 else 0)+(∑ k,if g (bulk false k)=b then 1 else 0)+
        ((if g (rim true)=b then 1 else 0)+(if g (rim false)=b then 1 else 0))=_
      simp only [colour,endColour]
      cases i <;> cases b <;> simp
    inside := by
      intro u v ne eq
      rw [gram,ite_eq_right ne,eq]
      rcases off u v ne with h|h <;> cases a : g v <;> norm_num [bit,h]
    outside := by
      intro u v ne
      have diff : u≠v := fun eq ↦ ne (congrArg g eq)
      rw [gram,ite_eq_right diff]
      cases a : g u <;> cases b : g v <;> simp_all [bit] }
  have within (a : Bool) (k l : Fin m) : realPaley (E (bulk a k)) (E (bulk a l)) =
      (if a then (-1:ℝ) else 1)*(quadraticChar F ((e l).val-(e k).val):ℝ) := by
    cases a <;> simp [E,fieldPoint,realPaley,HadamardMod.TorusFrobenius.entry,←mul_sub,map_mul,hw]
  have mixed (a : Bool) (k l : Fin m) (b : Bool) : realPaley (E (bulk a k)) (E (rim b))=
      realPaley (E (bulk a l)) (E (rim b)) := by
    have neg (t : F) : 0-t=(-1)*t := by ring
    cases a <;> cases b <;> simp only [E,chart_apply,fieldPoint,realPaley,HadamardMod.TorusFrobenius.entry,
      neg,map_mul,hw,(e k).property,(e l).property]
  have matchGram (a : Bool) (k l : Fin m) :
      (bordered A T L H*(bordered A T L H).transpose) (bulk a k) (bulk a l)=(N*N.transpose) (bulk a k) (bulk a l) := by
    rw [bulk_gram A T L H ht,blocks,incidence_gram hc q4 hw (e k).property (e l).property,gram]
    by_cases eq : k=l
    · subst l; simp; ring
    · have diff : (e k).val≠(e l).val := fun h ↦ eq (eq_of_coords e h)
      have separate : bulk a k≠bulk a l := by simpa [bulk] using eq
      rw [ite_eq_right diff,ite_eq_right separate,colour,colour,within]
      cases a <;> cases i <;> push_cast <;> norm_num [bit,cosetSign] <;> ring
  have same : |(bordered A T L H).det|=|N.det| := by
    apply abs_det_of_border_blocks hm _ _ pm pn
    · intro a k l ne
      rw [matchGram,gram,ite_eq_right (show bulk a k≠bulk a l by simpa [bulk] using ne),colour,colour]
      have obs := off (bulk a k) (bulk a l) (by simpa [bulk] using ne)
      rcases obs with h|h <;> cases a <;> cases i <;> norm_num [bit,h]
    · exact matchGram
    · exact mixed_gram A T L H reg
    · intro a k l b
      rw [gram,gram,ite_eq_right (by simp [bulk,rim]),ite_eq_right (by simp [bulk,rim]),colour,colour,mixed a k l b]
    · intro b t
      rw [rim_norm A T L H hl hh,gram,ite_eq_left rfl]
      exact_mod_cast size
  simpa only [N,det_submatrix_equiv_self] using same

#print axioms compare_incidence_border


/-- Signed sequences on the two chosen translated sets, listed in a cyclic
enumeration of the nonzero squares. -/
def sourcePair (w : F) (i j : Bool) (e : Fin m ≃ SquareIndex F) : Bool → Fin m → ℝ
  | false,k => (incidence 1 i (e k).val:ℝ)
  | true,k => (incidence w j (e k).val:ℝ)

private theorem sum_by_coords (e : Fin m ≃ SquareIndex F) (f : F → ℤ) :
    (∑ k, f (e k).val)=sumSquares f := by
  let S := (univ : Finset F).filter (fun x ↦ quadraticChar F x=1)
  have memS (x : F) : x∈S ↔ quadraticChar F x=1 := by simp [S]
  calc
    _ = ∑ x : SquareIndex F, f x.val := e.sum_comp (fun x ↦ f x.val)
    _ = ∑ x ∈ S, f x := (sum_subtype S memS f).symm
    _ = _ := by simp only [S,sum_filter,sumSquares]


/-- Exact sums of the two signed support rows in a cyclic enumeration. -/
theorem source_pair_sums (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (w : F) (hw : quadraticChar F w= -1) (i j : Bool) (e : Fin m ≃ SquareIndex F) :
    (∑ t, sourcePair w i j e false t)=(if i then 0 else -2) ∧
      (∑ t, sourcePair w i j e true t)=0 := by
  obtain ⟨a,b⟩ := incidence_sums hc q4 hw i j
  simp only [sourcePair,←Int.cast_sum,sum_by_coords e,a,b,Int.cast_zero,and_true]
  cases i <;> norm_num [cosetSign]

#print axioms source_pair_sums

theorem source_layout_gram [NeZero m] (w : F) (i j : Bool) (e : Fin m ≃ SquareIndex F)
    (cyc : ∀ k l, (e (k-l)).val=(e k).val/(e l).val) (u : CyclicLayout m)
    (a : Bool) (k l : Fin m) :
    let A := u.core (sourcePair w i j e)
    (A*A.transpose) (a,k) (a,l)=(incidenceGram w i j (e k).val (e l).val:ℝ) := by
  dsimp only
  rw [u.gram,Fintype.sum_bool]
  unfold sourcePair
  simp only [correlation,cyc]
  unfold incidenceGram
  rw [←sum_by_coords e,←sum_by_coords e]
  push_cast
  abel

theorem compare_source_layout [NeZero m] (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (hm : 2 ≤ m) (w : F) (hw : quadraticChar F w= -1) (e : Fin m ≃ SquareIndex F)
    (cyc : ∀ k l, (e (k-l)).val=(e k).val/(e l).val)
    (i j : Bool) (u : CyclicLayout m) (T L H : Matrix Bool Bool ℝ)
    (ht : Signs T) (hl : Signs L) (hh : Signs H)
    (p : Partition (bordered (u.core (sourcePair w i j e)) T L H*
      (bordered (u.core (sourcePair w i j e)) T L H).transpose)) :
    |(bordered (u.core (sourcePair w i j e)) T L H).det|=|(reference (F:=F) i).det| :=
  compare_incidence_border hc q4 hm w hw e i j _ T L H ht hl hh (u.regular _)
    (source_layout_gram w i j e cyc u) p

#print axioms source_layout_gram
#print axioms compare_source_layout


private def squareUnits (F : Type) [Field F] [Fintype F] [DecidableEq F] : Subgroup Fˣ where
  carrier := {x | quadraticChar F (x:F)=1}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change quadraticChar F ((x:F)*(y:F))=1
    rw [map_mul,hx,hy,one_mul]
  inv_mem' := by
    intro x hx
    have h := congrArg (quadraticChar F) (show (x:F)*((x⁻¹:Fˣ):F)=1 by simp)
    rw [map_mul,show quadraticChar F (x:F)=1 from hx,one_mul,map_one] at h
    exact h

private def squareUnitEquiv : squareUnits F ≃ SquareIndex F where
  toFun x := ⟨(x.val:F),x.property⟩
  invFun x := ⟨Units.mk0 x.val (by intro h; have t:=x.property; rw [h] at t; norm_num at t),x.property⟩
  left_inv _ := Subtype.ext (Units.ext rfl)
  right_inv _ := rfl

theorem square_index_card (w : F) (hw : quadraticChar F w= -1) :
    Fintype.card (SquareIndex F)=(Fintype.card F-1)/2 := by
  let e := (Fintype.equivFin (SquareIndex F)).symm
  have q := Fintype.card_congr (chart w hw e)
  simp only [Index,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Fintype.card_option] at q
  omega

/-- The required cyclic ordering of the squares exists for every finite field
and the corresponding positive length. -/
theorem exists_square_enumeration {n : ℕ} (card : Fintype.card (SquareIndex F)=n+1) :
    ∃ e : Fin (n+1) ≃ SquareIndex F, ∀ k l, (e (k-l)).val=(e k).val/(e l).val := by
  let S := squareUnits F
  have cardS : Nat.card S=n+1 :=
    (Nat.card_congr (squareUnitEquiv (F:=F))).trans ((Nat.card_eq_fintype_card).trans card)
  have cyc := zmodCyclicMulEquiv (G:=S) (inferInstance : IsCyclic S)
  rw [cardS] at cyc
  let a : Multiplicative (ZMod (n+1)) ≃* S := cyc
  let z := ZMod.finEquiv (n+1)
  let f : Fin (n+1) ≃ SquareIndex F := z.toEquiv.trans ((Multiplicative.ofAdd (α:=ZMod (n+1))).trans
    (a.toEquiv.trans (squareUnitEquiv (F:=F))))
  refine ⟨f,?_⟩
  intro k l
  have mp := a.map_div (Multiplicative.ofAdd (z k)) (Multiplicative.ofAdd (z l))
  have md := congrArg (fun s : S ↦ ((s.val:Fˣ):F)) mp
  change ((a (Multiplicative.ofAdd (z (k-l)))).val:F)=
    ((a (Multiplicative.ofAdd (z k))).val:F)/((a (Multiplicative.ofAdd (z l))).val:F)
  rw [map_sub,ofAdd_sub]
  simpa only [Subgroup.coe_div,Units.val_div_eq_div_val] using md

#print axioms exists_square_enumeration

end Hadamard.MSXCore
