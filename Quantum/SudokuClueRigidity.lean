module
public import Quantum.SudokuClassicalLocus
public import Quantum.SudokuTradeResult

/-! With a uniquely determined classical solution at most one symbol is absent
from the clues. A common unitary taking its coordinate completion to another
solution cannot mix any two coordinates. -/
@[expose] public section
noncomputable section
namespace SudokuLocus
open Function QuantumSudoku PartialSudoku FractionalLayouts SudokuEmbedding

variable {n : ℕ} [NeZero n] {p : Puzzle n}

def Printed (p : Puzzle n) (i : Sites n) : Prop := ∃ r c,p r c=some i

theorem one_absent {f : Solution n} (hc : ClassicalCompletes p f)
    (unique : ∀ g,ClassicalCompletes p g → g=f) {a b : Sites n} (ne : a≠b) :
    Printed p a ∨ Printed p b := by
  classical
  by_contra! missing
  let s := Equiv.swap a b
  let g : Solution n := fun r c => s (f r c)
  have ok : ClassicalCompletes p g := by
    refine ⟨fun d k => s.bijective.comp (hc.1 d k),?_⟩
    intro r c j clue
    change s (f r c)=j
    rw [hc.2 r c j clue]
    exact Equiv.swap_apply_of_ne_of_ne (fun hj => missing.1 ⟨r,c,hj ▸ clue⟩)
      (fun hj => missing.2 ⟨r,c,hj ▸ clue⟩)
  obtain ⟨c,member⟩ := (hc.1 .row 0).surjective a
  change f 0 c=a at member
  have eq := congrArg (fun x : Solution n => x 0 c) (unique g ok)
  change s (f 0 c)=f 0 c at eq
  simpa [member,s,ne.symm] using eq

private theorem printed_image {f : Solution n} {v : Grid (Fin n)} (hf : ClassicalCompletes p f)
    (hv : QuantumCompletes p v) {U : H (Fin n) ≃ₗᵢ[ℂ] H (Fin n)}
    (rel : ∀ r c,∃ z : Circle, U (classicalBoard f r c)=(z:ℂ) • v r c) {i : Sites n} (h : Printed p i) :
    ∃ z : Circle,U (unitAxis i)=(z:ℂ) • unitAxis i := by
  obtain ⟨r,c,clue⟩:=h
  obtain ⟨z,hz⟩:=rel r c
  obtain ⟨w,hw⟩:=hv.2 r c i clue
  change U (unitAxis (f r c))=_ at hz
  exact ⟨z*w,by simpa [hf.2 r c i clue,hw,smul_smul] using hz⟩

private theorem printed_excludes_second {f : Solution n} {v : Grid (Fin n)}
    (hf : ClassicalCompletes p f) (hv : QuantumCompletes p v)
    {U : H (Fin n) ≃ₗᵢ[ℂ] H (Fin n)}
    (rel : ∀ r c,∃ z : Circle,U (classicalBoard f r c)=(z:ℂ) • v r c)
    {r c i j : Sites n} (hi : Printed p i) (coord : v r c i≠0) (ne : i≠j) : v r c j=0 := by
  obtain ⟨a,ha⟩:=printed_image hf hv rel hi
  obtain ⟨z,hz⟩:=rel r c
  change U (unitAxis (f r c))=(z:ℂ) • v r c at hz
  by_cases e : i=f r c
  · rw [←e,ha] at hz
    have vj:=congrArg (fun y : H (Fin n) => y j) hz
    simpa [unitAxis,PiLp.single_apply,ne.symm,Circle.coe_ne_zero] using vj.symm
  · have orth:=U.inner_map_map (unitAxis i) (unitAxis (f r c))
    rw [ha,hz,inner_smul_left,inner_smul_right,axis_inner,ite_eq_right e] at orth
    simp [unitAxis,EuclideanSpace.inner_single_left,Circle.coe_ne_zero,coord] at orth

theorem mixed_inequivalent {f : Solution n} {v : Grid (Fin n)} (hf : ClassicalCompletes p f)
    (unique : ∀ g,ClassicalCompletes p g → g=f) (hv : QuantumCompletes p v) (mixed : Mixed v) :
    ¬Equivalent (classicalBoard f) v := by
  rintro ⟨U,rel⟩
  obtain ⟨r,c,a,b,ne,ha,hb⟩:=mixed
  rcases one_absent hf unique ne with left | right
  · exact hb (printed_excludes_second hf hv rel left ha ne)
  · exact ha (printed_excludes_second hf hv rel right hb ne.symm)

theorem unique_dichotomy (one : ∃! f,ClassicalCompletes p f) :
    Subsingleton (QSolutions p) ∨
      ((∃ v w : Grid (Fin n),QuantumCompletes p v ∧ QuantumCompletes p w ∧ ¬Equivalent v w) ∧
        Nonempty (Circle ↪ QSolutions p)) := by
  classical
  obtain ⟨f,hf,unique⟩:=one
  by_cases mixed : ∃ v : Grid (Fin n),QuantumCompletes p v ∧ Mixed v
  · obtain ⟨v,hv,hm⟩:=mixed
    refine Or.inr ⟨⟨_,v,classical_quantum hf,hv,mixed_inequivalent hf unique hv hm⟩,?_⟩
    obtain ⟨r,c,a,b,ne,ha,hb⟩:=hm
    exact ⟨SudokuContinuum.circleEmbedding hv ne ha hb⟩
  · left
    have collapse (q : QSolutions p) : q=classicalEmbedding p ⟨f,hf⟩ := by
      obtain ⟨⟨v,h⟩,rfl⟩:=Quotient.exists_rep q
      obtain ⟨g,hg,phase⟩:=coordinates_of_not_mixed h (fun m => mixed ⟨v,h,m⟩)
      obtain rfl := unique g hg
      exact Quotient.sound phase
    exact ⟨fun u v => (collapse u).trans (collapse v).symm⟩

theorem many_iff_inequivalent : SudokuTrade.UniqueMany n ↔ SudokuTrade.UniqueQuantumCounterexample n := by
  constructor
  · rintro ⟨p,one,⟨emb⟩⟩
    rcases unique_dichotomy one with single | both
    · have eq : (1:Circle)= -1 := emb.injective (single.elim _ _)
      have bad:=congrArg (fun x : Circle => (x:ℂ)) eq
      norm_num at bad
    · exact ⟨p,one,both⟩
  · exact SudokuTrade.UniqueQuantumCounterexample.many

#print axioms one_absent
#print axioms unique_dichotomy
#print axioms many_iff_inequivalent
end SudokuLocus
