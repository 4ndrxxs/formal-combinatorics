import PermanentIsotropicColumns
import PermanentSymmetry

/-! Complementary two-by-two permanents give every entry of the order-four
Hessian. Finite multiset identities certify the underlying monomials before
evaluation over an arbitrary field. -/
noncomputable section
open Matrix Equiv Finset PermanentFive QuinticPencil PermanentBorder
namespace PermanentOrderFour
abbrev F := Fin 4
abbrev Cell4 := F × F
abbrev Terms := Multiset (Multiset Cell4)
variable {K : Type*} [Field K]
def evalTerms (z : Cell4 → K) (s : Terms) : K :=
  (s.map fun w ↦ (w.map z).prod).sum
def term (p : Perm F) (s : Finset F) : Multiset Cell4 :=
  s.val.map fun j ↦ (p j,j)
def terms₂ (e f : Cell4) : Terms :=
  (univ.filter fun p : Perm F ↦ p f.2=f.1 ∧ e.2≠f.2 ∧ p e.2=e.1).val.map
    fun p ↦ term p ((univ.erase f.2).erase e.2)
def terms₁ (e : Cell4) : Terms :=
  (univ.filter fun p : Perm F ↦ p e.2=e.1).val.map fun p ↦ term p (univ.erase e.2)
def terms₀ : Terms := (univ : Finset (Perm F)).val.map fun p ↦ term p univ

private theorem eval_second (z : Cell4 → K) (e f : Cell4) :
    evalTerms z (terms₂ e f)=secondAt z e f := by
  rw [secondAt,←Finset.sum_filter]
  simp [evalTerms,terms₂,term,Finset.sum,Finset.prod]
private theorem eval_first (z : Cell4 → K) (e : Cell4) :
    evalTerms z (terms₁ e)=gradAt z e := by
  rw [gradAt,←Finset.sum_filter]
  simp [evalTerms,terms₁,term,Finset.sum,Finset.prod]
private theorem eval_per (z : Cell4 → K) : evalTerms z terms₀=PermanentBorder.value z := by
  have h : PermanentBorder.value z=∑ p : Perm F, ∏ j : F, z (p j,j) := by
    simp [PermanentBorder.value,per,Matrix.permanent,PermanentCuts.generic]
  rw [h]
  simp only [evalTerms,terms₀,term,Finset.sum,Finset.prod,Multiset.map_map,Function.comp_def]

def otherTwo (a b : F) : F × F := ![![(0,0),(2,3),(1,3),(1,2)],![(2,3),(0,0),(0,3),(0,2)],![(1,3),(0,3),(0,0),(0,1)],![(1,2),(0,2),(0,1),(0,0)]] a b
def otherThree (a : F) : F × F × F := ![(1,2,3),(0,2,3),(0,1,3),(0,1,2)] a
def words₂ (z t i j : F) : Terms :=
  {{(z,i),(t,j)},{(z,j),(t,i)}}
def words₃ (r s t i j k : F) : Terms :=
  {{(r,i),(s,j),(t,k)}, {(r,i),(s,k),(t,j)}, {(r,j),(s,i),(t,k)},
   {(r,j),(s,k),(t,i)}, {(r,k),(s,i),(t,j)}, {(r,k),(s,j),(t,i)}}
def pairs (e f : Cell4) : Terms :=
  if e.1=f.1 ∨ e.2=f.2 then 0 else
  let r := otherTwo e.1 f.1
  let c := otherTwo e.2 f.2
  words₂ r.1 r.2 c.1 c.2
def triples (e : Cell4) : Terms :=
  let r := otherThree e.1
  let c := otherThree e.2
  words₃ r.1 r.2.1 r.2.2 c.1 c.2.1 c.2.2
def quartics : Terms := ((univ : Finset F).val.map fun j ↦
  (triples (3,j)).map fun w ↦ (3,j) ::ₘ w).join

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem pair_certificate : ∀ e f : Cell4, terms₂ e f=pairs e f := by decide +kernel
set_option maxRecDepth 20000 in
private theorem triple_certificate : ∀ e : Cell4, terms₁ e=triples e := by decide +kernel
set_option maxRecDepth 20000 in
private theorem quartic_certificate : terms₀=quartics := by decide +kernel

def two (z : Cell4 → K) (r s i j : F) : K := z (r,i)*z (s,j)+z (r,j)*z (s,i)
def three (z : Cell4 → K) (r s t i j k : F) : K :=
 z (r,i)*z (s,j)*z (t,k)+z (r,i)*z (s,k)*z (t,j)+z (r,j)*z (s,i)*z (t,k)+
 z (r,j)*z (s,k)*z (t,i)+z (r,k)*z (s,i)*z (t,j)+z (r,k)*z (s,j)*z (t,i)
def H (z : Cell4 → K) : Matrix Cell4 Cell4 K := Matrix.of fun e f ↦
  if e.1=f.1 ∨ e.2=f.2 then 0 else
  let r := otherTwo e.1 f.1
  let c := otherTwo e.2 f.2
  two z r.1 r.2 c.1 c.2
def grad (z : Cell4 → K) (e : Cell4) : K :=
  let r := otherThree e.1
  let c := otherThree e.2
  three z r.1 r.2.1 r.2.2 c.1 c.2.1 c.2.2

theorem hess_eq (z : Cell4 → K) : hessian (per K F) z=H z := by
  ext e f
  rw [second_formula,←eval_second,pair_certificate]
  by_cases h : e.1=f.1 ∨ e.2=f.2
  · simp [H,pairs,h,evalTerms]
  · simp [H,pairs,h,evalTerms,words₂,two]
theorem grad_eq (z : Cell4 → K) (e : Cell4) : gradAt z e=grad z e := by
  rw [←eval_first,triple_certificate]
  simp [grad,triples,evalTerms,words₃,three]
  ring
theorem value_eq (z : Cell4 → K) : PermanentBorder.value z = ∑ j : F, z (3,j)*grad z (3,j) := by
  rw [←eval_per,quartic_certificate]
  have sub (j : F) : evalTerms z (triples (3,j))=grad z (3,j) := by
    rw [←triple_certificate,eval_first,grad_eq]
  simp only [←sub,quartics,evalTerms,Multiset.map_join,Multiset.sum_join,Multiset.map_map,
    Finset.sum,Function.comp_apply]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro j _
  rw [←Multiset.sum_map_mul_left]
  simp

#print axioms hess_eq
#print axioms value_eq
end PermanentOrderFour
