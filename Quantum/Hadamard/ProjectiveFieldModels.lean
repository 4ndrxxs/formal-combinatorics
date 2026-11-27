import Quantum.Hadamard.ProjectiveQuadraticOrbits
import Quantum.Hadamard.ConferenceBitCompletion

/-! A finite-field model yields a certificate for every isomorphic field.
The finite comparison checks the original Paley entries and the canonical
diagonal signs before transferring an already verified determinant. -/

noncomputable section
open Finset Matrix
namespace Hadamard.ProjectiveSigning
open Hadamard.BitTrace

variable {F E : Type} [Field F] [Field E] [Fintype F] [Fintype E] [DecidableEq F] [DecidableEq E]

def fourFifths (q : ℕ) : ℝ := (4/5:ℝ)*((2*(q:ℝ))*((q:ℝ)-1)^(q/2))

def CertifiedPatterns (F : Type) [Field F] [Fintype F] [DecidableEq F] : Prop :=
  ∃ d : F, quadraticChar F d= -1 ∧ ∀ pat : Pattern, fourFifths (Fintype.card F) ≤ signedDet (pat.sign d)

theorem character_by_squares (c : F→ℤ) (zero : c 0=0)
    (range : ∀u, u≠0 → c u=1 ∨ c u= -1)
    (square : ∀u, u≠0 → (c u=1 ↔ ∃v:F, u=v*v)) :
    ∀ u, c u=quadraticChar F u := by
  intro u
  by_cases h : u=0
  · simpa [h] using zero
  rcases range u h with plus|minus
  · exact plus.trans ((quadraticChar_one_iff_isSquare h).mpr ((square u h).mp plus)).symm
  · have ns : ¬IsSquare u := by
      intro sq
      have p := (square u h).mpr sq
      omega
    exact minus.trans (quadraticChar_neg_one_iff_not_isSquare.mpr ns).symm

theorem char_equiv (e : F ≃+* E) (u : F) : quadraticChar E (e u)=quadraticChar F u := by
  by_cases h : u=0
  · simp [h]
  have nz : e u≠0 := (map_ne_zero_iff e e.injective).mpr h
  have sq : IsSquare (e u) ↔ IsSquare u :=
    ⟨fun hs ↦ by simpa using hs.map e.symm.toMonoidHom,fun hs ↦ hs.map e.toMonoidHom⟩
  by_cases hs : IsSquare u
  · rw [(quadraticChar_one_iff_isSquare nz).mpr (sq.mpr hs),(quadraticChar_one_iff_isSquare h).mpr hs]
  · rw [quadraticChar_neg_one_iff_not_isSquare.mpr (mt sq.mp hs),quadraticChar_neg_one_iff_not_isSquare.mpr hs]

private theorem charFun_equiv (e : F ≃+* E) (u : F) : quadraticCharFun E (e u)=quadraticCharFun F u :=
  char_equiv e u

private theorem bits_equiv (e : F ≃+* E) (d : F) (pat : Pattern) (i : Option F) :
    pat.sign (e d) (e.toEquiv.optionCongr i)=pat.sign d i := by
  cases pat <;> cases i <;> simp [Pattern.sign,Pattern.read,quadraticValue,←map_pow,←map_neg,
    ←map_add,charFun_equiv]

theorem signedDet_equiv (e : F ≃+* E) (d : F) (pat : Pattern) :
    signedDet (pat.sign d)=signedDet (pat.sign (e d)) := by
  let f := e.toEquiv.optionCongr
  have cp (i j : Option F) : realPaley (f i) (f j)=realPaley i j := by
    cases i <;> cases j <;> simp [f,realPaley,HadamardMod.TorusFrobenius.entry,←map_sub,charFun_equiv]
  have eqn : (realPaley (F:=E)+diagonal (fun j ↦ (pat.sign (e d) j:ℝ))).submatrix f f =
      realPaley (F:=F)+diagonal (fun j ↦ (pat.sign d j:ℝ)) := by
    ext i j
    simp only [Matrix.submatrix_apply,Matrix.add_apply,Matrix.diagonal_apply,Equiv.apply_eq_iff_eq,cp]
    rw [show pat.sign (e d) (f i)=pat.sign d i from bits_equiv e d pat i]
  unfold signedDet
  rw [←eqn,det_submatrix_equiv_self]

theorem certified_of_card (card : Fintype.card F=Fintype.card E) (model : CertifiedPatterns E) :
    CertifiedPatterns F := by
  let e : E ≃+* F := FiniteField.ringEquivOfCardEq card.symm
  obtain ⟨d,hd,all⟩ := model
  refine ⟨e d,(char_equiv e d).trans hd,fun pat ↦ ?_⟩
  rw [card,←signedDet_equiv e d pat]
  exact all pat

/-- Assemble closed arithmetic checks, one numbered field element at a time. -/
theorem extend_check {n : ℕ} {P : ℕ→Prop} (earlier : ∀i<n,P i) (last : P n) : ∀i<n+1,P i := by
  intro i hi
  by_cases h : i=n
  · simpa [h] using last
  · exact earlier i (by omega)

/-- Number the field elements first and infinity last. -/
def chart {q : ℕ} (e : Fin q ≃ F) : Fin (q+1) ≃ Option F :=
  finSuccEquivLast.trans e.optionCongr

def tableEntry (c : F→ℤ) : Option F → Option F → ℤ
  | none,none => 0
  | some _,none | none,some _ => 1
  | some i,some j => c (j-i)

/-- Literal equality of the full, field-indexed determinant with the determinant
stored in a bit certificate. The two verification hypotheses use finite arithmetic. -/
theorem determinant_from_table {q v : ℕ} (num : Fin q ≃ F) (c : F→ℤ)
    (correct : ∀u, c u=quadraticChar F u) (data : Fin (q+1)→ℕ)
    (rows : ∀i j, tableEntry c (chart num i) (chart num j) =
       sign (data i) j.val - (if i=j then 1 else 0 : ℤ))
    (d : F) (p : Pattern) (index : Fin v ⊕ Fin v ≃ Fin (q+1))
    (diags : ∀i, p.read c d (chart num (index i))=Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i) :
    signedDet (p.sign d)=|(orderedWordBlock data index+
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  let g := index.trans (chart num)
  have chars : c=fun u ↦ quadraticChar F u := funext correct
  have cp (i j : Fin (q+1)) : realPaley (chart num i) (chart num j)=realWordBlock data i j := by
    have h := rows i j
    rw [chars] at h
    change HadamardMod.TorusFrobenius.entry (chart num i) (chart num j)=_ at h
    simp only [realPaley,realWordBlock, Matrix.map_apply, Matrix.sub_apply,Matrix.one_apply,wordMatrix]
    exact congrArg (fun z : ℤ ↦ (z:ℝ)) h
  have sd (i : Fin v ⊕ Fin v) : (p.sign d (g i):ℝ)=Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1) i := by
    have h := diags i
    rw [chars] at h
    change p.sign d (g i)=_ at h
    cases i <;> dsimp at h ⊢ <;> exact_mod_cast h
  have mat : (realPaley+diagonal (fun i ↦ (p.sign d i:ℝ))).submatrix g g =
      orderedWordBlock data index+Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1)) := by
    ext i j
    simp only [Matrix.submatrix_apply,Matrix.add_apply,Matrix.diagonal_apply,Equiv.apply_eq_iff_eq,sd]
    rw [show realPaley (g i) (g j)=orderedWordBlock data index i j from cp _ _]
  unfold signedDet
  rw [←det_submatrix_equiv_self g,mat]

/-- Transfer from the six canonical signings to every resolved quadratic signing. -/
theorem quadratic_of_certified (model : CertifiedPatterns F) (hc : ringChar F≠2)
    (q4 : Fintype.card F%4=1) (a b c : F) (disc : b^2-4*a*c≠0)
    (s : Option F→Bool) (w : ℤ) (hw : w^2=1)
    (agree : ∀ i, quadraticValue a b c i≠0 → signOf (s i)=w*quadraticChar F (quadraticValue a b c i))
    (ties : (∑ i, if quadraticValue a b c i=0 then signOf (s i) else 0)=0) :
    fourFifths (Fintype.card F) ≤ signedDet (fun i ↦ signOf (s i)) := by
  obtain ⟨d,hd,all⟩ := model
  have two : (2:F)≠0 := fun h ↦ hc (CharP.ringChar_of_prime_eq_zero Nat.prime_two h)
  have hm : quadraticChar F (-1)=1 := (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr
    (FiniteField.isSquare_neg_one_iff.mpr (by omega))
  have unit (i) : (signOf (s i))^2=1 := by cases s i <;> decide
  obtain ⟨pat,eq⟩ := quadratic_det_six two hm d hd a b c disc _ w hw unit agree ties
  rw [eq]; exact all pat

#print axioms certified_of_card
#print axioms determinant_from_table
#print axioms quadratic_of_certified
end Hadamard.ProjectiveSigning
