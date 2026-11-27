import Quantum.Hadamard.ConferenceCubicMatrix
import Quantum.Hadamard.ProjectiveQuadraticBalance
import Quantum.Hadamard.TorusFrobeniusPaley

/-! The uniform determinant theorem on the original finite-field coordinates.
The diagonal signs are specified by an actual nonsingular binary quadratic
form and its values at the projective points, with opposite signs at its roots. -/

noncomputable section
open Finset Matrix
open scoped BigOperators
open Hadamard.DeterminantRatio

namespace Hadamard.ProjectiveSigning

theorem balanced_signs_on_indices {I : Type*} [Fintype I] [DecidableEq I]
    (C : Matrix I I ℝ) (s : I → Bool) (k : ℕ)
    (size : Fintype.card I = 2*(k+1)) (positive : (univ.filter (fun i ↦ s i=true)).card=k+1)
    (large : 169≤2*(k:ℝ)+1) (hc : C.IsHermitian) (square : C*C=(2*(k:ℝ)+1) • 1)
    (diag : ∀ i, C i i=0) (off : ∀ i j, i≠j → C i j^2=1) :
    (4/5:ℝ)*ewBound k ≤ |(C+diagonal (fun i ↦ if s i then (1:ℝ) else -1)).det| := by
  classical
  let p (i : I) := s i=true
  let e := Equiv.sumCompl p
  let B := C.submatrix e e
  let d (i : I) : ℝ := if s i then 1 else -1
  have cp : Fintype.card {i // p i}=k+1 := (Fintype.card_subtype p).trans positive
  have cm : Fintype.card {i // ¬p i}=k+1 := by rw [Fintype.card_subtype_compl,cp,size]; omega
  have sq : B*B=(2*(k:ℝ)+1) • 1 := by
    dsimp [B]; rw [submatrix_mul_equiv,square]
    change (2*(k:ℝ)+1) • ((1 : Matrix I I ℝ).submatrix e e) = _
    rw [submatrix_one_equiv]
  have sg : d ∘ e = completionSign := by
    funext i
    cases i with
    | inl j =>
      change (if p j.val then (1:ℝ) else -1)=1
      simp [j.property]
    | inr j =>
      change (if p j.val then (1:ℝ) else -1)= -1
      simp [j.property]
  have h := balanced_conference_four_fifths_169 k cp cm large (hc.submatrix e) sq
    (fun i ↦ diag (e i)) (fun i j ne ↦ off _ _ (e.injective.ne ne))
  have id : (C+diagonal d).submatrix e e = B+diagonal completionSign := by
    change B+(diagonal d).submatrix e e=B+diagonal completionSign
    rw [submatrix_diagonal_equiv,sg]
  rw [←id, det_submatrix_equiv_self] at h
  exact h

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The real Paley matrix on the affine chart and the point at infinity. -/
def realPaley : Matrix (Option F) (Option F) ℝ := fun x y ↦ (HadamardMod.TorusFrobenius.entry x y : ℤ)

private theorem realPaley_properties (hc : ringChar F≠2) (q4 : Fintype.card F%4=1) :
    (realPaley (F:=F)).IsHermitian ∧ realPaley (F:=F)*realPaley=(Fintype.card F:ℝ) • 1 ∧
    (∀ i, realPaley (F:=F) i i=0) ∧ (∀ i j, i≠j → realPaley (F:=F) i j^2=1) := by
  let P := HadamardMod.TorusFrobenius.conference (F:=F) hc
  have sy := HadamardMod.TorusFrobenius.conference_sym (F:=F) hc (by omega)
  have rs (i j : Option F) : realPaley i j=realPaley j i := by
    dsimp [realPaley]
    exact_mod_cast sy i j
  have zero (i : Option F) : realPaley i i=0 := by
    dsimp [realPaley]
    exact_mod_cast P.diag i
  have sig (i j : Option F) (h : i≠j) : realPaley i j^2=1 := by
    obtain a | a := P.sign i j h
    · have e : realPaley i j=1 := by
        dsimp [realPaley]
        exact_mod_cast a
      rw [e]; norm_num
    · have e : realPaley i j= -1 := by
        dsimp [realPaley]
        exact_mod_cast a
      rw [e]; norm_num
  refine ⟨?_, ?_, zero, sig⟩
  · ext i j
    exact rs j i
  · ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.smul_apply, Matrix.one_apply,smul_eq_mul]
    by_cases ne : i=j
    · subst j
      have val (l : Option F) : realPaley i l * realPaley l i =
          1-(if l=i then 1 else 0 : ℝ) := by
        rw [rs l i,←sq]
        by_cases eq : l=i
        · subst l; simp [zero]
        · simp [eq,sig i l (Ne.symm eq)]
      simp [val,sum_sub_distrib,Fintype.card_option]
    · simp only [ne,ite_false,mul_zero]
      have off := P.off i j ne
      change (∑ l : Option F, (HadamardMod.TorusFrobenius.entry i l : ℤ)*HadamardMod.TorusFrobenius.entry j l)=0 at off
      simp_rw [show ∀ l, realPaley l j=realPaley j l from fun l ↦ rs l j]
      dsimp [realPaley]
      exact_mod_cast off

/-- Uniform four-fifths bound for every nondegenerate projective quadratic
signing of the concrete real Paley matrix as soon as the field has 169 elements. -/
theorem quadratic_paley_four_fifths (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (large : 169≤Fintype.card F) (a b c : F) (disc : b^2-4*a*c≠0)
    (s : Option F→Bool) (orientation : ℤ)
    (agree : ∀ i, quadraticValue a b c i ≠ 0 →
      (if s i then (1:ℤ) else -1)=orientation*quadraticChar F (quadraticValue a b c i))
    (ties : (∑ i : Option F, if quadraticValue a b c i=0 then (if s i then (1:ℤ) else -1) else 0)=0) :
    let q := Fintype.card F
    (4/5:ℝ)*(2*(q:ℝ))*((q:ℝ)-1)^(q/2) ≤
      |(realPaley+diagonal (fun i ↦ if s i then (1:ℝ) else -1)).det| := by
  let k := Fintype.card F / 2
  have kn : 2*k+1 = Fintype.card F := by dsimp [k]; omega
  have kr : 2*(k:ℝ)+1=(Fintype.card F:ℝ) := by exact_mod_cast kn
  have eq := balanced_resolved_quadratic hc a b c disc s orientation agree ties
  obtain ⟨herm,square,diag,off⟩ := realPaley_properties hc q4
  have h := balanced_signs_on_indices realPaley s k (by rw [Fintype.card_option]; omega)
    (by omega) (by rw [kr]; exact_mod_cast large) herm (kr ▸ square) diag off
  have W : ewBound k=(2*(Fintype.card F:ℝ))*((Fintype.card F:ℝ)-1)^k := by
    unfold ewBound
    rw [←kr]
    congr 1 <;> ring
  simpa only [W, k, mul_assoc] using h

#print axioms balanced_signs_on_indices
#print axioms quadratic_paley_four_fifths

end Hadamard.ProjectiveSigning
