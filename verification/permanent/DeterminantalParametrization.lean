import DeterminantalHeight
import Mathlib.LinearAlgebra.Matrix.Rank

/-! A polynomial parametrization of square matrices with two dependent
rows, together with the height of a point whose final two rows vanish. -/

noncomputable section
namespace DeterminantalRegularity
namespace RankParam
open MvPolynomial Matrix Finset

abbrev Slot (H : Type*) := H ⊕ Fin 2
abbrev Key (U H : Type*) := (Fin 2 × H) ⊕ ((H × Slot H) ⊕ U)
abbrev Gen (U H : Type*) := U ⊕ (Slot H × Slot H)
abbrev Poly (K U H : Type*) [Field K] := MvPolynomial (Key U H) K

variable (K : Type*) [Field K] (U H : Type*) [Fintype H]

def topRows : Matrix H (Slot H) (Poly K U H) :=
  Matrix.of (fun i j ↦ X (.inr (.inl (i,j))))

def coeffRows : Matrix (Fin 2) H (Poly K U H) :=
  Matrix.of (fun b i ↦ X (.inl (b,i)))

def raw : Matrix (Slot H) (Slot H) (Poly K U H) :=
  Matrix.of (fun r j ↦ Sum.elim (fun i ↦ topRows K U H i j)
    (fun b ↦ ∑ i, coeffRows K U H b i * topRows K U H i j) r)

def paramMap : MvPolynomial (Gen U H) K →+* Poly K U H :=
  eval₂Hom C (Sum.elim (fun u ↦ X (.inr (.inr u))) (fun ij ↦ raw K U H ij.1 ij.2))

abbrev Coord := (paramMap K U H).range
def pull : MvPolynomial (Gen U H) K →+* Coord K U H := (paramMap K U H).rangeRestrict
def incl : Coord K U H →+* Poly K U H := (paramMap K U H).range.subtype
def ground : K →+* Coord K U H := (pull K U H).comp C
def input (u : U) : Coord K U H := pull K U H (X (.inl u))
def entry : Matrix (Slot H) (Slot H) (Coord K U H) :=
  Matrix.of (fun i j ↦ pull K U H (X (.inr (i,j))))

@[simp] theorem incl_ground (k : K) : incl K U H (ground K U H k) = C k := by
  change paramMap K U H (C k) = _
  simp [paramMap]

@[simp] theorem incl_input (u : U) : incl K U H (input K U H u) = X (.inr (.inr u)) := by
  change paramMap K U H (X (.inl u)) = _
  simp [paramMap]

@[simp] theorem incl_entry (i j : Slot H) : incl K U H (entry K U H i j) = raw K U H i j := by
  change paramMap K U H (X (.inr (i,j))) = _
  simp [paramMap]

def origin (A : Matrix H (Slot H) K) : Key U H → K :=
  Sum.elim (fun _ ↦ 0) (Sum.elim (fun ij ↦ A ij.1 ij.2) (fun _ ↦ 0))

variable [DecidableEq H] [Fintype U] [DecidableEq U]

instance : IsNoetherianRing (Coord K U H) :=
  isNoetherianRing_of_surjective _ _ (pull K U H) (paramMap K U H).rangeRestrict_surjective

def originPrime (A : Matrix H (Slot H) K) : Ideal (Coord K U H) :=
  pointPrime (incl K U H) (origin K U H A) univ

private def early : Finset (Key U H) := univ.filter (fun k ↦ k.isLeft = true)
private def core : Matrix H H (Poly K U H) := (topRows K U H).submatrix id Sum.inl

omit [Fintype U] [DecidableEq U] in
private theorem core_ne_zero : (core K U H).det ≠ 0 := by
  let test : Key U H → K := Sum.elim (fun _ ↦ 0)
    (Sum.elim (fun ij ↦ Sum.elim (fun h ↦ if ij.1 = h then 1 else 0) (fun _ ↦ 0) ij.2) (fun _ ↦ 0))
  have eq : (MvPolynomial.eval test).mapMatrix (core K U H) = 1 := by
    ext i j
    simp [core,topRows,test,Matrix.one_apply]
  intro hz
  have fail := congrArg (MvPolynomial.eval test) hz
  rw [RingHom.map_det,eq,Matrix.det_one,map_zero] at fail
  exact one_ne_zero fail

private theorem survives (A : Matrix H (Slot H) K) (s : Finset (Key U H)) (hs : s ⊆ early U H) :
    specialize (origin K U H A) s (core K U H).det ≠ 0 := by
  have eq : (specialize (origin K U H A) s).mapMatrix (core K U H) = core K U H := by
    ext i j
    have out : (Sum.inr (.inl (i,Sum.inl j)) : Key U H) ∉ s := by
      intro h; have imp := hs h; simp [early] at imp
    simp [core,topRows,out]
  rw [RingHom.map_det,eq]
  exact core_ne_zero K U H

omit [Fintype U] [DecidableEq U] in
private theorem weighted_coeff (b : Fin 2) (i : H) :
    (core K U H).det * X (.inl (b,i)) ∈ Set.range (incl K U H) := by
  let Q : Matrix H H (Coord K U H) := (entry K U H).submatrix Sum.inl Sum.inl
  let row : H → Coord K U H := fun j ↦ entry K U H (.inr b) (.inl j)
  refine ⟨(Q.updateRow i row).det,?_⟩
  rw [RingHom.map_det]
  have eq : (incl K U H).mapMatrix (Q.updateRow i row) =
      (core K U H).updateRow i (∑ k, coeffRows K U H b k • (core K U H) k) := by
    ext l j
    by_cases h : l = i
    · simp [Matrix.updateRow_apply,h,Q,row,raw,core,Pi.smul_apply,Finset.sum_apply]
    · simp [Matrix.updateRow_apply,h,Q,raw,core]
  rw [eq,Matrix.det_updateRow_sum]
  simp [coeffRows,mul_comm]

/-- The local height is at least the number of top entries, row coefficients
and independent input parameters, even when the top matrix specializes
to a matrix of smaller rank. -/
theorem origin_height (A : Matrix H (Slot H) K) :
    (Fintype.card (Key U H) : ℕ∞) ≤ (originPrime K U H A).height := by
  apply height_of_parameters (incl K U H) (origin K U H A) (early U H) (core K U H).det
  · exact survives K U H A
  · intro v hv
    cases v with
    | inl bc => simpa [origin] using weighted_coeff K U H bc.1 bc.2
    | inr z => simp [early] at hv
  · intro v hv
    cases v with
    | inl bc => simp [early] at hv
    | inr z =>
      cases z with
      | inl ij =>
        refine ⟨entry K U H (.inl ij.1) ij.2 - ground K U H (A ij.1 ij.2),?_⟩
        simp [raw,topRows,origin]
      | inr u =>
        refine ⟨input K U H u,?_⟩
        simp [origin]

#print axioms origin_height
end RankParam
end DeterminantalRegularity
