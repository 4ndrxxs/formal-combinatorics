module
public import Quantum.FractionalCorrelations

/-! Product observables, common measurement coordinates, and the two-qubit
correlation obstruction. Matrices use the order 00, 01, 10, 11. -/
@[expose] public section
noncomputable section
namespace FractionalTensor
open Complex Matrix FractionalCorrelations
open scoped ComplexConjugate Matrix

abbrev M := Matrix (Fin 4) (Fin 4) ℂ
abbrev V := Fin 4 → ℂ

def ip (f g : V) : ℂ := star f ⬝ᵥ g
def expectation (f : V) (m : M) : ℝ := (ip f (m *ᵥ f)).re

def vertical (a b : ℝ) (z w : ℂ) : M :=
  !![(a:ℂ), 0, z, 0; 0, (b:ℂ), 0, w; conj z, 0, -a, 0; 0, conj w, 0, -b]
def horizontal (a b : ℝ) (z w : ℂ) : M :=
  !![(a:ℂ), z, 0, 0; conj z, -a, 0, 0; 0, 0, (b:ℂ), w; 0, 0, conj w, -b]
def va := vertical 1 1 0 0
def hb := horizontal 1 1 0 0
def lEq (x : ℂ) := vertical 0 0 (conj x) (conj x)
def rEq (x : ℂ) := horizontal 0 0 (conj x) (conj x)

def entry (d : ℝ) (x y : Bool) := if x && y then -d else d

structure PairData (d : ℝ) (A B : Bool → M) where
  state : Bool → V
  orth : ip (state false) (state true)=0
  leftMean : ∀ i x, expectation (state i) (A x)=0
  rightMean : ∀ i y, expectation (state i) (B y)=0
  joint : ∀ i x y, expectation (state i) (A x * B y)=entry d x y

theorem ip_adjoint (T : M) (f g : V) :
    ip (Tᴴ *ᵥ f) g=ip f (T *ᵥ g) := by
  simp [ip,Matrix.star_mulVec,← Matrix.dotProduct_mulVec]

theorem ip_unitary (T : M) (h : T*Tᴴ=1) (f g : V) :
    ip (Tᴴ *ᵥ f) (Tᴴ *ᵥ g)=ip f g := by
  simp [ip_adjoint,Matrix.mulVec_mulVec,h]

theorem expectation_unitary (T : M) (h : T*Tᴴ=1) (f : V) (m : M) :
    expectation (Tᴴ *ᵥ f) (Tᴴ*m*T)=expectation f m := by
  unfold expectation
  rw [ip_adjoint,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]
  simp [Matrix.mul_assoc,h,← Matrix.mul_assoc T Tᴴ]

def PairData.change {d : ℝ} {A B : Bool → M} (h : PairData d A B) (T : M)
    (u : T*Tᴴ=1) : PairData d (fun i => Tᴴ*A i*T) (fun i => Tᴴ*B i*T) where
  state i := Tᴴ *ᵥ h.state i
  orth := (ip_unitary T u _ _).trans h.orth
  leftMean i x := (expectation_unitary T u _ _).trans (h.leftMean i x)
  rightMean i x := (expectation_unitary T u _ _).trans (h.rightMean i x)
  joint i x y := by
    change expectation _ ((Tᴴ*A x*T)*(Tᴴ*B y*T))=_
    have he : (Tᴴ*A x*T)*(Tᴴ*B y*T)=Tᴴ*(A x*B y)*T := by
      calc
        _ = Tᴴ*A x*(T*Tᴴ)*B y*T := by simp only [Matrix.mul_assoc]
        _ = _ := by simp [u,Matrix.mul_assoc]
    rw [he,expectation_unitary _ u]
    exact h.joint i x y

theorem lMean (f : V) (x : ℂ) : expectation f (lEq x)=
    2*(x*(f 0*conj (f 2)+f 1*conj (f 3))).re := by
  simp [expectation,ip,lEq,vertical,Matrix.mulVec,dotProduct,Fin.sum_univ_four,
    Complex.mul_re,Complex.mul_im]
  ring

theorem rMean (f : V) (y : ℂ) : expectation f (rEq y)=
    2*(y*(f 0*conj (f 1)+f 2*conj (f 3))).re := by
  simp [expectation,ip,rEq,horizontal,Matrix.mulVec,dotProduct,Fin.sum_univ_four,
    Complex.mul_re,Complex.mul_im]
  ring

theorem jMean (f : V) (x y : ℂ) : expectation f (lEq x*rEq y)=
    correlation x y (f 0*conj (f 3)) (f 1*conj (f 2)) := by
  simp [expectation,ip,lEq,rEq,vertical,horizontal,Matrix.mul_apply,Matrix.mulVec,
    dotProduct,Fin.sum_univ_four,correlation,Complex.mul_re,Complex.mul_im]
  ring

theorem vanishes {v x : ℂ} (hx : x.im≠0) (h : 2*v.re=0)
    (hh : 2*(x*v).re=0) : v=0 := by
  apply Complex.ext
  · simp; linarith
  · have r : v.re=0 := by linarith
    simp [Complex.mul_re,r] at hh
    exact (hh.resolve_left hx)

def setting (x : ℂ) (b : Bool) := if b then x else 1

theorem circular_forces_zero {d : ℝ} {x y : ℂ} (hx : x.im≠0) (hy : y.im≠0)
    (h : PairData d (fun i => lEq (setting x i)) (fun j => rEq (setting y j))) : d=0 := by
  let f := h.state false
  let g := h.state true
  have row (i : Bool) : h.state i 0*conj (h.state i 2)+h.state i 1*conj (h.state i 3)=0 :=
    vanishes hx (by simpa [lMean,setting] using h.leftMean i false)
      (by simpa [lMean,setting] using h.leftMean i true)
  have col (i : Bool) : h.state i 0*conj (h.state i 1)+h.state i 2*conj (h.state i 3)=0 :=
    vanishes hy (by simpa [rMean,setting] using h.rightMean i false)
      (by simpa [rMean,setting] using h.rightMean i true)
  have j (i t u : Bool) : correlation (setting x t) (setting y u)
      (h.state i 0*conj (h.state i 3)) (h.state i 1*conj (h.state i 2))=entry d t u :=
    (jMean _ _ _).symm.trans (h.joint i t u)
  have ort : conj (f 0)*g 0+conj (f 1)*g 1+conj (f 2)*g 2+conj (f 3)*g 3=0 := by
    simpa [f,g,ip,dotProduct,Fin.sum_univ_four] using h.orth
  have all (t u : Bool) : correlation (setting x t) (setting y u)
      (f 0*conj (f 3)) (f 1*conj (f 2)) =
      correlation (setting x t) (setting y u) (g 0*conj (g 3)) (g 1*conj (g 2)) :=
    (j false t u).trans (j true t u).symm
  have he := singular_of_equal_correlations hx hy (row false) (col false) (row true) (col true)
    ort (by
      rintro s (rfl|hs) t (rfl|ht)
      · exact all false false
      · rw [Set.mem_singleton_iff.mp ht]; exact all false true
      · rw [Set.mem_singleton_iff.mp hs]; exact all true false
      · rw [Set.mem_singleton_iff.mp hs,Set.mem_singleton_iff.mp ht]; exact all true true)
  have m00 := j false false false
  have m01 := j false false true
  have m10 := j false true false
  have m11 := j false true true
  simp only [entry,setting,Bool.and_false,Bool.false_and,Bool.true_and,
    Bool.false_eq_true,ite_false,ite_true] at m00 m01 m10 m11
  rw [m00,m01,m10,m11] at he
  nlinarith

#print axioms circular_forces_zero

def chooseObs (a b : M) (t : Bool) := if t then b else a

/-- The tensor product of the two oriented circular bases for a real qubit. -/
def circularBasis : M := (1/2:ℂ) •
  !![1,1,1,1; I,-I,I,-I; I,I,-I,-I; -1,1,1,-1]

theorem circular_unitary : circularBasis*circularBasisᴴ=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [circularBasis,Matrix.mul_apply,Fin.sum_univ_four,Matrix.one_apply,
      Matrix.conjTranspose_apply,Complex.mul_re,Complex.mul_im,map_ofNat]

theorem circular_vertical (a r : ℝ) :
    circularBasisᴴ * vertical a a r r * circularBasis=lEq (a+(r:ℂ)*I) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [circularBasis,vertical,lEq,Matrix.mul_apply,Fin.sum_univ_four,
      Matrix.conjTranspose_apply,Complex.mul_re,Complex.mul_im] <;> ring

theorem circular_horizontal (a r : ℝ) :
    circularBasisᴴ * horizontal a a r r * circularBasis=rEq (a+(r:ℂ)*I) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [circularBasis,horizontal,rEq,Matrix.mul_apply,Fin.sum_univ_four,
      Matrix.conjTranspose_apply,Complex.mul_re,Complex.mul_im] <;> ring

theorem product_forces_zero {d a b r s : ℝ} (hr : r≠0) (hs : s≠0)
    (h : PairData d (chooseObs va (vertical a a r r)) (chooseObs hb (horizontal b b s s))) :
    d=0 := by
  have t := h.change circularBasis circular_unitary
  have tA : (fun i => circularBasisᴴ * chooseObs va (vertical a a r r) i * circularBasis)=
      (fun i => lEq (setting (a+(r:ℂ)*I) i)) := by
    funext i
    cases i
    · simpa [chooseObs,va,setting] using circular_vertical 1 0
    · exact circular_vertical a r
  have tB : (fun i => circularBasisᴴ * chooseObs hb (horizontal b b s s) i * circularBasis)=
      (fun i => rEq (setting (b+(s:ℂ)*I) i)) := by
    funext i
    cases i
    · simpa [chooseObs,hb,setting] using circular_horizontal 1 0
    · exact circular_horizontal b s
  rw [tA,tB] at t
  exact circular_forces_zero (by simpa [Complex.mul_im] using hr)
    (by simpa [Complex.mul_im] using hs) t

#print axioms product_forces_zero
end FractionalTensor
