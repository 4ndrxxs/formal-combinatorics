import Quantum.Hadamard.LinPhoaSourceArray
import Mathlib.NumberTheory.JacobiSum.Basic

/-! Character values of the two core Gram blocks. The paired Jacobi sums are
formed with Mathlib's zero-extended multiplicative characters. -/

noncomputable section
open Finset Matrix Hadamard.MSXCore Hadamard.NearBorder
namespace Hadamard.LinPhoa

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

def eta (F : Type) [Field F] [Fintype F] [DecidableEq F] : MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

@[simp] private theorem eta_apply (x : F) : eta F x=(quadraticChar F x:ℂ) := rfl

def squareFourier (ψ : MulChar F ℂ) : ℂ :=
  ∑ x : F, if quadraticChar F x=1 then ψ x*eta F (x-1) else 0

/-- Twice the Fourier coefficient on the nonzero squares is the sum of the
two Jacobi sums for the two possible extensions of the character. -/
theorem square_fourier_jacobi (q4 : Fintype.card F%4=1) (ψ : MulChar F ℂ) :
    2*squareFourier ψ=jacobiSum ψ (eta F)+jacobiSum (ψ*eta F) (eta F) := by
  have minus : quadraticChar F (-1)=1 :=
    (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr
      (FiniteField.isSquare_neg_one_iff.mpr (by omega))
  have rev (x : F) : eta F (1-x)=eta F (x-1) := by
    rw [show 1-x=(-1)*(x-1) by ring,map_mul,eta_apply,minus,Int.cast_one,one_mul]
  unfold squareFourier jacobiSum
  rw [mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro x _
  rw [MulChar.mul_apply,rev]
  by_cases zero : x=0
  · subst x; simp [MulChar.map_zero]
  · rcases quadraticChar_dichotomy zero with v|v <;> simp [v]
    ring

variable {m : ℕ} [NeZero m]

private theorem enum_add (e : Fin m ≃ SquareIndex F)
    (cyc : ∀ k l, (e (k-l)).val=(e k).val/(e l).val) (t k : Fin m) :
    (e (t+k)).val=(e t).val*(e k).val := by
  have nz : (e k).val≠0 := by intro h; have z := (e k).property; rw [h] at z; norm_num at z
  have h := cyc (t+k) k
  rw [add_sub_cancel_right] at h
  exact ((eq_div_iff nz).mp h).symm

omit [NeZero m] in
private theorem fourier_by_enumeration (ψ : MulChar F ℂ) (e : Fin m ≃ SquareIndex F) :
    (∑ t, ψ (e t).val*eta F ((e t).val-1))=squareFourier ψ := by
  let S := (univ : Finset F).filter (fun x ↦ quadraticChar F x=1)
  have memS (x : F) : x∈S ↔ quadraticChar F x=1 := by simp [S]
  calc
    _ = ∑ x : SquareIndex F, ψ x.val*eta F (x.val-1) := e.sum_comp _
    _ = ∑ x ∈ S, ψ x*eta F (x-1) := (sum_subtype S memS (fun x : F ↦ ψ x*eta F (x-1))).symm
    _ = _ := by simp only [S,sum_filter,squareFourier]

/-- The convolution kernel χ(z−y) on squares acts diagonally on every
restricted multiplicative character. -/
theorem difference_character (ψ : MulChar F ℂ) (e : Fin m ≃ SquareIndex F)
    (cyc : ∀ k l, (e (k-l)).val=(e k).val/(e l).val) (k : Fin m) :
    (∑ l, eta F ((e l).val-(e k).val)*ψ (e l).val)=ψ (e k).val*squareFourier ψ := by
  let term (l : Fin m) := eta F ((e l).val-(e k).val)*ψ (e l).val
  have shift := Equiv.sum_comp (Equiv.addRight k) term
  change (∑ t, term (t+k))=∑ t, term t at shift
  change (∑ t, term t)=_
  rw [←shift,←fourier_by_enumeration ψ e,mul_sum]
  apply sum_congr rfl
  intro t _
  change eta F ((e (t+k)).val-(e k).val)*ψ (e (t+k)).val=_
  rw [enum_add e cyc,show (e t).val*(e k).val-(e k).val=((e t).val-1)*(e k).val by ring,map_mul,map_mul]
  have unit : eta F (e k).val=1 := by rw [eta_apply,(e k).property,Int.cast_one]
  rw [unit,mul_one]; ring

/-- The literal two bulk diagonal Gram blocks have the same entries. -/
theorem bulk_character_entry (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (w : F) (hw : quadraticChar F w= -1) (i j c a : Bool) (e : Fin m ≃ SquareIndex F)
    (cyc : ∀ k l, (e (k-l)).val=(e k).val/(e l).val) (k l : Fin m) :
    (gram c (sourcePair w i j e) (bulk a k) (bulk a l) : ℂ)=
      (if k=l then (Fintype.card F:ℂ)+1 else 0)-
      2*(cosetSign i:ℂ)*eta F ((e l).val-(e k).val) := by
  let f := sourcePair w i j e
  have g := bulk_gram (core f) strip strip (corner c) strip_sign a k l
  have r := source_layout_gram w i j e cyc (layout m) a k l
  rw [layout_core] at r
  have gl : gram c f (bulk a k) (bulk a l)=(incidenceGram w i j (e k).val (e l).val:ℝ)+2 :=
    g.trans (congrArg (·+2) r)
  change (gram c f (bulk a k) (bulk a l):ℂ)=_
  rw [gl,incidence_gram hc q4 hw (e k).property (e l).property,eta_apply]
  by_cases ne : k=l
  · subst l; simp; ring
  · have diff : (e k).val≠(e l).val := fun h ↦ ne (e.injective (Subtype.ext h))
    rw [ite_eq_right diff,ite_eq_right ne]
    push_cast
    ring

/-- On each old row class of the actual bordered matrix, a multiplicative
character has the paired-Jacobi factor appearing in the eigenvalue. -/
theorem bulk_jacobi_mode (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (w : F) (hw : quadraticChar F w= -1) (i j c a : Bool) (e : Fin m ≃ SquareIndex F)
    (cyc : ∀ k l, (e (k-l)).val=(e k).val/(e l).val) (ψ : MulChar F ℂ) (k : Fin m) :
    (∑ l, (gram c (sourcePair w i j e) (bulk a k) (bulk a l):ℂ)*ψ (e l).val)=
      ((Fintype.card F:ℂ)+1-(cosetSign i:ℂ)*
        (jacobiSum ψ (eta F)+jacobiSum (ψ*eta F) (eta F)))*ψ (e k).val := by
  calc
    _ = ((Fintype.card F:ℂ)+1)*ψ (e k).val - 2*(cosetSign i:ℂ)*
        (∑ l, eta F ((e l).val-(e k).val)*ψ (e l).val) := by
      have main : ((Fintype.card F:ℂ)+1)*ψ (e k).val=
          ∑ l, (if k=l then (Fintype.card F:ℂ)+1 else 0)*ψ (e l).val := by
        simp [ite_mul]
      rw [main,mul_sum,←sum_sub_distrib]
      apply sum_congr rfl
      intro l _
      rw [bulk_character_entry hc q4 w hw i j c a e cyc k l]
      ring
    _ = _ := by
      rw [difference_character ψ e cyc k,←square_fourier_jacobi q4 ψ]
      ring

private theorem mode_sum_zero (ψ : MulChar F ℂ) (e : Fin m ≃ SquareIndex F)
    (cyc : ∀ k l, (e (k-l)).val=(e k).val/(e l).val) (h : ∃ k, ψ (e k).val≠1) :
    (∑ l, ψ (e l).val)=0 := by
  obtain ⟨k,hk⟩ := h
  have shift := Equiv.sum_comp (Equiv.addRight k) (fun t : Fin m ↦ ψ (e t).val)
  change (∑ t, ψ (e (t+k)).val)=∑ t, ψ (e t).val at shift
  simp only [enum_add e cyc,map_mul,←sum_mul] at shift
  exact (mul_eq_zero.mp (show (∑ t, ψ (e t).val)*(ψ (e k).val-1)=0 by
    rw [mul_sub,mul_one,shift,sub_self])).resolve_right (sub_ne_zero.mpr hk)

/-- A cyclic character extended by zero outside its chosen bulk class. -/
def supportedMode (e : Fin m ≃ SquareIndex F) (a : Bool) (ψ : MulChar F ℂ) : Index m → ℂ
  | .inl (b,k) => if b=a then ψ (e k).val else 0
  | .inr _ => 0

/-- Every nontrivial restricted character gives a nonzero eigenvector of the
complete Gram matrix on each old class, with its exact paired-Jacobi eigenvalue.
The corner and choice of the second support are unrestricted. -/
theorem full_jacobi_mode (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (w : F) (hw : quadraticChar F w= -1) (i j c a : Bool) (e : Fin m ≃ SquareIndex F)
    (cyc : ∀ k l, (e (k-l)).val=(e k).val/(e l).val) (ψ : MulChar F ℂ)
    (hψ : ∃ k, ψ (e k).val≠1) :
    supportedMode e a ψ≠0 ∧
    ((gram c (sourcePair w i j e)).map Complex.ofReal).mulVec (supportedMode e a ψ)=
      ((Fintype.card F:ℂ)+1-(cosetSign i:ℂ)*
        (jacobiSum ψ (eta F)+jacobiSum (ψ*eta F) (eta F))) • supportedMode e a ψ := by
  let f := sourcePair w i j e
  let G := gram c f
  have sym (x y : Index m) : G x y=G y x := by simp [G,gram,Matrix.mul_apply,mul_comm]
  constructor
  · intro z
    have val := congrFun z (bulk a (0:Fin m))
    have nz : (e 0).val≠0 := by intro h; have t := (e 0).property; rw [h] at t; norm_num at t
    have unit : IsUnit (ψ (e 0).val) := (isUnit_iff_ne_zero.mpr nz).map ψ.toMonoidHom
    exact unit.ne_zero (by simpa [bulk,supportedMode] using val)
  · funext x
    change (∑ y, (G x y:ℂ)*supportedMode e a ψ y)=_ * supportedMode e a ψ x
    have restrict : (∑ y, (G x y:ℂ)*supportedMode e a ψ y)=
        ∑ l, (G x (bulk a l):ℂ)*ψ (e l).val := by
      simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool]
      cases a <;> simp [supportedMode,bulk]
    rw [restrict]
    rcases x with ⟨b,k⟩|b
    · by_cases same : b=a
      · subst b
        simpa only [supportedMode,ite_true] using bulk_jacobi_mode hc q4 w hw i j c a e cyc ψ k
      · have cross (l : Fin m) : G (bulk b k) (bulk a l)=0 := by
          cases b <;> cases a
          · exact (same rfl).elim
          · exact bulk_cross c f k l
          · rw [sym]; exact bulk_cross c f l k
          · exact (same rfl).elim
        change (∑ l,(G (bulk b k) (bulk a l):ℂ)*ψ (e l).val)=_ * (if b=a then ψ (e k).val else 0)
        simp [cross,same]
    · have same (l : Fin m) : G (rim b) (bulk a l)=G (rim b) (bulk a 0) := by
        have s := mixed_gram ((layout m).core f) strip strip (corner c) ((layout m).regular f) a l 0 b
        rw [layout_core] at s
        exact (sym _ _).trans (s.trans (sym _ _))
      change (∑ l,(G (rim b) (bulk a l):ℂ)*ψ (e l).val)=_ * 0
      simp only [same,←mul_sum,mode_sum_zero ψ e cyc hψ,mul_zero]

/-- Coordinates on the two border rows and the two constant bulk vectors. -/
def constantVector (x : Fin 4 → ℝ) : Index m → ℝ
  | .inr false => x 0
  | .inr true => x 1
  | .inl (false,_) => x 2
  | .inl (true,_) => x 3

def constantMatrix (v r c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![c,c,v,v; c,-c,v,-v; 1,1,r,0; 1,-1,0,-r]

/-- On vectors that are constant on each old class the full sign matrix acts
by this four-dimensional matrix, including for the two excluded corners. -/
theorem constant_action (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (w : F) (hw : quadraticChar F w= -1) (i j c : Bool) (e : Fin m ≃ SquareIndex F)
    (x : Fin 4 → ℝ) :
    (array c (sourcePair w i j e)).mulVec (constantVector x)=
      constantVector ((constantMatrix m (if i then 0 else -2) (orientation c)).mulVec x) := by
  let f := sourcePair w i j e
  have s := source_pair_sums hc q4 w hw i j e
  have direct (b : Bool) (k : Fin m) : (∑ l, f b (l-k))=∑ l, f b l :=
    (Equiv.subRight k).sum_comp (f b)
  have refl (b : Bool) (k : Fin m) : (∑ l, f b (k-l))=∑ l, f b l :=
    (Equiv.subLeft k).sum_comp (f b)
  change (array c f).mulVec _=_
  funext row
  rcases row with ⟨b,k⟩|b <;> cases b <;>
    simp only [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool,
      array,bordered,core,strip,corner,constantVector,constantMatrix,Fin.sum_univ_four] <;>
    simp [←sum_mul,direct,refl,show (∑ l,f false l)=(if i then 0 else -2) from s.1,
      show (∑ l,f true l)=0 from s.2] <;> ring

/-- Exact prefactor from the constant subspace. -/
theorem constant_det (v r c : ℝ) : (constantMatrix v r c).det=2*((c*r-v)^2+v^2) := by
  rw [Matrix.det_succ_row_zero]
  norm_num [constantMatrix,Matrix.det_fin_three,Fin.sum_univ_four,Matrix.submatrix_apply,Fin.succAbove]
  ring

#print axioms constant_action
#print axioms constant_det
#print axioms full_jacobi_mode
#print axioms bulk_character_entry
#print axioms bulk_jacobi_mode
#print axioms square_fourier_jacobi
#print axioms difference_character
end Hadamard.LinPhoa
