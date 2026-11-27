import Quantum.Hadamard.ProjectivePaleyDeterminant

/-! Projective changes of the two homogeneous coordinates of the Paley matrix.
The induced permutation preserves every absolute completed determinant up to
a common change of orientation of its diagonal. -/

noncomputable section
open Matrix Finset
open scoped BigOperators

namespace Hadamard.ProjectiveSigning
namespace Coordinates

variable {F : Type} [Field F] [DecidableEq F]

def x : Option F → F
  | none => 1
  | some u => u

def y : Option F → F
  | none => 0
  | some _ => 1

def point (u v : F) : Option F := if v=0 then none else some (u/v)

def scale (u v : F) : F := if v=0 then u else v

theorem extract (p : Option F) : point (x p) (y p) = p := by
  cases p <;> simp [point,x,y]

theorem scaled_point (r u v : F) (hr : r≠0) :
    point (r*u) (r*v) = point u v := by
  by_cases hv : v=0
  · simp [hv,point]
  · simp only [point,mul_ne_zero hr hv,hv,ite_false,Option.some.injEq]
    field_simp

theorem restoreX (u v : F) : scale u v * x (point u v) = u := by
  by_cases h : v=0
  · simp [h,scale,point,x]
  · simp only [h,scale,point,x,ite_false]
    field_simp

theorem restoreY (u v : F) : scale u v * y (point u v) = v := by
  by_cases h : v=0 <;> simp [h,scale,point,y]

theorem scale_ne (u v : F) (h : u≠0 ∨ v≠0) : scale u v ≠ 0 := by
  by_cases hv : v=0 <;> simp_all [scale]

structure Change (F : Type) [Field F] where
  a : F
  b : F
  c : F
  d : F
  invertible : a*d-b*c≠0

namespace Change

def det (g : Change F) := g.a*g.d-g.b*g.c

def top (g : Change F) (u v : F) := g.a*u+g.b*v
def bot (g : Change F) (u v : F) := g.c*u+g.d*v

def act (g : Change F) (p : Option F) := point (g.top (x p) (y p)) (g.bot (x p) (y p))
def factor (g : Change F) (p : Option F) := scale (g.top (x p) (y p)) (g.bot (x p) (y p))

theorem top_eq (g : Change F) (i : Option F) :
    g.factor i*x (g.act i)=g.top (x i) (y i) := restoreX ..
theorem bot_eq (g : Change F) (i : Option F) :
    g.factor i*y (g.act i)=g.bot (x i) (y i) := restoreY ..

theorem factor_ne (g : Change F) (i : Option F) : g.factor i≠0 := by
  apply scale_ne
  by_contra! h
  dsimp [top,bot] at h
  have hu : g.det*x i=0 := by
    dsimp [det]; linear_combination g.d*h.1-g.b*h.2
  have hv : g.det*y i=0 := by
    dsimp [det]; linear_combination g.a*h.2-g.c*h.1
  have ux := (mul_eq_zero.mp hu).resolve_left g.invertible
  have vy := (mul_eq_zero.mp hv).resolve_left g.invertible
  cases i <;> simp_all [x,y]

def adj (g : Change F) : Change F :=
  ⟨g.d,-g.b,-g.c,g.a,by simpa [mul_comm] using g.invertible⟩

theorem adj_act (g : Change F) (i : Option F) : g.adj.act (g.act i)=i := by
  let r := g.factor i
  have hr : r≠0 := g.factor_ne i
  have hx := g.top_eq i
  have hy := g.bot_eq i
  change point (g.d*x (g.act i)+(-g.b)*y (g.act i))
    ((-g.c)*x (g.act i)+g.a*y (g.act i))=i
  rw [←scaled_point r _ _ hr]
  have p : r*(g.d*x (g.act i)+(-g.b)*y (g.act i))=g.det*x i := by
    dsimp [r,det,top,bot] at *
    linear_combination g.d*hx-g.b*hy
  have q : r*((-g.c)*x (g.act i)+g.a*y (g.act i))=g.det*y i := by
    dsimp [r,det,top,bot] at *
    linear_combination -g.c*hx+g.a*hy
  rw [p,q,scaled_point g.det (x i) (y i) (show g.det≠0 from g.invertible),extract]

def perm (g : Change F) : Option F ≃ Option F where
  toFun := g.act
  invFun := g.adj.act
  left_inv := g.adj_act
  right_inv i := by simpa [adj] using g.adj.adj_act i

end Change

def bracket (i j : Option F) : F := y i*x j-x i*y j

theorem bracket_change (g : Change F) (i j : Option F) :
    g.factor i*g.factor j*bracket (g.act i) (g.act j)=g.det*bracket i j := by
  calc
    _ = (g.factor i*y (g.act i))*(g.factor j*x (g.act j))-
        (g.factor i*x (g.act i))*(g.factor j*y (g.act j)) := by unfold bracket; ring
    _ = _ := by rw [g.top_eq,g.top_eq,g.bot_eq,g.bot_eq]; unfold Change.top Change.bot Change.det bracket; ring

variable [Fintype F]

theorem char_bracket (hm : quadraticChar F (-1)=1) (i j : Option F) :
    quadraticChar F (bracket i j)=HadamardMod.TorusFrobenius.entry i j := by
  cases i <;> cases j <;> simp [bracket,x,y,HadamardMod.TorusFrobenius.entry,hm]

theorem paley_change (hm : quadraticChar F (-1)=1) (g : Change F) (i j : Option F) :
    HadamardMod.TorusFrobenius.entry (g.perm i) (g.perm j)=
    quadraticChar F g.det*quadraticChar F (g.factor i)*quadraticChar F (g.factor j)*
    HadamardMod.TorusFrobenius.entry i j := by
  have h := congrArg (quadraticChar F) (bracket_change g i j)
  simp only [map_mul,char_bracket hm] at h
  change HadamardMod.TorusFrobenius.entry (g.act i) (g.act j)=_
  have hi := quadraticChar_sq_one (g.factor_ne i)
  have hj := quadraticChar_sq_one (g.factor_ne j)
  calc
    _ = (quadraticChar F (g.factor i))^2 * (quadraticChar F (g.factor j))^2 *
        HadamardMod.TorusFrobenius.entry (g.act i) (g.act j) := by rw [hi,hj]; ring
    _ = _ := by linear_combination quadraticChar F (g.factor i)*quadraticChar F (g.factor j)*h

end Coordinates

/-- Removing signs from both the row and column of each index, and one common
sign from the whole matrix, preserves its absolute determinant. -/
theorem abs_det_signed {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℝ)
    (u : I→ℝ) (g : ℝ) (hu : ∀i, |u i|=1) (hg : |g|=1) :
    |(g • (diagonal u * A * diagonal u)).det|=|A.det| := by
  have h : |(diagonal u).det|=1 := by simp [det_diagonal,Finset.abs_prod,hu]
  rw [det_smul, det_mul, det_mul, abs_mul, abs_pow, hg, one_pow, one_mul, abs_mul, abs_mul, h]
  ring

variable {F : Type} [Field F] [DecidableEq F] [Fintype F]

def signedDet (s : Option F→ℤ) : ℝ :=
  |(realPaley + diagonal (fun i ↦ (s i:ℝ))).det|

theorem signedDet_change (hm : quadraticChar F (-1)=1) (g : Coordinates.Change F)
    (s : Option F→ℤ) :
    signedDet s = signedDet (fun i ↦ quadraticChar F g.det*s (g.perm i)) := by
  let G : ℝ := (quadraticChar F g.det : ℤ)
  let U (i : Option F) : ℝ := (quadraticChar F (g.factor i) : ℤ)
  have signG : G=1 ∨ G= -1 := by
    dsimp [G]; exact_mod_cast quadraticChar_dichotomy (show g.det≠0 from g.invertible)
  have signU (i) : U i=1 ∨ U i= -1 := by
    dsimp [U]; exact_mod_cast quadraticChar_dichotomy (g.factor_ne i)
  let B := realPaley (F:=F)+diagonal (fun i ↦ ((quadraticChar F g.det*s (g.perm i):ℤ):ℝ))
  have eqn : (realPaley (F:=F)+diagonal (fun i ↦ (s i:ℝ))).submatrix g.perm g.perm
      = G • (diagonal U * B * diagonal U) := by
    ext i j
    have he : realPaley (g.perm i) (g.perm j)=G*U i*U j*realPaley i j := by
      dsimp [realPaley,G,U]; exact_mod_cast Coordinates.paley_change hm g i j
    simp only [Matrix.submatrix_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.mul_diagonal,Matrix.diagonal_mul,B,Int.cast_mul,Matrix.diagonal_apply,Equiv.apply_eq_iff_eq]
    rw [he]
    by_cases h : i=j
    · subst j
      simp only [ite_true]
      change G*U i*U i*realPaley i i+(s (g.perm i):ℝ)=
        G*(U i*(realPaley i i+G*(s (g.perm i):ℝ))*U i)
      rcases signG with hg|hg <;> rcases signU i with hi|hi <;> rw [hg,hi] <;> ring
    · simp [h]; ring
  unfold signedDet
  rw [←det_submatrix_equiv_self g.perm,eqn]
  apply abs_det_signed
  · intro i; rcases signU i with h|h <;> simp [h]
  · rcases signG with h|h <;> simp [h]

#print axioms signedDet_change

end Hadamard.ProjectiveSigning
