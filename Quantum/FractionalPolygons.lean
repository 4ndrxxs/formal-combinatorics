module
public import Quantum.FractionalTorus
public import Quantum.Sudoku

/-! A global phase compatibility theorem for prescribed complex magnitudes on
any finite orthogonality pattern. Each pair supplies a closing polygon. The
remaining tests are the integer relations among its normalized side phases. -/
@[expose] public section
noncomputable section
namespace FractionalPolygons
open Complex Finset FractionalTorus
open scoped ComplexConjugate BigOperators

def unit (a : Torus) : ℂ := (a.toCircle:ℂ)
@[simp] theorem unit_add (a b : Torus) : unit (a+b)=unit a*unit b := by simp [unit]
@[simp] theorem unit_sub (a b : Torus) : unit (a-b)=unit a*conj (unit b) := by
  simp only [unit,sub_eq_add_neg,Real.Angle.toCircle_add,Real.Angle.toCircle_neg,
    Circle.coe_mul,Circle.coe_inv_eq_conj]
@[simp] theorem norm_unit (a : Torus) : ‖unit a‖=1 := Circle.norm_coe _
@[simp] theorem normSq_unit (a : Torus) : normSq (unit a)=1 := Circle.normSq_coe _

variable {X S E : Type*} [Fintype S]

def weight (p : X → S → ℝ) (L R : E → X) (e : E) (a : S) : ℝ :=
  Real.sqrt (p (L e) a)*Real.sqrt (p (R e) a)

def Realizable (p : X → S → ℝ) (L R : E → X) : Prop :=
  ∃ v : X → S → ℂ, (∀ x a, normSq (v x a)=p x a) ∧
    ∀ e, ∑ a, v (L e) a*conj (v (R e) a)=0

def GlobalPhases (p : X → S → ℝ) (L R : E → X) : Prop :=
  ∃ z : X → S → Torus, ∀ e, ∑ a, (weight p L R e a:ℂ)*unit (z (L e) a-z (R e) a)=0

def amplitude (p : X → S → ℝ) (z : X → S → Torus) (x : X) (a : S) : ℂ :=
  (Real.sqrt (p x a):ℂ)*unit (z x a)

omit [Fintype S] in
private theorem amplitude_product (p : X → S → ℝ) (z : X → S → Torus) (L R : E → X)
    (e : E) (a : S) : amplitude p z (L e) a*conj (amplitude p z (R e) a) =
      (weight p L R e a:ℂ)*unit (z (L e) a-z (R e) a) := by
  simp [amplitude,weight]
  ring

theorem realizable_iff_phases (p : X → S → ℝ) (L R : E → X) (hp : ∀ x a, 0≤p x a) :
    Realizable p L R ↔ GlobalPhases p L R := by
  constructor
  · rintro ⟨v,hm,hv⟩
    let z : X → S → Torus := fun x a => ((v x a).arg:Real.Angle)
    have re (x : X) (a : S) : amplitude p z x a=v x a := by
      have hx : Real.sqrt (p x a)=‖v x a‖ := by
        rw [←hm,Complex.normSq_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)]
      simp [amplitude,z,unit,hx,Circle.coe_exp]
    refine ⟨z,fun e => ?_⟩
    simpa only [←amplitude_product,re] using hv e
  · rintro ⟨z,hz⟩
    refine ⟨amplitude p z,fun x a => ?_,fun e => ?_⟩
    · simp [amplitude,Complex.normSq_mul,Complex.normSq_ofReal,← sq,Real.sq_sqrt (hp x a)]
    · simpa only [amplitude_product] using hz e

abbrev Observed (p : X → S → ℝ) (L R : E → X) :=
  {d : E × S // weight p L R d.1 d.2≠0}

def relationRow (L R : E → X) (base : E → S) (e : E) (a : S) : lattice (X×S) :=
  Finsupp.single (L e,a) 1-Finsupp.single (R e,a) 1-
    Finsupp.single (L e,base e) 1+Finsupp.single (R e,base e) 1

omit [Fintype S] in
@[simp] theorem row_evaluate (L R : E → X) (base : E → S) (e : E) (a : S)
    (v : X×S → Torus) : evaluate v (relationRow L R base e a) =
      v (L e,a)-v (R e,a)-v (L e,base e)+v (R e,base e) := by simp [relationRow]

def PolygonCriterion (p : X → S → ℝ) (L R : E → X) (base : E → S) : Prop :=
  ∃ t : E → S → Torus, (∀ e, ∑ a, (weight p L R e a:ℂ)*unit (t e a)=0) ∧
    ∀ c : lattice (Observed p L R),
      evaluate (fun (d : Observed p L R) => relationRow L R base d.1.1 d.1.2) c=0 →
      evaluate (fun (d : Observed p L R) => t d.1.1 d.1.2-t d.1.1 (base d.1.1)) c=0

theorem global_iff_polygon (p : X → S → ℝ) (L R : E → X) (base : E → S) :
    GlobalPhases p L R ↔ PolygonCriterion p L R base := by
  let rows := fun (d : Observed p L R) => relationRow L R base d.1.1 d.1.2
  constructor
  · rintro ⟨z,h⟩
    refine ⟨fun e a => z (L e) a-z (R e) a,h,?_⟩
    apply (integral_relations rows _).mp
    refine ⟨fun q => z q.1 q.2,fun d => ?_⟩
    simp [rows]; abel
  · rintro ⟨t,h,rel⟩
    obtain ⟨v,hv⟩ := (integral_relations rows
      (fun d => t d.1.1 d.1.2-t d.1.1 (base d.1.1))).mpr rel
    refine ⟨fun x a => v (x,a),fun e => ?_⟩
    let δ := v (L e,base e)-v (R e,base e)-t e (base e)
    calc
      _ = ∑ a, ((weight p L R e a:ℂ)*unit (t e a))*unit δ := by
        apply sum_congr rfl
        intro a _
        by_cases ha : weight p L R e a=0
        · simp [ha]
        · have hh := hv ⟨(e,a),ha⟩
          change evaluate v (relationRow L R base e a) = t e a-t e (base e) at hh
          rw [row_evaluate] at hh
          have diff : v (L e,a)-v (R e,a)=t e a+δ := by
            dsimp [δ]; linear_combination (norm := abel) hh
          rw [diff,unit_add,mul_assoc]
      _ = 0 := by rw [← sum_mul,h,zero_mul]

theorem realizable_iff_polygon (p : X → S → ℝ) (L R : E → X) (base : E → S)
    (hp : ∀ x a, 0≤p x a) : Realizable p L R ↔ PolygonCriterion p L R base :=
  (realizable_iff_phases p L R hp).trans (global_iff_polygon p L R base)

#print axioms realizable_iff_polygon

namespace Sudoku
open QuantumSudoku
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

abbrev Site (I : Type*) := Index I × Index I
def Adjacent (x y : Site I) : Prop :=
  x≠y ∧ (x.1=y.1 ∨ x.2=y.2 ∨ x.1.1=y.1.1 ∧ x.2.1=y.2.1)
abbrev Edge (I : Type*) := {e : Site I × Site I // Adjacent e.1 e.2}
def L (e : Edge I) := e.1.1
def R (e : Edge I) := e.1.2

def Measured (p : Site I → Index I → ℝ) : Prop :=
  ∃ v : Grid I, ∃ measurement : OrthonormalBasis (Index I) ℂ (H I),
    Valid v ∧ ∀ x a, normSq (measurement.repr (v x.1 x.2) a)=p x a

omit [Nonempty I] in
private theorem line_orth {v : Index I → H I} (h : BasisLine v) {x y : Index I} (hne : x≠y) :
    inner ℂ (v x) (v y)=0 := by
  obtain ⟨B,rfl⟩ := h
  simp [B.inner_eq_ite,hne]

omit [Nonempty I] in
private theorem valid_orth {v : Grid I} (h : Valid v) (x y : Site I) (e : Adjacent x y) :
    inner ℂ (v x.1 x.2) (v y.1 y.2)=0 := by
  rcases x with ⟨⟨i,a⟩,⟨j,b⟩⟩
  rcases y with ⟨⟨k,c⟩,⟨l,d⟩⟩
  rcases e with ⟨ne,row|col|blocks⟩
  · change (i,a)=(k,c) at row
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj row
    exact line_orth (h.row (i,a)) (fun eq => ne (Prod.ext rfl eq))
  · change (j,b)=(l,d) at col
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj col
    exact line_orth (h.column (j,b)) (fun eq => ne (Prod.ext eq rfl))
  · change i=k ∧ j=l at blocks
    obtain ⟨rfl,rfl⟩ := blocks
    apply line_orth (h.block i j) (x:=(a,b)) (y:=(c,d))
    intro eq
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    exact ne rfl

theorem measured_iff_vector (p : Site I → Index I → ℝ) (hs : ∀ x, ∑ a, p x a=1) :
    Measured p ↔ Realizable p (L (I:=I)) R := by
  constructor
  · rintro ⟨v,B,h,hp⟩
    refine ⟨fun x => ⇑(B.repr (v x.1 x.2)),hp,fun e => ?_⟩
    have t := valid_orth h e.1.2 e.1.1 ⟨Ne.symm e.2.1,
      e.2.2.elim (fun he => Or.inl he.symm) (fun he => Or.inr (he.elim
        (fun hh => Or.inl hh.symm) (fun hh => Or.inr ⟨hh.1.symm,hh.2.symm⟩)))⟩
    have eq := B.repr.inner_map_map (v e.1.2.1 e.1.2.2) (v e.1.1.1 e.1.1.2)
    have e' := eq.trans t
    rw [PiLp.inner_apply] at e'
    exact e'
  · rintro ⟨f,hm,hf⟩
    let v : Grid I := fun r c => WithLp.toLp 2 (f (r,c))
    have orth (x y : Site I) (h : Adjacent x y) : inner ℂ (v y.1 y.2) (v x.1 x.2)=0 := by
      simpa [v,PiLp.inner_apply,L,R] using hf ⟨(x,y),h⟩
    have normOne (x : Site I) : inner ℂ (v x.1 x.2) (v x.1 x.2)=1 := by
      rw [PiLp.inner_apply]
      change ∑ a, f x a*conj (f x a)=1
      simp only [Complex.mul_conj,hm,← Complex.ofReal_sum,hs,Complex.ofReal_one]
    refine ⟨v,EuclideanSpace.basisFun (Index I) ℂ,⟨?_,?_,?_⟩,fun x a => by simpa [v] using hm x a⟩
    · intro r
      apply basis_of_gram
      intro x y
      by_cases ne : x=y
      · subst y; simpa using normOne (r,x)
      · simpa [ne] using orth (r,y) (r,x) ⟨by simp [Ne.symm ne],Or.inl rfl⟩
    · intro c
      apply basis_of_gram
      intro x y
      by_cases ne : x=y
      · subst y; simpa using normOne (x,c)
      · simpa [ne] using orth (y,c) (x,c) ⟨by simp [Ne.symm ne],Or.inr (Or.inl rfl)⟩
    · intro i j
      apply basis_of_gram
      rintro ⟨a,b⟩ ⟨c,d⟩
      by_cases ne : (a,b)=(c,d)
      · obtain ⟨rfl,rfl⟩ := Prod.mk.inj ne
        simpa using normOne ((i,a),(j,b))
      · have dif : ((i,c),(j,d))≠((i,a),(j,b)) := by
          simp only [Prod.mk.injEq] at ne ⊢
          grind
        simpa [ne] using orth ((i,c),(j,d)) ((i,a),(j,b)) ⟨dif,Or.inr (Or.inr ⟨rfl,rfl⟩)⟩

/-- Every dimension, every complex measuring basis, and every labelled
Sudoku row, column, and block are covered. -/
theorem arbitrary_basis_iff_polygons (p : Site I → Index I → ℝ)
    (hs : ∀ x, ∑ a, p x a=1) (hp : ∀ x a, 0≤p x a) (base : Edge I → Index I) :
    Measured p ↔ PolygonCriterion p L R base :=
  (measured_iff_vector p hs).trans (realizable_iff_polygon p L R base hp)

#print axioms arbitrary_basis_iff_polygons

/-- The same finite list tests every choice of closed polygons for a fixed
support pattern, independent of all chosen side phases. -/
theorem arbitrary_basis_iff_finite (p : Site I → Index I → ℝ)
    (hs : ∀ x, ∑ a, p x a=1) (hp : ∀ x a, 0≤p x a) (base : Edge I → Index I) :
    ∃ tests : Finset (lattice (Observed p L R)),
      (∀ c ∈ tests, evaluate
        (fun (d : Observed p L R) => relationRow L R base d.1.1 d.1.2) c=0) ∧
      (Measured p ↔ ∃ t : Edge I → Index I → Torus,
        (∀ e, ∑ a, (weight p L R e a:ℂ)*unit (t e a)=0) ∧
        ∀ c ∈ tests, evaluate
          (fun (d : Observed p L R) => t d.1.1 d.1.2-t d.1.1 (base d.1.1)) c=0) := by
  classical
  let rows := fun (d : Observed p L R) => relationRow L R base d.1.1 d.1.2
  obtain ⟨tests,ht,hr⟩ := finite_relations rows
  refine ⟨tests,ht,?_⟩
  rw [arbitrary_basis_iff_polygons p hs hp base]
  exact exists_congr fun t => and_congr_right fun _ =>
    hr (fun d => t d.1.1 d.1.2-t d.1.1 (base d.1.1))

#print axioms arbitrary_basis_iff_finite
end Sudoku
end FractionalPolygons
