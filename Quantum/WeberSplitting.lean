module
public import Quantum.WeberMatching

/-! Classification of the two-projection splitting problem, Weber 2023, Problem 3.5.
The parameter is a reducing subspace for the two original projections. Fixing its
action on their common kernel gives a unique parameter even in infinite dimension. -/
@[expose] public section
noncomputable section
namespace WeberSplitting

open WeberCompletion (Op)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The exact constraints in Weber's question. The sum conditions themselves
imply orthogonality between the two summands of each original projection. -/
structure Split (P Q A B C D : Op H) : Prop where
  projA : IsStarProjection A
  projB : IsStarProjection B
  projC : IsStarProjection C
  projD : IsStarProjection D
  sumP : P = A+B
  sumQ : Q = C+D
  crossAC : A*C=0
  crossBD : B*D=0

/-- The four summands are parametrized by one common reducing projection. -/
structure Param (P Q A B C D E : Op H) : Prop where
  proj : IsStarProjection E
  commP : Commute E P
  commQ : Commute E Q
  firstP : E*P=A
  secondP : (1-E)*P=B
  firstQ : (1-E)*Q=C
  secondQ : E*Q=D

private theorem adjoint_zero {X Y : Op H} (px : IsStarProjection X)
    (py : IsStarProjection Y) (h : X*Y=0) : Y*X=0 := by
  simpa [px.isSelfAdjoint.star_eq,py.isSelfAdjoint.star_eq] using congrArg star h

private theorem reverse_product {X Y Z : Op H} (px : IsStarProjection X)
    (py : IsStarProjection Y) (pz : IsStarProjection Z) (h : X*Y=Z) : Y*X=Z := by
  simpa [px.isSelfAdjoint.star_eq,py.isSelfAdjoint.star_eq,pz.isSelfAdjoint.star_eq]
    using congrArg star h

/-- A canonical representative fixes the whole common zero subspace of P and Q. -/
def FixCommon (P Q E : Op H) := ∀ x, P x=0 → Q x=0 → E x=x

theorem Split.canonical {P Q A B C D : Op H} (hp : IsStarProjection P)
    (hq : IsStarProjection Q) (s : Split P Q A B C D) :
    ∃ E, Param P Q A B C D E ∧ FixCommon P Q E := by
  let _ : Module ℚ (Op H) := Module.compHom (Op H) (algebraMap ℚ ℂ)
  let _ : HasUniqueDiv (Op H) := HasUniqueDiv.of_module_rat _
  have pp := (s.projA.add_iff_isStarOrtho s.projB).mp (s.sumP ▸ hp)
  have qq := (s.projC.add_iff_isStarOrtho s.projD).mp (s.sumQ ▸ hq)
  have ba : B*A=0 := pp.mul_eq_zero s.projB.isSelfAdjoint
  have cd : C*D=0 := qq.mul_eq_zero' s.projD.isSelfAdjoint
  have ca : C*A=0 := adjoint_zero s.projA s.projC s.crossAC
  let K := B.toLinearMap.ker ⊓ C.toLinearMap.ker
  let _ : IsClosed (K : Set H) := B.isClosed_ker.inter C.isClosed_ker
  let _ : CompleteSpace K := IsClosed.completeSpace_coe
  let E := K.starProjection
  have e : IsStarProjection E := isStarProjection_starProjection
  have kfix {x : H} (b : B x=0) (c : C x=0) : E x=x :=
    Submodule.starProjection_eq_self_iff.mpr (show x∈K from ⟨b,c⟩)
  have atx {X Y : Op H} (z : X*Y=0) (x : H) : X (Y x)=0 :=
    congrArg (fun T : Op H => T x) z
  have ea : E*A=A := ContinuousLinearMap.ext fun x => kfix (atx ba x) (atx ca x)
  have ed : E*D=D := ContinuousLinearMap.ext fun x => kfix (atx s.crossBD x) (atx cd x)
  have be : B*E=0 := ContinuousLinearMap.ext fun x => (K.starProjection_apply_mem x).1
  have ce : C*E=0 := ContinuousLinearMap.ext fun x => (K.starProjection_apply_mem x).2
  have eb := adjoint_zero s.projB e be
  have ec := adjoint_zero s.projC e ce
  have ep : E*P=A := by rw [s.sumP,mul_add,ea,eb,add_zero]
  have eq : E*Q=D := by rw [s.sumQ,mul_add,ec,ed,zero_add]
  have comP : Commute E P := ep.trans (reverse_product e hp s.projA ep).symm
  have comQ : Commute E Q := eq.trans (reverse_product e hq s.projD eq).symm
  refine ⟨E,⟨e,comP,comQ,ep,?_,?_,eq⟩,?_⟩
  · rw [sub_mul,one_mul,ep,s.sumP]; abel
  · rw [sub_mul,one_mul,eq,s.sumQ]; abel
  · intro x px qx
    have bp : B*P=B := by rw [s.sumP,mul_add,ba,s.projB.isIdempotentElem.eq,zero_add]
    have cq : C*Q=C := by rw [s.sumQ,mul_add,cd,s.projC.isIdempotentElem.eq,add_zero]
    apply kfix
    · have z := congrArg (fun T : Op H => T x) bp
      change B (P x)=B x at z
      simpa [px] using z.symm
    · have z := congrArg (fun T : Op H => T x) cq
      change C (Q x)=C x at z
      simpa [qx] using z.symm

theorem Param.split {P Q A B C D E : Op H} (hp : IsStarProjection P)
    (hq : IsStarProjection Q) (t : Param P Q A B C D E) : Split P Q A B C D := by
  have cp := (Commute.one_left P).sub_left t.commP
  have cq := (Commute.one_left Q).sub_left t.commQ
  constructor
  · rw [← t.firstP]; exact t.proj.mul hp t.commP
  · rw [← t.secondP]; exact t.proj.one_sub.mul hp cp
  · rw [← t.firstQ]; exact t.proj.one_sub.mul hq cq
  · rw [← t.secondQ]; exact t.proj.mul hq t.commQ
  · rw [← t.firstP,← t.secondP]; noncomm_ring
  · rw [← t.firstQ,← t.secondQ]; noncomm_ring
  · rw [← t.firstP,← t.firstQ,← mul_assoc,mul_assoc E P (1-E),← cp.eq,
      ← mul_assoc,t.proj.mul_one_sub_self,zero_mul,zero_mul]
  · rw [← t.secondP,← t.secondQ,← mul_assoc,mul_assoc (1-E) P E,← t.commP.eq,
      ← mul_assoc,t.proj.one_sub_mul_self,zero_mul,zero_mul]

/-- Classification without a choice of representative. -/
theorem weber_problem_3_5 {P Q A B C D : Op H} (hp : IsStarProjection P) (hq : IsStarProjection Q) :
    Split P Q A B C D ↔ ∃ E, Param P Q A B C D E := by
  constructor
  · intro s
    obtain ⟨E,t,_⟩ := s.canonical hp hq
    exact ⟨E,t⟩
  · rintro ⟨E,t⟩
    exact t.split hp hq

/-- A bijective form of the classification. Two parameters can differ only on
the common kernel. Requiring both to fix it removes exactly that freedom. -/
theorem canonical_unique {P Q A B C D : Op H} (hp : IsStarProjection P)
    (hq : IsStarProjection Q) :
    Split P Q A B C D ↔ ∃! E, Param P Q A B C D E ∧ FixCommon P Q E := by
  constructor
  · intro s
    obtain ⟨E,t,te⟩ := s.canonical hp hq
    refine ⟨E,⟨t,te⟩,?_⟩
    rintro F ⟨u,uf⟩
    have pe : P*E=P*F := t.commP.eq.symm.trans (t.firstP.trans (u.firstP.symm.trans u.commP.eq))
    have qe : Q*E=Q*F := t.commQ.eq.symm.trans (t.secondQ.trans (u.secondQ.symm.trans u.commQ.eq))
    have delta (S : Op H) (h : S*E=S*F) (x : H) : S ((F-E) x)=0 := by
      have z := congrArg (fun T : Op H => T x) h
      change S (E x)=S (F x) at z
      simp [sub_apply,z]
    have zero : (F-E)*(F-E)=0 := by
      ext x
      have p := delta P pe x
      have q := delta Q qe x
      change F ((F-E) x)-E ((F-E) x)=0
      rw [uf _ p q,te _ p q,sub_self]
    have adj : star (F-E)=F-E := by simp [u.proj.isSelfAdjoint.star_eq,t.proj.isSelfAdjoint.star_eq]
    apply sub_eq_zero.mp
    apply star_mul_self_eq_zero.mp
    rwa [adj]
  · rintro ⟨E,⟨t,_⟩,_⟩
    exact t.split hp hq

#print axioms weber_problem_3_5
#print axioms canonical_unique
end WeberSplitting
