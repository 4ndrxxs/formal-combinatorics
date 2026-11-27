import PermanentPolynomialCurve

/-! Second-order data and exact smooth-zero identities for the polynomial curve. -/
noncomputable section
open Finset MvPolynomial PermanentFive PermanentBorder PermanentJets PermanentCurve
namespace PermanentDeformation
variable {K J : Type*} [Field K] [Fintype J] [DecidableEq J]

private theorem mult_jets (b : Polynomial K) (h : b.coeff 0=1) :
    (multiplier b).coeff 0=1 ∧
    (b*multiplier b).coeff 0=1 ∧ (b*multiplier b).coeff 1=0 ∧ (b*multiplier b).coeff 2=0 := by
  have eq : b*multiplier b=1+(b-1)^3 := by unfold multiplier; ring
  rw [eq]
  simp [multiplier,pow_succ,PermanentCurve.mul_one,PermanentCurve.mul_two,h,Polynomial.coeff_one]

theorem curve_jets (two : (2:K)≠0) (v : Cells J) :
    (curve K J v).coeff 0=base K J v ∧ (curve K J v).coeff 1=direction K J v ∧
    (curve K J v).coeff 2=bend K J v := by
  let x := tangentLine K J
  let b := gradAt x corner
  let f := multiplier b
  let q := -f*value x
  obtain ⟨hf,h0,h1,h2⟩ := mult_jets b (line_cofactor K J)
  obtain ⟨p0,p1,p2⟩ := line_per_jets (J:=J) two
  change (value x).coeff 0=0 at p0
  change (value x).coeff 1=0 at p1
  change (value x).coeff 2=_ at p2
  change f.coeff 0=1 at hf
  change (b*f).coeff 0=1 at h0
  change (b*f).coeff 1=0 at h1
  change (b*f).coeff 2=0 at h2
  have q0 : q.coeff 0=0 := by simp [q,p0]
  have q1 : q.coeff 1=0 := by simp [q,PermanentCurve.mul_one,p0,p1]
  have q2 : q.coeff 2=4*(Fintype.card J:K) := by simp [q,PermanentCurve.mul_two,hf,p0,p1,p2]
  change (editCol x corner (b*f) q v).coeff 0=_ ∧ (editCol x corner (b*f) q v).coeff 1=_ ∧
    (editCol x corner (b*f) q v).coeff 2=_
  have x0 : (x v).coeff 0=_ := line_zero (K:=K) v
  have x1 : (x v).coeff 1=_ := line_one (K:=K) v
  have x2 : (x v).coeff 2=0 := line_two (K:=K) v
  rcases v with ⟨a,c⟩
  cases a <;> cases c <;>
    simp [editCol,corner,bend,PermanentCurve.mul_one,PermanentCurve.mul_two,
      h0,h1,h2,q0,q1,q2,x0,x1,x2]

theorem curve_taylor (two : (2:K)≠0) (p : MvPolynomial (Cells J) K) :
    (subst (curve K J) p).coeff 0=atOne p ∧
    (subst (curve K J) p).coeff 1=atOne (dir (direction K J) p) ∧
    2*(subst (curve K J) p).coeff 2=
      atOne (dir (direction K J) (dir (direction K J) p))+2*atOne (dir (bend K J) p) :=
  taylor _ _ _ _ (fun i ↦ (curve_jets two i).1) (fun i ↦ (curve_jets two i).2.1)
    (fun i ↦ (curve_jets two i).2.2) p

theorem curve_value (t : K) : value (Polynomial.eval t ∘ curve K J)=0 := by
  have mapval (z : Cells J→Polynomial K) : value (Polynomial.eval t ∘ z)=Polynomial.eval t (value z) := by
    change value ((Polynomial.evalRingHom t) ∘ z)=(Polynomial.evalRingHom t) (value z)
    simp only [value_terms,map_sum,map_prod,Function.comp_apply]
  rw [mapval,curve,correction_zero,Polynomial.eval_zero]

theorem curve_grad (t : K) :
    gradAt (Polynomial.eval t ∘ curve K J) corner=Polynomial.eval t (gradAt (tangentLine K J) corner) := by
  change gradAt ((Polynomial.evalRingHom t) ∘ curve K J) corner=_
  rw [grad_map,curve,correction_smooth]
  rfl

end PermanentDeformation
