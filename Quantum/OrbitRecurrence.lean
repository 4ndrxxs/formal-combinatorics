module
public import Quantum.OrbitCutoff

/-! Minimal integer orbit relations and the all-time test for a nonmonic
source relation. All operators act on rational states. -/
@[expose] public section
noncomputable section
namespace RationalOrbit
open Polynomial
open scoped nonZeroDivisors

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

abbrev castQ := algebraMap ℤ ℚ
def act (T : Module.End ℚ V) (v : V) (P : ℚ[X]) := (aeval T P) v

def annihilating (T : Module.End ℚ V) (v : V) : Ideal ℚ[X] where
  carrier := {P | act T v P=0}
  zero_mem' := by simp [act]
  add_mem' := by intro a b ha hb; change act T v a=0 at ha; change act T v b=0 at hb
                 change act T v (a+b)=0; simpa [act] using congrArg₂ (·+·) ha hb
  smul_mem' := by
    intro a b h
    change act T v b=0 at h
    change act T v (a*b)=0
    simpa [act,mul_apply_eq_comp] using congrArg (aeval T a) h

/-- Divisibility here is in the ordinary integer polynomial ring. -/
structure SourceEquation (T : Module.End ℚ V) (v : V) (D : ℤ[X]) : Prop where
  primitive : D.IsPrimitive
  detects : ∀ P : ℤ[X], act T v (P.map castQ)=0 ↔ D∣P

theorem source_equation_exists [FiniteDimensional ℚ V] (T : Module.End ℚ V) (v : V) :
    ∃ D : ℤ[X], D≠0 ∧ SourceEquation T v D := by
  let I := annihilating T v
  let g := Submodule.IsPrincipal.generator I
  have iffG (P : ℚ[X]) : act T v P=0 ↔ g∣P := Submodule.IsPrincipal.mem_iff_generator_dvd I
  have ng : g≠0 := by
    intro eq
    have ch := (iffG T.charpoly).mp (by simp [act,T.aeval_self_charpoly])
    exact T.charpoly_monic.ne_zero (zero_dvd_iff.mp (eq ▸ ch))
  let M := IsLocalization.integerNormalization (nonZeroDivisors ℤ) g
  obtain ⟨s,hs,eq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) g
  have sn : s≠0 := mem_nonZeroDivisors_iff_ne_zero.mp hs
  have e : M.map castQ=C (s:ℚ)*g := by
    simpa only [M,C_mul',Int.cast_smul_eq_zsmul] using eq
  have snq : (s:ℚ)≠0 := by exact_mod_cast sn
  have nz : M≠0 := by
    intro zero
    have nn : C (s:ℚ)*g≠0 := mul_ne_zero (C_ne_zero.mpr snq) ng
    exact nn (by rw [← e,zero]; simp)
  let D := M.primPart
  have hD : D.IsPrimitive := M.isPrimitive_primPart
  have nzD : D≠0 := by intro hh; exact nz (by simpa [D,hh] using M.eq_C_content_mul_primPart)
  have cont : M.content≠0 := fun h => nz (content_eq_zero_iff.mp h)
  have unitS : IsUnit (C (s:ℚ)) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr snq)
  have unitC : IsUnit (C (M.content:ℚ)) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by exact_mod_cast cont))
  have f : M.map castQ = C (M.content:ℚ)*D.map castQ := by
    conv_lhs => rw [M.eq_C_content_mul_primPart]
    simp [D,castQ]
  refine ⟨D,nzD,hD,fun P => ?_⟩
  rw [iffG,IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast D P hD]
  change g∣P.map castQ ↔ D.map castQ∣P.map castQ
  calc
    _ ↔ M.map castQ∣P.map castQ := by rw [e,unitS.mul_left_dvd]
    _ ↔ _ := by rw [f,unitC.mul_left_dvd]

theorem SourceEquation.reduction_ne_zero {T : Module.End ℚ V} {v : V} {D : ℤ[X]}
    (h : SourceEquation T v D) (p : ℕ) [Fact p.Prime] : D.map (red p)≠0 := by
  intro eq
  have div : C (p:ℤ)∣D := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    change red p (D.coeff i)=0
    rw [← coeff_map,eq,coeff_zero]
  have u := Int.isUnit_iff.mp (h.primitive _ div)
  have pr : p.Prime := Fact.out
  have := pr.two_le
  omega

/-- An integer target polynomial records A times the proposed target state.
When the source polynomial has nonunit leading coefficient this gives a
finite search directly on the powers of the original operator. -/
theorem SourceEquation.hit_bound_sharp {T : Module.End ℚ V} {v w : V} {D : ℤ[X]}
    (h : SourceEquation T v D) {p : ℕ} [Fact p.Prime] (hd : (p:ℤ)∣D.leadingCoeff)
    (A : ℤ) (P : ℤ[X]) (target : act T v (P.map castQ)=(A:ℚ) • w) (t : ℕ)
    (ha : ¬(p:ℤ)^(t+1)∣A) (k : ℕ) (hit : (T^k) v=w) :
    k≤P.natDegree+t*(D.natDegree-(D.map (red p)).natDegree) := by
  have hv : D∣C A*X^k+(-P) := by
    apply (h.detects _).mp
    simp only [act,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,
      Polynomial.map_X,Polynomial.map_neg,map_add,map_mul,aeval_C,map_pow,aeval_X,map_neg,
      LinearMap.add_apply,mul_apply_eq_comp,Module.algebraMap_end_apply,LinearMap.neg_apply]
    change (A:ℚ) • (T^k) v + -(act T v (P.map castQ))=0
    rw [hit,target,add_neg_cancel]
  simpa using gap_bound_sharp D (h.reduction_ne_zero p) hd k t A (-P) ha hv

theorem SourceEquation.hit_bound {T : Module.End ℚ V} {v w : V} {D : ℤ[X]}
    (h : SourceEquation T v D) {p : ℕ} [Fact p.Prime] (hd : (p:ℤ)∣D.leadingCoeff)
    (A : ℤ) (P : ℤ[X]) (target : act T v (P.map castQ)=(A:ℚ) • w) (t : ℕ)
    (ha : ¬(p:ℤ)^(t+1)∣A) (k : ℕ) (hit : (T^k) v=w) :
    k≤P.natDegree+t*D.natDegree :=
  (h.hit_bound_sharp hd A P target t ha k hit).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left t (Nat.sub_le _ _)) _)

end RationalOrbit
