module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Tactic

/-! A rational Householder family puts finitely many nonzero rational vectors
in full coordinate support while preserving any specified open condition on
their squared coordinates. -/
@[expose] public section
noncomputable section
namespace FractionalRationalRotation
open Complex Finset Polynomial Filter
open scoped BigOperators ComplexConjugate Polynomial Topology

variable {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
abbrev E (J : Type*) [Fintype J] := EuclideanSpace ℂ J

private def exponent (j : J) : ℕ := (Fintype.equivFin J j).val
private def first (J : Type*) [Fintype J] [Nonempty J] : J :=
  (Fintype.equivFin J).symm ⟨0,Fintype.card_pos⟩

omit [DecidableEq J] [Nonempty J] in
private theorem exp_inj : Function.Injective (exponent : J → ℕ) :=
  Fin.val_injective.comp (Fintype.equivFin J).injective

private theorem zero_power (j : J) : (0:ℚ)^exponent j=if j=first J then 1 else 0 := by
  have h0 : exponent (first J)=0 := by simp [exponent,first]
  by_cases h : j=first J
  · simp [h,h0]
  · have n : exponent j≠0 := fun e => h (exp_inj (e.trans h0.symm))
    simp [h,zero_pow n]

private def pol (z : J → ℚ) : ℚ[X] := ∑ j, monomial (exponent j) (z j)
private def den (J : Type*) [Fintype J] : ℚ[X] := ∑ j : J, (X^exponent j)^2
private def num (z : J → ℚ) (k : J) : ℚ[X] := 2*X^exponent k*pol z-den J*C (z k)

omit [DecidableEq J] [Nonempty J] in
private theorem pol_eval (z : J → ℚ) (t : ℚ) : (pol z).eval t=∑ j,z j*t^exponent j := by
  simp [pol,Polynomial.eval_finsetSum,Polynomial.eval_monomial]
omit [DecidableEq J] [Nonempty J] in
private theorem den_eval (t : ℚ) : (den J).eval t=∑ j : J,(t^exponent j)^2 := by
  simp [den,Polynomial.eval_finsetSum]
omit [DecidableEq J] [Nonempty J] in
private theorem num_eval (z : J → ℚ) (k : J) (t : ℚ) :
    (num z k).eval t=2*t^exponent k*(pol z).eval t-(den J).eval t*z k := by simp [num]

private theorem den_zero : (den J).eval 0=1 := by
  rw [den_eval]
  simp [zero_power,ite_pow]
omit [DecidableEq J] in
private theorem den_ne (t : ℚ) : (den J).eval t≠0 := by
  rw [den_eval]
  apply ne_of_gt
  have one : (t^exponent (first J))^2=1 := by simp [exponent,first]
  have le := Finset.single_le_sum (s:=Finset.univ) (fun j _ => sq_nonneg (t^exponent j)) (mem_univ (first J))
  linarith

omit [Nonempty J] in
private theorem pol_coeff (z : J → ℚ) (k : J) : (pol z).coeff (exponent k)=z k := by
  simp only [pol,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial_apply,exp_inj.eq_iff,
    Finset.sum_ite_eq',mem_univ,ite_true]

private theorem num_zero (z : J → ℚ) (k : J) :
    (num z k).eval 0=if k=first J then z k else -z k := by
  rw [num_eval,pol_eval,den_zero]
  simp only [zero_power,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',mem_univ,ite_true]
  split <;> simp_all; ring

private theorem num_ne (z : J → ℚ) (nz : ∃ i, z i≠0) (k : J) : num z k≠0 := by
  by_cases h : z k=0
  · have pp : pol z≠0 := by
      obtain ⟨i,hi⟩ := nz
      intro e
      have eq := pol_coeff z i
      simp [e] at eq
      exact hi eq.symm
    simp [num,h,pp]
  · intro e
    have b := num_zero z k
    rw [e,Polynomial.eval_zero] at b
    split at b <;> simp_all

private def amp (z : J → ℚ) (t : ℚ) (k : J) := (num z k).eval t/(den J).eval t
def state (z : J → ℚ) : E J := WithLp.toLp 2 (fun j => (z j:ℂ))
private def axis (t : ℚ) : E J := state (fun j => t^exponent j)
private def U (t : ℚ) : E J ≃ₗᵢ[ℂ] E J := (ℂ ∙ axis t).reflection

omit [DecidableEq J] [Nonempty J] in
private theorem axis_inner (z : J → ℚ) (t : ℚ) : inner ℂ (axis t) (state z)=((pol z).eval t:ℚ) := by
  rw [PiLp.inner_apply,pol_eval]
  change (∑ j, (z j:ℂ)*conj ((t^exponent j:ℚ):ℂ))=_
  push_cast
  simp

omit [DecidableEq J] [Nonempty J] in
private theorem axis_self (t : ℚ) : ((‖axis (J:=J) t‖:ℂ)^2)=((den J).eval t:ℚ) := by
  calc
    _=inner ℂ (axis (J:=J) t) (axis (J:=J) t) := (inner_self_eq_norm_sq_to_K _).symm
    _=(((pol (fun j : J => t^exponent j)).eval t:ℚ):ℂ) := axis_inner _ _
    _=_ := by rw [pol_eval,den_eval]; simp only [pow_two]

omit [DecidableEq J] in
private theorem apply_U (z : J → ℚ) (t : ℚ) (k : J) : U t (state z) k=(amp z t k:ℂ) := by
  rw [U,Submodule.reflection_singleton_apply,axis_inner]
  simp only [PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,two_smul]
  change ((((pol z).eval t:ℚ):ℂ)/(‖axis (J:=J) t‖:ℂ)^2)*((t^exponent k:ℚ):ℂ)+
    ((((pol z).eval t:ℚ):ℂ)/(‖axis (J:=J) t‖:ℂ)^2)*((t^exponent k:ℚ):ℂ)-(z k:ℂ)=_
  rw [axis_self (J:=J) t]
  unfold amp
  rw [num_eval]
  have hn : (((den J).eval t:ℚ):ℂ)≠0 := by exact_mod_cast den_ne (J:=J) t
  push_cast
  field_simp
  ring

def probabilities {X : Type*} (z : X → J → ℚ) : X → J → ℝ := fun q k => (z q k:ℝ)^2

/-- A single rational unitary change of coordinates simultaneously removes
all zero entries. The squared table stays in any given open neighbourhood
of the starting table. The transformed coordinates are again rational real. -/
theorem perturb {X : Type*} [Finite X] (z : X → J → ℚ) (nonzero : ∀ q, ∃ j, z q j≠0)
    (G : Set (X → J → ℝ)) (hG : IsOpen G) (belongs : probabilities z∈G) :
    ∃ (T : E J ≃ₗᵢ[ℂ] E J) (w : X → J → ℚ),
      (∀ q k, T (state (z q)) k=(w q k:ℂ)) ∧ (∀ q k, w q k≠0) ∧ probabilities w∈G := by
  let v (t : ℚ) (q : X) (k : J) := amp (z q) t k
  have continuousTable : Continuous (fun t => probabilities (v t)) := by
    apply continuous_pi
    intro q
    apply continuous_pi
    intro k
    exact (Rat.continuous_coe_real.comp
      ((num (z q) k).continuous.div (den J).continuous den_ne)).pow 2
  have atZero : probabilities (v 0)=probabilities z := by
    funext q k
    change (((num (z q) k).eval 0/(den J).eval 0:ℚ):ℝ)^2=_
    rw [num_zero,den_zero,div_one]
    split <;> simp [probabilities]
  have stays : ∀ᶠ t in 𝓝[≠] (0:ℚ), probabilities (v t)∈G :=
    (continuousTable.continuousAt.eventually (hG.mem_nhds (by
      change probabilities (v 0)∈G; rwa [atZero]))).filter_mono nhdsWithin_le_nhds
  have full : ∀ᶠ t in 𝓝[≠] (0:ℚ), ∀ q k, v t q k≠0 := by
    apply Filter.eventually_all.mpr
    intro q
    apply Filter.eventually_all.mpr
    intro k
    have h := (Polynomial.eventually_eval_ne_zero_cofinite (num_ne (z q) (nonzero q) k)).filter_mono
      (nhdsNE_le_cofinite (0:ℚ))
    exact h.mono fun t ht => div_ne_zero ht (den_ne t)
  obtain ⟨t,ht,hopen⟩ := (full.and stays).exists
  exact ⟨U t,v t,fun q k => apply_U (z q) t k,ht,hopen⟩

#print axioms perturb
end FractionalRationalRotation

