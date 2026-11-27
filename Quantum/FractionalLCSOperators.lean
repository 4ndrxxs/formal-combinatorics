module
public import Quantum.FractionalLCSSeven
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-! The ray projector solution verifies power, pairwise commutation and the ordered context products. -/
@[expose] public section
noncomputable section
namespace TransitiveLCS
open QuantumCertificate Finset Complex
open scoped ComplexConjugate BigOperators

abbrev End (p : ℕ) := Module.End ℂ (Space p)

def basisRay {p : ℕ} (b : Basis p) (i : Fin p) : Ray p :=
  Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i)

def root (p : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / p)

theorem primitive_root {p : ℕ} [NeZero p] : IsPrimitiveRoot (root p) p :=
  Complex.isPrimitiveRoot_exp p (NeZero.ne _)

/-- All variables act by genuine unitaries. Each enumerating orthonormal basis lists
a context once, with commuting gates and the prescribed scalar product. -/
def Arrangement.Quantum {p : ℕ} (A : Arrangement p) : Prop :=
  ∃ X : Ray p → End p,
    (∀ v ∈ A.rays, (∃ U : Unitary p, U.toLinearEquiv.toLinearMap = X v) ∧ X v ^ p = 1) ∧
    ∀ C ∈ A.contexts, ∀ b : Basis p, basisRays b = C →
      (∀ i j, Commute (X (basisRay b i)) (X (basisRay b j))) ∧
      (List.ofFn (fun i => X (basisRay b i))).prod = root p • (1 : End p)

def gate {p : ℕ} (z : ℂ) (q : Ray p) : End p :=
  1 + (z-1) • q.submodule.starProjection.toLinearMap

def factor {p : ℕ} (z : ℂ) (i j : Fin p) : ℂ := if i=j then z else 1

theorem gate_basis {p : ℕ} (z : ℂ) (b : Basis p) (i j : Fin p) :
    gate z (basisRay b i) (b j) = factor z i j • b j := by
  change b j + (z-1) • ((Submodule.span ℂ {b i}).starProjection (b j)) = _
  rw [Submodule.starProjection_singleton,b.norm_eq_one,
    b.inner_eq_ite]
  by_cases h : i=j
  · subst j
    simp [factor,sub_smul]
  · simp [h,factor]

theorem gate_power {p : ℕ} {z : ℂ} (hz : z ^ p=1) (b : Basis p) (i : Fin p) :
    gate z (basisRay b i) ^ p = 1 := by
  have h (k : ℕ) (j : Fin p) : (gate z (basisRay b i)^k) (b j) = (factor z i j)^k • b j := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ',mul_apply_eq_comp,ih,map_smul,gate_basis,smul_smul,pow_succ]
  apply b.toBasis.ext
  intro j
  change (gate z (basisRay b i)^p) (b j) = b j
  rw [h]
  by_cases e : i=j <;> simp [factor,e,hz]

theorem gate_unitary {p : ℕ} [NeZero p] {z : ℂ} (hz : ‖z‖=1) (b : Basis p) (i : Fin p) :
    ∃ U : Unitary p, U.toLinearEquiv.toLinearMap = gate z (basisRay b i) := by
  have un (j : Fin p) : conj (factor z i j) * factor z i j = 1 := by
    by_cases h : i=j <;> simp [factor,h,Complex.conj_mul',hz]
  have hon : Orthonormal ℂ (fun j => factor z i j • b j) := by
    rw [orthonormal_iff_ite]
    intro a c
    rw [inner_smul_left,inner_smul_right,b.inner_eq_ite]
    by_cases h : a=c
    · subst c
      simp [un]
    · simp [h]
  let d : Basis p := OrthonormalBasis.mk hon
    (hon.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)).ge
  refine ⟨b.equiv d (Equiv.refl _),b.toBasis.ext ?_⟩
  intro j
  change b.equiv d (Equiv.refl _) (b j) = gate z (basisRay b i) (b j)
  rw [OrthonormalBasis.equiv_apply_basis,gate_basis]
  exact congrFun (OrthonormalBasis.coe_mk _ _) j

theorem gate_commute {p : ℕ} (z : ℂ) (b : Basis p) (i j : Fin p) :
    Commute (gate z (basisRay b i)) (gate z (basisRay b j)) := by
  apply b.toBasis.ext
  intro k
  change gate z (basisRay b i) (gate z (basisRay b j) (b k)) =
    gate z (basisRay b j) (gate z (basisRay b i) (b k))
  rw [gate_basis,gate_basis,map_smul,map_smul,gate_basis,gate_basis,smul_smul,smul_smul,mul_comm]

theorem gate_product {p : ℕ} (z : ℂ) (b : Basis p) :
    (List.ofFn (fun i => gate z (basisRay b i))).prod = z • (1 : End p) := by
  have h (l : List (Fin p)) (j : Fin p) :
      (l.map (fun i => gate z (basisRay b i))).prod (b j) =
        (l.map (fun i => factor z i j)).prod • b j := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons,List.prod_cons,mul_apply_eq_comp,ih,map_smul,gate_basis,smul_smul]
      rw [mul_comm]
  apply b.toBasis.ext
  intro j
  change (List.ofFn (fun i => gate z (basisRay b i))).prod (b j) = z • b j
  have hj := h (List.ofFn (id : Fin p → Fin p)) j
  simp [List.map_ofFn,List.prod_ofFn,factor] at hj
  exact hj

theorem Arrangement.quantum {p : ℕ} [NeZero p] (A : Arrangement p) : A.Quantum := by
  classical
  refine ⟨gate (root p),?_,?_⟩
  · intro q hq
    obtain ⟨C,hC,hqC⟩ := (A.incidence q).mp hq
    obtain ⟨b,rfl⟩ := A.orthonormal C hC
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hqC
    change basisRay b i = q at hi
    subst q
    exact ⟨gate_unitary (primitive_root.norm'_eq_one (NeZero.ne p)) b i,
      gate_power primitive_root.pow_eq_one b i⟩
  · intro C hC b hb
    exact ⟨gate_commute (root p) b,gate_product (root p) b⟩

theorem Seven.physical_gap : ∃ A : Arrangement 7,
    A.RayAndContextTransitive ∧ A.Quantum ∧ ¬ A.Classical := by
  obtain ⟨A,hA,hc⟩ := Seven.transitive_gap
  exact ⟨A,hA,A.quantum,hc⟩

#print axioms Seven.physical_gap
end TransitiveLCS

