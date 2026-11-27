module
public import Quantum.FractionalTensor
public import Quantum.FractionalPositive

/-! Normalizing the first block of an arbitrary measured SudoQ and passing to
its rank-one effects. All cell and measurement labels are retained. -/
@[expose] public section
noncomputable section
namespace FractionalProjectors
open Complex Matrix Finset QuantumCertificate FractionalTensor FractionalBinary
open scoped ComplexConjugate Matrix BigOperators

def projection (v : V) : M := vecMulVec v (star v)
def axis (i : Fin 4) : Space 4 := EuclideanSpace.single i 1
def firstOutcome (b : Bool) : Fin 4 := if b then 1 else 0

theorem ip_inner (v w : Space 4) : ip (⇑v) (⇑w)=inner ℂ v w := by
  simp [ip,PiLp.inner_apply,dotProduct,mul_comm]

theorem basis_projection_sum (B : ONB) : ∑ i, projection (⇑(B i))=1 := by
  ext i j
  have t := congrArg (fun v : Space 4 => v i) (B.sum_repr' (axis j))
  simpa [projection,Matrix.vecMulVec_apply,Matrix.sum_apply,Matrix.one_apply,axis,Fin.sum_univ_four,
    EuclideanSpace.inner_single_right,PiLp.single_apply,mul_comm,eq_comm] using t

theorem basis_projection_mul (B : ONB) (i j : Fin 4) :
    projection (⇑(B i))*projection (⇑(B j))=if i=j then projection (⇑(B i)) else 0 := by
  rw [projection,projection,Matrix.vecMulVec_mul_vecMulVec]
  change vecMulVec _ ((ip (⇑(B i)) (⇑(B j))) • _)=_
  rw [ip_inner,B.inner_eq_ite]
  by_cases h : i=j <;> simp [h]

theorem projection_hermitian (v : V) : (projection v)ᴴ=projection v := by
  ext i j
  simp [projection,Matrix.vecMulVec_apply,Matrix.conjTranspose_apply,mul_comm]

theorem basis_projection_trace (B : ONB) (i : Fin 4) : (projection (⇑(B i))).trace=1 := by
  have h := (ip_inner (B i) (B i)).trans (B.inner_eq_ite i i)
  simpa [projection,Matrix.vecMulVec_apply,Matrix.trace,Matrix.diag,ip,dotProduct,mul_comm] using h

theorem projection_expect (f v : Space 4) :
    expectation (⇑f) (projection (⇑v))=Complex.normSq (inner ℂ f v) := by
  have e : projection (⇑v) *ᵥ (⇑f) = (inner ℂ v f) • (⇑v : V) := by
    rw [projection,Matrix.vecMulVec_mulVec,← ip_inner]
    ext i
    simp [ip,mul_comm]
  rw [expectation,e]
  change (star (⇑f : V) ⬝ᵥ ((inner ℂ v f) • ⇑v)).re=_
  rw [dotProduct_smul]
  change ((inner ℂ v f)*ip (⇑f) (⇑v)).re=_
  rw [ip_inner,← inner_conj_symm v f,mul_comm,Complex.mul_conj]
  rfl

structure Model (p : Prob) where
  effect : Site → M
  state : Bool → V
  orth : ip (state false) (state true)=0
  born : ∀ i x, expectation (state i) (effect x)=p x (firstOutcome i)
  unitSum : ∀ l, ∑ k, effect (line l k)=1
  product : ∀ l i j, effect (line l i)*effect (line l j)=
    if i=j then effect (line l i) else 0
  hermitian : ∀ x, (effect x)ᴴ=effect x
  trace : ∀ x, (effect x).trace=1
  reference : ∀ i, effect (line 8 i)=projection (⇑(axis i))

/-- The normalized projectors come from the supplied grid by one common
unitary, which also transports arbitrary effects and generalized measurements. -/
theorem normalized_with_unitary {p : Prob} (v : Site → Space 4) (hg : Grid v)
    (hp : ∀ x a, Complex.normSq (v x a)=p x a) :
    ∃ (m : Model p) (T : M), T*Tᴴ=1 ∧
      ∀ x, m.effect x=Tᴴ*projection (⇑(v x))*T := by
  obtain ⟨base,hbase⟩ := hg 8
  let w (x : Site) : Space 4 := base.repr (v x)
  let f (a : Bool) : Space 4 := base.repr (axis (firstOutcome a))
  let T : M := fun i j => base j i
  have hT : T*Tᴴ=1 := by
    have b := basis_projection_sum base
    ext i j
    rw [Matrix.mul_apply]
    change (∑ k, base k i*conj (base k j))=_
    simpa [projection,Matrix.vecMulVec_apply,Matrix.sum_apply] using congrFun (congrFun b i) j
  have hrepr (x : Site) : Tᴴ *ᵥ (⇑(v x))=⇑(w x) := by
    funext i
    rw [show w x=base.repr (v x) by rfl,OrthonormalBasis.repr_apply_apply]
    change (∑ j,conj (base i j)*v x j)=_
    simp [PiLp.inner_apply,mul_comm]
  have hw (l : Fin 12) : ∃ B : ONB, ⇑B=fun i => w (line l i) := by
    obtain ⟨B,he⟩ := hg l
    exact ⟨B.map base.repr,funext fun i => by simp [w,he]⟩
  refine ⟨{ effect := fun x => projection (⇑(w x))
            state := fun a => ⇑(f a)
            orth := ?_
            born := ?_
            unitSum := ?_
            product := ?_
            hermitian := fun x => projection_hermitian _
            trace := ?_
            reference := ?_ },T,hT,?_⟩
  · rw [ip_inner]
    simp [f,firstOutcome,axis,EuclideanSpace.inner_single_left]
  · intro a x
    rw [projection_expect]
    simpa [f,w,axis,EuclideanSpace.inner_single_left] using hp x (firstOutcome a)
  · intro l
    obtain ⟨B,hB⟩ := hw l
    simpa only [hB] using basis_projection_sum B
  · intro l i j
    obtain ⟨B,hB⟩ := hw l
    simpa only [hB] using basis_projection_mul B i j
  · rintro ⟨r,c⟩
    let l : Fin 12 := ⟨r.val,by omega⟩
    have he : line l c=(r,c) := by fin_cases r <;> fin_cases c <;> rfl
    obtain ⟨B,hB⟩ := hw l
    simpa only [hB,he] using basis_projection_trace B c
  · intro i
    change projection (⇑(base.repr (v (line 8 i))))=_
    rw [←congrFun hbase i,OrthonormalBasis.repr_self]
    rfl
  · intro x
    change projection (⇑(w x))=_
    rw [←hrepr,projection,projection,Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,
      Matrix.star_mulVec,Matrix.conjTranspose_conjTranspose]

theorem normalized {p : Prob} (h : ArbitraryMeasurement p) : Nonempty (Model p) := by
  obtain ⟨v,hg,hp⟩ := any_basis.mp h
  obtain ⟨m,_,_,_⟩ := normalized_with_unitary v hg hp
  exact ⟨m⟩

#print axioms normalized
end FractionalProjectors
