module

public import Quantum.PunctureAlgebra
public import Quantum.PunctureSix

/-! Off-diagonal arrays with full projective cardinality in a space of
dimension one less than their order. -/

@[expose] public section
noncomputable section
namespace UniversalPuncture

open Finset Complex Matrix MaximalHypercubes
open scoped ComplexConjugate Matrix

theorem exists_frequency {q : ℕ} (hq : 5≤q) (h6 : q≠6) :
    ∃ a : ℕ, 1<a ∧ a+1<q ∧ a.Coprime q := by
  by_cases hodd : q%2=1
  · exact ⟨2,by decide,by omega,Nat.coprime_two_left.mpr ⟨q/2,by omega⟩⟩
  by_cases h4 : q%4=0
  · let a := q/2-1
    have ha : Odd a := ⟨q/4-1, by dsimp [a]; omega⟩
    have hq' : q = 2+2*a := by dsimp [a]; omega
    refine ⟨a,by dsimp [a]; omega,by dsimp [a]; omega,?_⟩
    conv_rhs => rw [hq']
    exact (Nat.coprime_add_mul_right_right _ _ _).mpr ha.coprime_two_right
  · let a := q/2-2
    have ha : Odd a := ⟨q/4-1, by dsimp [a]; omega⟩
    have hq' : q = 4+2*a := by dsimp [a]; omega
    refine ⟨a,by dsimp [a]; omega,by dsimp [a]; omega,?_⟩
    conv_rhs => rw [hq']
    apply (Nat.coprime_add_mul_right_right _ _ _).mpr
    exact ha.coprime_two_right.pow_right 2

def offDiagonal {n : ℕ} (p : QuantumCertificate.Cell n) : Bool := p.1 != p.2

theorem card_offDiagonal (n : ℕ) :
    Nat.card (QuantumCertificate.Used (@offDiagonal n)) = n*(n-1) := by
  classical
  let e : QuantumCertificate.Used (@offDiagonal n) ≃
      ↥((Finset.univ : Finset (Fin n)).offDiag) :=
    { toFun := fun p => ⟨p.val,Finset.mem_offDiag.mpr
        ⟨Finset.mem_univ _,Finset.mem_univ _,by simpa [offDiagonal] using p.property⟩⟩
      invFun := fun p => ⟨p.val,by simpa [offDiagonal] using (Finset.mem_offDiag.mp p.property).2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, Finset.offDiag_card]
  simp [Nat.mul_sub_one]

def dropCoordinate {d : ℕ} (v : Space (d+1)) : Space d :=
  WithLp.toLp 2 (fun i => v i.succ)

theorem drop_inner {d : ℕ} (v w : Space (d+1)) (h : v 0=0) :
    inner ℂ (dropCoordinate v) (dropCoordinate w) = inner ℂ v w := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_succ]
  simp [h,dropCoordinate]

/-- Drop the common diagonal direction of a full array after an isometric
change of coordinates. Only the projective separation of off-diagonal cells
is needed. -/
theorem compress {d : ℕ} (v : Fin (d+1) → Fin (d+1) → Space (d+1))
    (rows : ∀ i j k, inner ℂ (v i j) (v i k) = if j=k then 1 else 0)
    (cols : ∀ i j k, inner ℂ (v j i) (v k i) = if j=k then 1 else 0)
    (diag : ∀ i, v i i = v 0 0)
    (sep : ∀ {i j u w} {z : ℂ}, i ≠ j → z ≠ 0 → z • v u w = v i j → i=u ∧ j=w) :
    Nonempty (QuantumCertificate.PartialArray (d+1) d ((d+1)*d) offDiagonal) := by
  classical
  have ortho : Orthonormal ℂ (v 0) := orthonormal_iff_ite.mpr (rows 0)
  let B : OrthonormalBasis (Fin (d+1)) ℂ (Space (d+1)) := OrthonormalBasis.mk ortho
    (ortho.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)).ge
  have hB : ⇑B = v 0 := OrthonormalBasis.coe_mk _ _
  let g (p : QuantumCertificate.Cell (d+1)) := B.repr (v p.1 p.2)
  let f (p : QuantumCertificate.Cell (d+1)) := dropCoordinate (g p)
  have hz (p : QuantumCertificate.Used (@offDiagonal (d+1))) : g p.val 0 = 0 := by
    have hp : p.val.1 ≠ p.val.2 := by simpa [offDiagonal] using p.property
    change B.repr _ 0 = 0
    rw [B.repr_apply_apply, congrFun hB 0, ← diag p.val.1, rows, ite_eq_right hp]
  have hGram (p : QuantumCertificate.Used (@offDiagonal (d+1))) (q : QuantumCertificate.Cell (d+1)) :
      inner ℂ (f p.val) (f q) = inner ℂ (v p.val.1 p.val.2) (v q.1 q.2) :=
    (drop_inner _ _ (hz p)).trans (B.repr.inner_map_map _ _)
  have hUnit (p : QuantumCertificate.Used (@offDiagonal (d+1))) : ‖f p.val‖ = 1 := by
    have h : inner ℂ (f p.val) (f p.val) = 1 := by rw [hGram p,rows,ite_eq_left rfl]
    rw [inner_self_eq_norm_sq_to_K] at h
    have hh := congrArg Complex.re h
    norm_cast at hh
    change ‖f p.val‖^2 = 1 at hh
    nlinarith [norm_nonneg (f p.val)]
  have nz (p : QuantumCertificate.Used (@offDiagonal (d+1))) : f p.val ≠ 0 :=
    fun h => by simpa [h] using hUnit p
  refine ⟨⟨f,nz,hUnit,?_,?_,?_⟩⟩
  · intro i j k hj _ hjk
    exact (hGram ⟨(i,j),hj⟩ (i,k)).trans (by simp [rows,hjk])
  · intro i j k hj _ hjk
    exact (hGram ⟨(j,i),hj⟩ (k,i)).trans (by simp [cols,hjk])
  · have inject : Function.Injective (fun p : QuantumCertificate.Used (@offDiagonal (d+1)) =>
        Projectivization.mk ℂ (f p.val) (nz p)) := by
      intro p q h
      obtain ⟨z,he⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
      have hne : z ≠ 0 := by
        intro e
        exact nz p (by simpa [e] using he.symm)
      have hv : z • v q.val.1 q.val.2 = v p.val.1 p.val.2 := by
        apply B.repr.injective
        rw [map_smul]
        change z • g q.val = g p.val
        ext i
        refine Fin.cases ?_ (fun k => ?_) i
        · change z * g q.val 0 = g p.val 0
          rw [hz p,hz q,mul_zero]
        · exact congrArg (fun w : Space d => w k) he
      have hp : p.val.1 ≠ p.val.2 := by simpa [offDiagonal] using p.property
      exact Subtype.ext (Prod.ext (sep hp hne hv).1 (sep hp hne hv).2)
    rw [QuantumCertificate.rayRange,Set.ncard_range_of_injective inject,card_offDiagonal]
    simp

theorem puncture_fourier (r : ℕ) (hr : 0<r) {a : ℕ} (h1 : 1<a) (h2 : a+1<r+4)
    (hc : a.Coprime (r+4)) :
    Nonempty (QuantumCertificate.PartialArray (r+4) (r+3) ((r+4)*(r+3)) offDiagonal) := by
  obtain ⟨e,he⟩ := frequency_permutation h1 h2
  let v (i j : Fin (r+4)) := vector (quotient a e i j)
  apply compress v
  · intro i j k
    dsimp only [v]
    rw [vector_gram, quotient, quotient, Gram_left _ _ _ (fourierUnit_unitary _ _ _),
      adjoint_gram, fourierUnit_gram e he]
    split <;> simp only [map_natCast,map_zero,mul_zero,inv_mul_cancel₀ (order_ne r)]
  · intro i j k
    dsimp only [v]
    rw [vector_gram, quotient, quotient, Gram_right _ _ _ (adjoint_unitary (fourierUnit_unitary _ _ _)),
      fourierUnit_gram e he]
    split <;> simp only [mul_zero,inv_mul_cancel₀ (order_ne r)]
  · intro i
    simp [v,quotient,mul_adjoint_eq_one (fourierUnit_unitary _ _ _)]
  · exact fun hi hz h => quotient_separated hr hc e hi hz h

/-- For every order at least five, all ordered off-diagonal cells have
different projective rays and each punctured row and column is an
orthonormal basis of the ambient complex space of dimension q-1. -/
theorem universal_puncture (q : ℕ) (hq : 5≤q) :
    Nonempty (QuantumCertificate.PartialArray q (q-1) (q*(q-1)) (fun p => p.1 != p.2)) := by
  by_cases h6 : q=6
  · subst q
    exact puncture_six
  obtain ⟨a,h1,h2,hc⟩ := exists_frequency hq h6
  obtain ⟨r,rfl⟩ : ∃ r, q=r+4 := ⟨q-4,by omega⟩
  exact puncture_fourier r (by omega) h1 h2 hc

#print axioms universal_puncture
end UniversalPuncture
