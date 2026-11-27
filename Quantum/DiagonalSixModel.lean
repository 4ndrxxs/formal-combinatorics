module
public import Quantum.Diagonal
public import Mathlib.Analysis.Matrix.Order

/-! Rank-one projector model of a diagonal quantum Latin square in order six.
The index pairs are the orbits of the ordinary reversal of Fin 6. -/
@[expose] public section
noncomputable section
namespace DiagonalSix
open Complex Matrix Finset QuantumCertificate
open scoped ComplexConjugate Matrix BigOperators

abbrev Tri := Fin 3
abbrev Bit := Fin 2
abbrev Idx := Tri × Bit
abbrev M := Matrix (Fin 6) (Fin 6) ℂ
abbrev V := Fin 6 → ℂ
abbrev B6 := OrthonormalBasis (Fin 6) ℂ (Space 6)

def ord : Idx ≃ Fin 6 where
  toFun a := if a.2=0 then ⟨a.1.val,by omega⟩ else ⟨5-a.1.val,by omega⟩
  invFun u := if h : u.val<3 then (⟨u.val,h⟩,0)
    else (⟨5-u.val,by omega⟩,1)
  left_inv := by rintro ⟨i,t⟩; fin_cases i <;> fin_cases t <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem ord_rev (i : Tri) (t : Bit) : ord (i,t.rev)=(ord (i,t)).rev := by
  fin_cases i <;> fin_cases t <;> rfl

def proj (v : Space 6) : M := vecMulVec (⇑v : V) (star (⇑v : V))

theorem basis_sum (B : B6) : ∑ i, proj (B i)=1 := by
  ext i j
  have t := congrArg (fun v : Space 6 => v i) (B.sum_repr' (EuclideanSpace.single j 1))
  simpa [proj,Matrix.vecMulVec_apply,Matrix.sum_apply,Matrix.one_apply,
    EuclideanSpace.inner_single_right,PiLp.single_apply,mul_comm,eq_comm] using t

theorem ip_inner (v w : Space 6) : star (⇑v : V) ⬝ᵥ (⇑w : V)=inner ℂ v w := by
  simp [PiLp.inner_apply,dotProduct,mul_comm]

theorem basis_mul (B : B6) (i j : Fin 6) :
    proj (B i)*proj (B j)=if i=j then proj (B i) else 0 := by
  rw [proj,proj,Matrix.vecMulVec_mul_vecMulVec]
  rw [ip_inner,B.inner_eq_ite]
  by_cases h : i=j <;> simp [h]

theorem proj_herm (v : Space 6) : (proj v)ᴴ=proj v := by
  ext i j
  simp [proj,Matrix.vecMulVec_apply,Matrix.conjTranspose_apply,mul_comm]

theorem basis_trace (B : B6) (i : Fin 6) : (proj (B i)).trace=1 := by
  have h := (ip_inner (B i) (B i)).trans (B.inner_eq_ite i i)
  simpa [proj,Matrix.vecMulVec_apply,Matrix.trace,Matrix.diag,dotProduct,mul_comm] using h

structure Model where
  p : Idx → Idx → M
  herm : ∀ r c, (p r c)ᴴ=p r c
  idem : ∀ r c, p r c*p r c=p r c
  trace : ∀ r c, (p r c).trace=1
  row : ∀ r, ∑ c, p r c=1
  col : ∀ c, ∑ r, p r c=1
  main : ∑ r, p r r=1
  anti : ∑ r : Idx, p r (r.1,r.2.rev)=1
  rowOrth : ∀ r c d, c≠d → p r c*p r d=0
  colOrth : ∀ c r s, r≠s → p r c*p s c=0
  mainOrth : ∀ r s, r≠s → p r r*p s s=0
  antiOrth : ∀ r s : Idx, r≠s → p r (r.1,r.2.rev)*p s (s.1,s.2.rev)=0
  rankOne : ∀ r c, ∃ v : Space 6, p r c=proj v

theorem sum_ord (f : Fin 6 → M) : ∑ x : Idx, f (ord x)=∑ i, f i :=
  Equiv.sum_comp ord f

def toModel (v : Cell 6 → Space 6)
    (rows : ∀ i, IsBasisLine v (fun j => (i,j)))
    (cols : ∀ j, IsBasisLine v (fun i => (i,j)))
    (main : IsBasisLine v (mainDiag 6)) (anti : IsBasisLine v (antiDiag 6)) : Model := by
  let p := fun r c : Idx => proj (v (ord r,ord c))
  have total {l} (hl : IsBasisLine v l) : ∑ x : Idx, proj (v (l (ord x)))=1 := by
    rw [sum_ord (fun i => proj (v (l i)))]
    obtain ⟨B,h⟩ := hl
    simpa only [h] using basis_sum B
  have orth {l} (hl : IsBasisLine v l) (x y : Idx) (hne : x≠y) :
      proj (v (l (ord x)))*proj (v (l (ord y)))=0 := by
    obtain ⟨B,h⟩ := hl
    have hc : ord x≠ord y := fun e => hne (ord.injective e)
    simpa only [h,if_neg hc] using basis_mul B (ord x) (ord y)
  refine ⟨p,fun r c => proj_herm _,?_,?_,fun r => total (rows (ord r)),
    fun c => total (cols (ord c)),total main,?_,fun r => orth (rows (ord r)),
    fun c => orth (cols (ord c)),orth main,?_,fun r c => ⟨_,rfl⟩⟩
  · intro r c
    obtain ⟨B,h⟩ := rows (ord r)
    simpa [p,h] using basis_mul B (ord c) (ord c)
  · intro r c
    obtain ⟨B,h⟩ := rows (ord r)
    simpa [p,h] using basis_trace B (ord c)
  · simpa [p,antiDiag,ord_rev] using total anti
  · intro r s h
    simpa [p,antiDiag,ord_rev] using orth anti r s h

@[simp] theorem toModel_p (v rows cols main anti r c) :
    (toModel v rows cols main anti).p r c=proj (v (ord r,ord c)) := rfl

end DiagonalSix
