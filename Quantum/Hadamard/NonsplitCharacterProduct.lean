import Quantum.Hadamard.NonsplitGauss
import Quantum.Hadamard.LinPhoaCharacterProduct
import Quantum.Hadamard.ConferencePrincipalDet

/-! The complete determinant in the character basis of the norm-one torus. -/

noncomputable section
open Finset Matrix Hadamard.ProjectiveSigning Hadamard.ProjectiveSigning.Coordinates Hadamard.LinPhoa
open Hadamard.DeterminantRatio (completionSign)
namespace Hadamard.NonsplitTorus
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {d : F} [Fact (¬IsSquare d)]

private def sides (m : ℕ) : (Fin m⊕Fin m) ≃ Bool×Fin m where
  toFun := Sum.elim (fun i ↦ (false,i)) (fun i ↦ (true,i))
  invFun p := if p.1 then Sum.inr p.2 else Sum.inl p.2
  left_inv s := by cases s <;> rfl
  right_inv p := by rcases p with ⟨b,i⟩; cases b <;> rfl

private def base (h : (Ext d)ˣ) [NeZero (orderOf h)] :
    Matrix (Bool×Fin (orderOf h)) (Bool×Fin (orderOf h)) ℝ :=
  Matrix.of fun i j ↦ (cyclicEntry h i j:ℝ)

private theorem base_properties (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (hm : quadraticChar F (-1)=1) (h : (Ext d)ˣ) [NeZero (orderOf h)]
    (ho : orderOf h=(Fintype.card F+1)/2) (hn : (h:Ext d).norm=1) :
    (base h).IsHermitian ∧ base h*base h=(Fintype.card F:ℝ) • 1 ∧ ∀ i, base h i i=0 := by
  let E := Equiv.ofBijective _ (projective_chart_bijective q4 hm h ho hn)
  let U (i : Bool×Fin (orderOf h)) : ℝ := (quadraticChar F (scale (vector h i).re (vector h i).im):ℤ)
  have unit (i) : U i=1 ∨ U i= -1 := by
    have nz : vector h i≠0 := by
      rcases i with ⟨b,k⟩
      apply mul_ne_zero _ (pow_ne_zero _ h.ne_zero)
      cases b
      · exact one_ne_zero
      · intro eq; exact one_ne_zero (congrArg QuadraticAlgebra.im eq)
    have sn := scale_ne (u:=(vector h i).re) (v:=(vector h i).im)
      (by by_contra! eq; exact nz (QuadraticAlgebra.ext eq.1 eq.2))
    dsimp [U]
    exact_mod_cast quadraticChar_dichotomy sn
  have ent (i j) : base h i j=U i*U j*realPaley (E i) (E j) := by
    dsimp [base,U,E,realPaley]
    exact_mod_cast (cyclic_wedge hm h hn i j).symm.trans (wedge_chart hm _ _)
  obtain ⟨sy,sq,zero,_⟩ := realPaley_properties hc q4
  refine ⟨?_,?_,fun i ↦ by rw [ent,zero,mul_zero]⟩
  · ext i j
    change base h j i=base h i j
    rw [ent,ent]
    have eq : realPaley (E j) (E i)=realPaley (E i) (E j) := sy.apply _ _
    rw [eq]; ring
  · ext i j
    have eq : (base h*base h) i j=U i*U j*((realPaley (F:=F)*realPaley : Matrix (Option F) (Option F) ℝ)) (E i) (E j) := by
      rw [Matrix.mul_apply,Matrix.mul_apply,←Equiv.sum_comp E (fun k ↦ realPaley (E i) k*realPaley k (E j)),mul_sum]
      apply sum_congr rfl
      intro k _
      rw [ent,ent]
      rcases unit k with a|a <;> rw [a] <;> ring
    rw [eq,sq]
    simp only [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Equiv.apply_eq_iff_eq]
    by_cases same : i=j
    · subst j; rcases unit i with a|a <;> simp [a]
    · simp [same]

def torusGram (h : (Ext d)ˣ) [NeZero (orderOf h)] (α : ℤ) :
    Matrix (Fin (orderOf h)) (Fin (orderOf h)) ℝ :=
  ((Fintype.card F:ℝ)+1) • 1 + (2*(α:ℝ)) • Matrix.of (fun k l ↦ (quadraticChar F (spin h (l-k)).im:ℝ))

/-- The absolute determinant on both torus cosets reduces to the determinant
of the single cyclic matrix with entries n times delta plus 2 alpha chi(y). -/
theorem torus_principal_det (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (hm : quadraticChar F (-1)=1) (h : (Ext d)ˣ) [NeZero (orderOf h)]
    (ho : orderOf h=(Fintype.card F+1)/2) (hn : (h:Ext d).norm=1) (α : ℤ) (sign : α^2=1) :
    |(twoCirculant h α).det|=(torusGram h α).det := by
  let e := sides (orderOf h)
  let R := (base h).submatrix e e
  let C := (α:ℝ) • R
  let D := diagonal (completionSign (I:=Fin (orderOf h)) (J:=Fin (orderOf h)))
  have ar : (α:ℝ)*(α:ℝ)=1 := by exact_mod_cast (show α*α=1 by simpa [pow_two] using sign)
  have ab : |(α:ℝ)|=1 := by rcases sq_eq_one_iff.mp sign with a|a <;> simp [a]
  obtain ⟨sy,sq,zero⟩ := base_properties hc q4 hm h ho hn
  have cs : C.IsHermitian := (sy.submatrix e).smul (isSelfAdjoint_iff.mpr (by rfl) : IsSelfAdjoint (α:ℝ))
  have cq : C*C=(Fintype.card F:ℝ) • 1 := by
    dsimp [C,R]
    rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,ar,one_smul,submatrix_mul_equiv,sq]
    change (Fintype.card F:ℝ) • ((1 : Matrix _ _ ℝ).submatrix e e)=_
    rw [submatrix_one_equiv]
  have ct : C.trace=0 := by simp [C,R,Matrix.trace,Matrix.diag,Matrix.smul_apply,Matrix.submatrix_apply,zero]
  have qpos : (1:ℝ)<Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  have pp := Hadamard.ConferenceAverage.balanced_principal_det C (orderOf h) (Fintype.card F)
    (Fintype.card_fin _) (Fintype.card_fin _) qpos cs cq ct
  have mat : (twoCirculant h α).submatrix e e=R+(α:ℝ) • D := by
    ext i j
    simp only [twoCirculant,R,base,Matrix.submatrix_apply,Matrix.add_apply,Matrix.of_apply]
    congr 1
    simp only [D,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,Equiv.apply_eq_iff_eq]
    by_cases eq : i=j
    · subst j; cases i <;> simp [completionSign,e,sides]
    · simp [eq]
  have mult : C+D=(α:ℝ) • (twoCirculant h α).submatrix e e := by rw [mat,smul_add,smul_smul,ar,one_smul]
  change |(C+D).det|=_ at pp
  rw [mult,det_smul,det_submatrix_equiv_self,abs_mul,abs_pow,ab,one_pow,one_mul] at pp
  rw [pp]
  congr 1
  ext i j
  simp [torusGram,C,R,e,sides,base,cyclicEntry,Matrix.smul_apply,smul_eq_mul,Matrix.add_apply,Matrix.submatrix_apply]
  ring

#print axioms torus_principal_det

noncomputable local instance (d : F) : Fintype (Ext d) :=
  Fintype.ofEquiv (F×F) (QuadraticAlgebra.equivProd d 0).symm

def torusSymbol (h : (Ext d)ˣ) [NeZero (orderOf h)] (θ : AddChar (Fin (orderOf h)) ℂ) : ℂ :=
  ∑ i : Fin (orderOf h), θ i*eta F (spin h i).im

/-- All torus characters occur, including the trivial character. -/
theorem torus_character_product (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (hm : quadraticChar F (-1)=1) (h : (Ext d)ˣ) [NeZero (orderOf h)]
    (ho : orderOf h=(Fintype.card F+1)/2) (hn : (h:Ext d).norm=1) (α : ℤ) (sign : α^2=1) :
    ((|(twoCirculant h α).det|:ℝ):ℂ)=
      ∏ θ : AddChar (Fin (orderOf h)) ℂ, ((Fintype.card F:ℂ)+1+2*(α:ℂ)*torusSymbol h θ) := by
  rw [torus_principal_det hc q4 hm h ho hn α sign]
  change Complex.ofRealHom (torusGram h α).det=_
  rw [RingHom.map_det]
  apply det_in_characters
  intro θ
  funext k
  change (∑ l, ((torusGram h α k l:ℝ):ℂ)*θ l)=_*θ k
  have coeff (l : Fin (orderOf h)) : ((torusGram h α k l : ℝ):ℂ)=
      (if k=l then (Fintype.card F:ℂ)+1 else 0)+2*(α:ℂ)*eta F (spin h (l-k)).im := by
    change ((torusGram h α k l : ℝ):ℂ)=_+2*(α:ℂ)*(quadraticChar F (spin h (l-k)).im:ℂ)
    by_cases eq : k=l <;> simp [torusGram,Matrix.add_apply,Matrix.smul_apply,eq]
  have cr (l : Fin (orderOf h)) : θ l=θ (l-k)*θ k := by rw [←θ.map_add_eq_mul,sub_add_cancel]
  have shift : (∑ l : Fin (orderOf h), θ (l-k)*eta F (spin h (l-k)).im)=torusSymbol h θ :=
    Equiv.sum_comp (Equiv.subRight k) (fun l ↦ θ l*eta F (spin h l).im)
  simp only [coeff,add_mul,sum_add_distrib,ite_mul,zero_mul,sum_ite_eq,mem_univ,ite_true]
  have term (l : Fin (orderOf h)) : 2*(α:ℂ)*eta F (spin h (l-k)).im*θ l=
      (2*(α:ℂ)*θ k)*(θ (l-k)*eta F (spin h (l-k)).im) := by
    rw [cr l]; ring
  rw [show (∑ l : Fin (orderOf h), 2*(α:ℂ)*eta F (spin h (l-k)).im*θ l)=
      (2*(α:ℂ)*θ k)*torusSymbol h θ by simp only [term,←mul_sum,shift]]
  ring

/-- Twice the Fourier coefficient, expressed only through ordinary Gauss sums. -/
def gaussCorrection (Ω : MulChar (Ext d) ℂ) (ψ : AddChar F ℂ) : ℂ :=
  Ω (twiceRoot d)*(gaussSum Ω (traceCharacter ψ)-gaussSum (Ω*eta (Ext d)) (traceCharacter ψ))/
    gaussSum (eta F) ψ

/-- Each determinant is an exact product of Gauss differences. Both
orientations use the same extensions and the same additive character. -/
theorem exists_torus_gauss_product (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (hm : quadraticChar F (-1)=1) (h : (Ext d)ˣ) [NeZero (orderOf h)]
    (ho : orderOf h=(Fintype.card F+1)/2) (hn : (h:Ext d).norm=1) :
    ∃ Ω : AddChar (Fin (orderOf h)) ℂ → MulChar (Ext d) ℂ,
      (∀ θ s, Ω θ (algebraMap F (Ext d) s)=eta F s) ∧ (∀ θ i, Ω θ (spin h i)=θ i) ∧
      (∀ θ, (Ω θ (twiceRoot d))^2= -1) ∧
      ∀ (ψ : AddChar F ℂ), ψ.IsPrimitive → ∀ α : ℤ, α^2=1 →
        ((|(twoCirculant h α).det|:ℝ):ℂ)=∏ θ : AddChar (Fin (orderOf h)) ℂ,
          ((Fintype.card F:ℂ)+1+(α:ℂ)*gaussCorrection (Ω θ) ψ) := by
  choose Ω restricts spins phase diff using exists_torus_gauss_pair hc q4 hm h ho hn
  refine ⟨Ω,restricts,spins,phase,fun ψ prim α sign ↦ ?_⟩
  have ne : eta F≠1 := (MulChar.ringHomComp_ne_one_iff
      (by exact_mod_cast (Int.cast_injective (α:=ℂ)))).mpr (quadraticChar_ne_one hc)
  have gn : gaussSum (eta F) ψ≠0 := gaussSum_ne_zero_of_nontrivial
    (by exact_mod_cast Fintype.card_ne_zero (α:=F)) ne prim
  rw [torus_character_product hc q4 hm h ho hn α sign]
  apply prod_congr rfl
  intro θ _
  have eq : gaussCorrection (Ω θ) ψ=2*torusSymbol h θ := by
    apply (div_eq_iff gn).mpr
    rw [diff θ ψ]
    unfold torusSymbol
    ring
  rw [eq]; ring

#print axioms torus_character_product
#print axioms exists_torus_gauss_product

end Hadamard.NonsplitTorus
