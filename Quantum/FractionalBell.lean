module
public import Quantum.FractionalBellGeometry

/-! A fixed product grid attaining the pure-state and generalized-readout
bounds, including their endpoints. -/
@[expose] public section
noncomputable section
namespace FractionalBell
open QuantumCertificate FractionalBinary FractionalPositive FractionalProjectors
  FractionalTensor FractionalCorrelations FractionalSettings Complex Matrix Finset
open scoped ComplexConjugate ComplexOrder Matrix BigOperators

/-- The exponent of i for a local signed equatorial eigenvector at the site. -/
def localPowers (q : Site) : Fin 4 × Fin 4 :=
  let x := q.1.val / 2
  let y := q.2.val / 2
  let flip := (x+y)%2
  (⟨(x+2*((q.1.val+flip)%2))%4,by omega⟩,⟨(y+2*((q.2.val+flip)%2))%4,by omega⟩)

def fourth : Fin 4 → IQ := ![(1,0),(0,1),(-1,0),(0,-1)]
def fixedCoeff (q : Site) (k : Fin 4) : IQ :=
  let (x,y) := localPowers q
  fourth (![0,y,x,x+y] k)

def fixedGrid (q : Site) := vector 1 4 (fixedCoeff q)

theorem fixed_is_grid : Grid fixedGrid := by
  intro l
  exact basis_of_test (by decide : 0<4) _ ((by decide +kernel :
    ∀ l, GramTest 1 4 (fun k => fixedCoeff (line l k))) l)

theorem fixed_apply (q : Site) (k : Fin 4) :
    fixedGrid q k=(1/2:ℂ)*embed 1 (fixedCoeff q k) := by
  norm_num [fixedGrid,vector]

def pureState (a b : ℝ) : Space 4 := WithLp.toLp 2 ![(a:ℂ),0,0,(b:ℂ)*(1+I)]

theorem pure_norm (a b : ℝ) (h : a^2+2*b^2=1) : ‖pureState a b‖=1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [←inner_self_eq_norm_sq (𝕜:=ℂ),←ip_inner]
  norm_num [pureState,ip,dotProduct,Fin.sum_univ_four,Complex.mul_re,Complex.mul_im]
  nlinarith

theorem pure_born (a b t : ℝ) (h : a^2+2*b^2=1) (ht : 2*a*b=t) (q : Site) :
    normSq (inner ℂ (pureState a b) (fixedGrid q))=(1+t*mask q)/4 := by
  rcases q with ⟨i,j⟩
  rw [←ip_inner]
  fin_cases i <;> fin_cases j <;>
    norm_num [pureState,ip,dotProduct,Fin.sum_univ_four,fixed_apply,fixedCoeff,localPowers,fourth,
      embed,mask,pattern,Complex.normSq_apply,Complex.mul_re,Complex.mul_im] <;> nlinarith

theorem pure_coefficients (t : ℝ) (h : 2*t^2≤1) :
    ∃ a b : ℝ, a^2+2*b^2=1 ∧ 2*a*b=t := by
  let s := Real.sqrt (1-2*t^2)
  have hs : s^2=1-2*t^2 := Real.sq_sqrt (by linarith)
  have hs0 : 0≤s := Real.sqrt_nonneg _
  let a := Real.sqrt ((1+s)/2)
  have ha : a^2=(1+s)/2 := Real.sq_sqrt (by linarith)
  have hap : a≠0 := ne_of_gt (Real.sqrt_pos.mpr (by linarith))
  have hp : 2*a^2*a^2-2*a^2+t^2=0 := by rw [ha]; nlinarith only [hs]
  refine ⟨a,t/(2*a),?_,?_⟩
  · field_simp [hap]
    nlinarith only [hp]
  · field_simp

theorem fixed_separate {t : ℝ} (h : 2*t^2≤1) :
    ∀ k, ∃ f : Space 4, ‖f‖=1 ∧ ∀ q, normSq (inner ℂ f (fixedGrid q))=family t q k := by
  intro k
  have hs : (weightSign k)^2=1 := by fin_cases k <;> norm_num [weightSign]
  have ht : 2*(t*weightSign k)^2≤1 := by simpa [mul_pow,hs] using h
  obtain ⟨a,b,hab,hprod⟩ := pure_coefficients _ ht
  refine ⟨pureState a b,pure_norm _ _ hab,fun q => ?_⟩
  rw [pure_born _ _ _ hab hprod,family_apply]
  ring

def witness (t r : ℝ) : M :=
  !![(r:ℂ),0,0,2*(t:ℂ)*(1-I); 0,1,0,0; 0,0,-1,0; 2*(t:ℂ)*(1+I),0,0,-(r:ℂ)]

theorem witness_hermitian (t r : ℝ) : (witness t r)ᴴ=witness t r := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [witness,Matrix.conjTranspose_apply,Complex.mul_re,Complex.mul_im]

theorem witness_square (t r : ℝ) (h : r^2+8*t^2=1) : witness t r*witness t r=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [witness,Matrix.mul_apply,Fin.sum_univ_four,Matrix.one_apply,
      Complex.mul_re,Complex.mul_im] <;> nlinarith

theorem witness_born (t r : ℝ) (q : Site) :
    expectation (⇑(fixedGrid q)) (witness t r)=t*mask q := by
  rcases q with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [expectation,ip,Matrix.mulVec,dotProduct,Fin.sum_univ_four,witness,fixed_apply,
      fixedCoeff,localPowers,fourth,embed,mask,pattern,Complex.mul_re,Complex.mul_im] <;> ring

def splitEffect (H : M) (k : Fin 4) : M :=
  (1/4:ℝ) • (if k.val<2 then 1+H else 1-H)

theorem split_pos {H : M} (herm : Hᴴ=H) (square : H*H=1) (k : Fin 4) :
    (splitEffect H k).PosSemidef := by
  have aux (X : M) (hx : Xᴴ=X) (hh : X*X=X+X) : ((1/4:ℝ) • X).PosSemidef := by
    have he : (1/8:ℝ) • (Xᴴ*X)=(1/4:ℝ) • X := by rw [hx,hh]; module
    exact he ▸ (Matrix.posSemidef_conjTranspose_mul_self X).smul (by norm_num)
  unfold splitEffect
  split
  · apply aux _ (by simp [herm]); noncomm_ring [square]
  · apply aux _ (by simp [herm]); noncomm_ring [square]

theorem split_sum (H : M) : ∑ k, splitEffect H k=1 := by
  norm_num [Fin.sum_univ_four,splitEffect]
  module

theorem exp_smul (v : V) (r : ℝ) (H : M) : expectation v (r • H)=r*expectation v H := by
  simp [expectation,ip,Matrix.mulVec,dotProduct,Fin.sum_univ_four,Complex.mul_re,
    Complex.mul_im]
  ring

theorem fixed_generalized {t : ℝ} (h : 8*t^2≤1) : Generalized (family t) := by
  let r := Real.sqrt (1-8*t^2)
  have hr : r^2=1-8*t^2 := Real.sq_sqrt (by linarith)
  let H := witness t r
  refine ⟨fixedGrid,splitEffect H,fixed_is_grid,
    split_pos (witness_hermitian t r) (witness_square t r (by linarith)),split_sum H,?_⟩
  intro q k
  have hu : expectation (⇑(fixedGrid q)) 1=1 := by
    simp only [expectation,Matrix.one_mulVec,unit_ip (norm_grid fixed_is_grid q),Complex.one_re]
  rw [family_apply,splitEffect,exp_smul]
  fin_cases k <;> norm_num [exp_add,exp_sub,H,witness_born,hu,weightSign] <;> ring

/-- The four separate pure-outcome tables are attainable on a common
SudoQ exactly up to the single-outcome Bell radius. -/
theorem separate_iff (t : ℝ) : Separate (family t) ↔ 2*t^2≤1 :=
  ⟨separate_bound,fun h => ⟨fixedGrid,fixed_is_grid,fixed_separate h⟩⟩

/-- A genuine shared four-outcome POVM on a genuine SudoQ has precisely
half the separate-outcome radius for this line. -/
theorem generalized_iff (t : ℝ) : Generalized (family t) ↔ 8*t^2≤1 :=
  ⟨generalized_bound,fixed_generalized⟩

theorem projective_iff (t : ℝ) : ArbitraryMeasurement (family t) ↔ t=0 := by
  rw [family,FractionalNoisy.realizes_iff]
  constructor <;> intro h <;> linarith

#print axioms separate_iff
#print axioms generalized_iff
#print axioms projective_iff
end FractionalBell

