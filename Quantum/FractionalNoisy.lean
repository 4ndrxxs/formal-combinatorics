module
public import Quantum.FractionalSettings

/-! Every point of the noisy line is locally orthostochastic. The uniform
point is its unique global realization under an arbitrary complex measurement. -/
@[expose] public section
noncomputable section
namespace FractionalNoisy
open Complex Finset QuantumCertificate FractionalTensor FractionalSettings
open FractionalBinary FractionalPositive
open scoped ComplexConjugate BigOperators

def coefficients (a b : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![a,a,b,b],![a,-a,b,-b],![b,b,-a,-a],![b,-b,-a,a]]

def realVector (a b : ℝ) (i : Fin 4) : Space 4 :=
  WithLp.toLp 2 (fun j => (coefficients a b i j:ℂ))

theorem real_basis {a b : ℝ} (h : 2*a^2+2*b^2=1) :
    ∃ B : ONB, ⇑B=realVector a b := by
  have ho : Orthonormal ℂ (realVector a b) := by
    apply orthonormal_iff_ite.mpr
    intro i j
    rw [← FractionalProjectors.ip_inner]
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [realVector,coefficients,ip,dotProduct,Fin.sum_univ_four,
        Complex.mul_re,Complex.mul_im] <;> nlinarith
  exact ⟨OrthonormalBasis.mk ho
    (ho.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)).ge,
    OrthonormalBasis.coe_mk _ _⟩

theorem local_orthostochastic (ε : ℝ) (h0 : 0≤ε) (h1 : ε≤1) :
    LocallyOrthostochastic (noisy ε) := by
  let a := Real.sqrt ((1-ε)/2)
  let b := Real.sqrt (ε/2)
  have ha : a^2=(1-ε)/2 := Real.sq_sqrt (by linarith)
  have hb : b^2=ε/2 := Real.sq_sqrt (by linarith)
  obtain ⟨B,hB⟩ := real_basis (a:=a) (b:=b) (by linarith)
  have wt (g s : Bool) (i : Fin 4) : (B (label g s) i).im=0 ∧
      normSq (B (label g s) i)=noisyWeight ε g i := by
    rw [congrFun hB (label g s)]
    cases g <;> cases s <;> fin_cases i <;>
      norm_num [realVector,coefficients,label,first,second,noisyWeight,Complex.normSq_apply] <;>
      nlinarith
  intro l
  obtain ⟨f,hf⟩ := (by decide +kernel :
    ∀ l, ∃ f : Fin 4 → Fin 4, Function.Injective f ∧
      ∀ i, ∃ s : Bool, f i=label (pattern (line l i)) s) l
  let perm := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hf.1)
  refine ⟨B.reindex perm.symm,fun i j => ?_⟩
  obtain ⟨s,hs⟩ := hf.2 i
  rw [OrthonormalBasis.reindex_apply,Equiv.symm_symm]
  change (B (f i) j).im=0 ∧ normSq (B (f i) j)=_
  rw [hs]
  exact wt _ _ _

def classicalSymbol (p : Site) : Fin 4 :=
  (![![0,1,3,2],![2,3,1,0],![3,2,0,1],![1,0,2,3]] : Fin 4 → Fin 4 → Fin 4) p.1 p.2

theorem uniform : ArbitraryMeasurement (noisy (1/2)) := by
  obtain ⟨B,hB⟩ := real_basis (a:=1/2) (b:=1/2) (by norm_num)
  apply any_basis.mpr
  refine ⟨fun p => B (classicalSymbol p),?_,?_⟩
  · intro l
    let f := fun j => classicalSymbol (line l j)
    have inj : Function.Injective f :=
      (by decide +kernel : ∀ l, Function.Injective (fun j => classicalSymbol (line l j))) l
    let perm := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp inj)
    exact ⟨B.reindex perm.symm,funext fun j => by simp [perm,f]⟩
  · intro p a
    have w (k j : Fin 4) : normSq (B k j)=1/4 := by
      rw [congrFun hB k]
      fin_cases k <;> fin_cases j <;> norm_num [realVector,coefficients,Complex.normSq_apply]
    rw [w]
    unfold noisy noisyWeight
    split <;> norm_num

/-- A full arbitrary-basis iff, with no normal-form assumption or external
classification theorem in its hypotheses. -/
theorem realizes_iff (ε : ℝ) : ArbitraryMeasurement (noisy ε) ↔ ε=1/2 :=
  ⟨epsilon_of_quantum,fun h => h ▸ uniform⟩

#print axioms local_orthostochastic
#print axioms realizes_iff
end FractionalNoisy
