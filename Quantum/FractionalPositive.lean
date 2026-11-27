module
public import Quantum.FractionalBinary

/-! A quantitative five-cycle obstruction and an everywhere-positive, locally
orthostochastic fractional Sudoku excluded for every global measurement basis. -/
@[expose] public section
noncomputable section
namespace FractionalPositive
open QuantumCertificate FractionalBinary Complex
open scoped ComplexConjugate BigOperators

def noisyWeight (ε : ℝ) (g : Bool) (a : Fin 4) : ℝ :=
  if a=first g ∨ a=second g then (1-ε)/2 else ε/2
def noisy (ε : ℝ) : Prob := fun x a => noisyWeight ε (pattern x) a

theorem pair_norm {a b : ℂ} {r : ℝ} (ha : normSq a=r) (hb : normSq b=r) :
    ‖a*conj b‖=r := by
  have h1 := (Complex.normSq_eq_norm_sq a).symm.trans ha
  have h2 := (Complex.normSq_eq_norm_sq b).symm.trans hb
  have eq : ‖a‖=‖b‖ := (sq_eq_sq₀ (norm_nonneg a) (norm_nonneg b)).mp (h1.trans h2.symm)
  rw [norm_mul,Complex.norm_conj,← eq,← sq,h1]

theorem two_norm_bound {v w : Space 4} {r s : ℝ} (hr : 0<r)
    (hv1 : normSq (v 1)=r) (hw0 : normSq (w 0)=r)
    (hv2 : normSq (v 2)=s) (hv3 : normSq (v 3)=s)
    (hw2 : normSq (w 2)=s) (hw3 : normSq (w 3)=s) (ho : inner ℂ v w=0) :
    ‖conj (v 0)*v 1+conj (w 0)*w 1‖≤2*s := by
  have hx : w 0*conj (w 0)=(r : ℂ) := by rw [Complex.mul_conj,hw0]
  have hy : v 1*conj (v 1)=(r : ℂ) := by rw [Complex.mul_conj,hv1]
  have he : (r : ℂ)*(conj (v 0)*v 1+conj (w 0)*w 1) =
      (conj (w 0)*v 1)*(w 0*conj (v 0)+w 1*conj (v 1)) := by
    linear_combination -(conj (v 0)*v 1)*hx - (conj (w 0)*w 1)*hy
  have he' := congrArg norm he
  have hfactor : ‖conj (w 0)*v 1‖=r := by rw [mul_comm]; exact pair_norm hv1 hw0
  rw [norm_mul,norm_mul (conj (w 0)*v 1),hfactor,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] at he'
  have hab := mul_left_cancel₀ hr.ne' he'
  have ho' := ho
  rw [PiLp.inner_apply,Fin.sum_univ_four] at ho'
  change w 0*conj (v 0)+w 1*conj (v 1)+w 2*conj (v 2)+w 3*conj (v 3)=0 at ho'
  have tail : w 0*conj (v 0)+w 1*conj (v 1) = -(w 2*conj (v 2)+w 3*conj (v 3)) := by
    linear_combination ho'
  rw [hab,tail,norm_neg]
  calc
    _ ≤ ‖w 2*conj (v 2)‖+‖w 3*conj (v 3)‖ := norm_add_le _ _
    _ = _ := by rw [pair_norm hw2 hv2,pair_norm hw3 hv3]; ring

theorem odd_five_bound (a b c d e : ℂ) :
    2*‖a‖ ≤ ‖a+b‖+‖b+c‖+‖c+d‖+‖d+e‖+‖e+a‖ := by
  have eq : (2 : ℂ)*a=(a+b)+(-(b+c))+(c+d)+(-(d+e))+(e+a) := by ring
  calc
    _ = ‖(2 : ℂ)*a‖ := by simp
    _ = _ := congrArg norm eq
    _ ≤ _ := by
      grw [norm_add_le,norm_add_le,norm_add_le,norm_add_le]
      simp only [norm_neg,le_refl]

theorem noise_lower_bound (ε : ℝ) (h : ArbitraryMeasurement (noisy ε)) : (1:ℝ)/6≤ε := by
  by_cases he : ε<1
  · obtain ⟨v,hg,hp⟩ := any_basis.mp h
    let phase (x : Site) := conj (v x 0)*v x 1
    have hi0 (x : Site) (hx : pattern x=true) : normSq (v x 0)=(1-ε)/2 := by
      simpa [noisy,noisyWeight,hx,first,second] using hp x 0
    have hi1 (x : Site) (hx : pattern x=true) : normSq (v x 1)=(1-ε)/2 := by
      simpa [noisy,noisyWeight,hx,first,second] using hp x 1
    have hi2 (x : Site) (hx : pattern x=true) : normSq (v x 2)=ε/2 := by
      simpa [noisy,noisyWeight,hx,first,second] using hp x 2
    have hi3 (x : Site) (hx : pattern x=true) : normSq (v x 3)=ε/2 := by
      simpa [noisy,noisyWeight,hx,first,second] using hp x 3
    have edge (l : Fin 12) (i j : Fin 4) (hij : i≠j)
        (hi : pattern (line l i)=true) (hj : pattern (line l j)=true) :
        ‖phase (line l i)+phase (line l j)‖≤ε := by
      obtain ⟨B,hB⟩ := hg l
      have ho : inner ℂ (v (line l i)) (v (line l j))=0 := by
        rw [←congrFun hB i,←congrFun hB j,B.inner_eq_ite]; simp [hij]
      have pt := two_norm_bound (by linarith : 0<(1-ε)/2)
        (hi1 _ hi) (hi0 _ hj)
        (hi2 _ hi) (hi3 _ hi) (hi2 _ hj) (hi3 _ hj) ho
      change ‖conj (v (line l i) 0)*v (line l i) 1+conj (v (line l j) 0)*v (line l j) 1‖≤ε
      linarith only [pt]
    have a : ‖phase (0,0)+phase (1,1)‖≤ε := edge 8 0 3 (by decide) (by decide) (by decide)
    have b : ‖phase (1,1)+phase (3,1)‖≤ε := edge 5 1 3 (by decide) (by decide) (by decide)
    have c : ‖phase (3,1)+phase (3,2)‖≤ε := edge 3 1 2 (by decide) (by decide) (by decide)
    have d : ‖phase (3,2)+phase (0,2)‖≤ε := edge 6 3 0 (by decide) (by decide) (by decide)
    have e : ‖phase (0,2)+phase (0,0)‖≤ε := edge 0 2 0 (by decide) (by decide) (by decide)
    have root : ‖phase (0,0)‖=(1-ε)/2 := by
      change ‖conj (v (0,0) 0)*v (0,0) 1‖=_
      rw [mul_comm]
      exact pair_norm (hi1 _ (by decide)) (hi0 _ (by decide))
    have bound := odd_five_bound (phase (0,0)) (phase (1,1)) (phase (3,1))
        (phase (3,2)) (phase (0,2))
    linarith
  · linarith

def positiveSigns : Fin 4 → Fin 4 → ℤ :=
  ![![3,3,1,1],![3,-3,1,-1],![1,1,-3,-3],![1,-1,-3,3]]
def positiveReps (i j : Fin 4) : IQ := (positiveSigns i j,0)

theorem positive_entries : ∀ x a, 0 < noisy (1/10) x a := by
  intro x a
  unfold noisy noisyWeight
  split <;> norm_num

theorem positive_local : LocallyOrthostochastic (noisy (1/10)) := by
  obtain ⟨B,hB⟩ := basis_of_test (by decide : 0<20) (v:=positiveReps)
    (by decide +kernel : GramTest 1 20 positiveReps)
  have wt (g s : Bool) (a : Fin 4) : (B (label g s) a).im=0 ∧
      Complex.normSq (B (label g s) a)=noisyWeight (1/10) g a := by
    rw [congrFun hB (label g s)]
    have hs : (Real.sqrt 20)^2=20 := Real.sq_sqrt (by norm_num)
    cases g <;> cases s <;> fin_cases a <;>
      norm_num [vector,positiveReps,positiveSigns,label,first,second,embed,noisyWeight,
        Complex.mul_re,Complex.mul_im,Complex.normSq_apply,Complex.inv_re,Complex.inv_im,
        mul_pow,←sq] <;> nlinarith only [hs]
  intro l
  obtain ⟨e,he⟩ := (by decide +kernel :
    ∀ l, ∃ f : Fin 4 → Fin 4, Function.Injective f ∧
      ∀ i, ∃ s : Bool, f i=label (pattern (line l i)) s) l
  let equiv := Equiv.ofBijective e ((Finite.injective_iff_bijective).mp he.1)
  refine ⟨B.reindex equiv.symm,fun i a => ?_⟩
  obtain ⟨s,hs⟩ := he.2 i
  rw [OrthonormalBasis.reindex_apply,Equiv.symm_symm]
  change ((B (e i)) a).im=0 ∧ normSq ((B (e i)) a) = _
  rw [hs]
  exact wt _ _ a

theorem positive_impossible : ¬ArbitraryMeasurement (noisy (1/10)) := by
  intro h
  have bad := noise_lower_bound _ h
  norm_num at bad

#print axioms noise_lower_bound
#print axioms positive_local
#print axioms positive_impossible
end FractionalPositive
