import PermanentStarMinor

/-! Turning the corrected Hessian columns into smooth points over the ground field. -/
noncomputable section
open Matrix Finset MvPolynomial PermanentFive PermanentBorder PermanentJets PermanentCurve QuinticPencil PermanentSpecialization
namespace PermanentDeformation
variable {K J S : Type*} [Field K] [Fintype J] [DecidableEq J] [Fintype S] [DecidableEq S]

def HessPoly (K J : Type*) [Field K] [Fintype J] [DecidableEq J] :
    Matrix (Cells J) (Cells J) (Polynomial K) :=
  Matrix.of (fun i j ↦ subst (curve K J) (pderiv i (pderiv j (permP K J))))

theorem HessPoly_ev (t : K) : ev t (HessPoly K J)=hessian (permP K J) (Polynomial.eval t ∘ curve K J) := by
  ext i j
  exact subst_eval _ _ _

theorem HessPoly_base (two : (2:K)≠0) : ev 0 (HessPoly K J)=hessian (permP K J) (base K J) := by
  ext i j
  change Polynomial.eval 0 (subst _ _)=_
  rw [←Polynomial.coeff_zero_eq_eval_zero]
  exact (curve_taylor two (pderiv i (pderiv j (permP K J)))).1

def tests (K : Type*) [Field K] (f : S→J) : Matrix S (Cells J) K :=
  Matrix.of (fun i ↦ parameter (mode K (f i)))
def columns (K : Type*) [Field K] (f : S→J) : Matrix (Cells J) S (Polynomial K) :=
  Matrix.of (fun v j ↦ imageDiv (mode K (f j)) v)

omit [Fintype S] [DecidableEq S] in
theorem tests_kill (two : (2:K)≠0) (f : S→J) : tests K f * ev 0 (HessPoly K J)=0 := by
  rw [HessPoly_base two]
  ext i v
  have h := parameter_kernel (mode K (f i)) (mode_sum _) v
  simpa only [tests,Matrix.mul_apply,Matrix.of_apply,Matrix.zero_apply,atOne,dir_apply,
    map_sum,map_mul,eval_C,hessian,base] using h

theorem pairing [Nonempty J] (two : (2:K)≠0) (f : S↪J) :
    tests K f * ev 0 (columns K f)=gram K J S := by
  ext i j
  change (∑ v,parameter (mode K (f i)) v*Polynomial.eval 0 (imageDiv (mode K (f j)) v))=_
  simp_rw [←Polynomial.coeff_zero_eq_eval_zero]
  rw [image_reduced two _ _ (mode_sum _) (mode_sum _),mode_energy]
  simp [gram,eq_comm]

omit [Fintype S] [DecidableEq S] in
theorem columns_image (two : (2:K)≠0) (f : S→J) (t : K) (tnz : t≠0) :
    ∃ Z : Matrix (Cells J) S K,ev t (columns K f)=ev t (HessPoly K J)*Z := by
  let z (j : S) := parameter (mode K (f j))+t • correction (mode K (f j))
  refine ⟨Matrix.of (fun v j ↦ ((t^2)⁻¹ • z j) v),?_⟩
  ext v j
  change Polynomial.eval t (imageDiv (mode K (f j)) v)=
    (ev t (HessPoly K J) *ᵥ ((t^2)⁻¹ • z j)) v
  rw [HessPoly_ev,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul]
  have h := congrArg (Polynomial.eval t) (image_factor two (mode K (f j)) (mode_sum _) v)
  simp only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,image_eval] at h
  field_simp
  exact h

theorem attained_by_minor [Infinite K] [Nonempty J] (two : (2:K)≠0) (f : S↪J)
    (minor : (gram K J S).det≠0) :
    ∃ z : Cells J→K,PermanentBorder.value z=0 ∧ gradAt z corner≠0 ∧
      ((Fintype.card J+2)^2-(Fintype.card J+2)+2)+Fintype.card S≤(hessian (permP K J) z).rank := by
  have nz : (Polynomial.eval 0 (gradAt (tangentLine K J) corner))≠0 := by
    rw [←Polynomial.coeff_zero_eq_eval_zero,line_cofactor]
    exact one_ne_zero
  have det0 : (tests K f*ev 0 (columns K f)).det≠0 := by rw [pairing two f];exact minor
  obtain ⟨t,sm,r⟩ := rank_gain (HessPoly K J) (tests K f) (columns K f) _ nz
    (tests_kill two f) det0 (columns_image two f)
  refine ⟨Polynomial.eval t ∘ curve K J,curve_value t,by rwa [curve_grad],?_⟩
  rw [HessPoly_base two,HessPoly_ev] at r
  have baseRank := PermanentArrow.exact_rank two (none:Option (Option J))
    (by simp : 2≤Fintype.card (Option (Option J)))
  change (hessian (permP K J) (base K J)).rank=_ at baseRank
  rw [baseRank] at r
  simpa only [Fintype.card_option,Nat.add_assoc] using r

end PermanentDeformation
