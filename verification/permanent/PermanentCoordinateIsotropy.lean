import PermanentGenericFrame
import PermanentGridWeights
import QuinticIsotropicDirections
import RationalIsotropicSpecialization

/-! Generic and specialized isotropic subspaces in a padded coordinate frame. -/

noncomputable section
open Matrix Module Polynomial QuinticPencil
namespace PermanentFive
variable {K n I : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]
  [Fintype I] [DecidableEq I]

theorem normalized_frame_isotropy_weighted (weights : GridWeights) (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (S : Finset Cell)
    (card : S.card = finrank K (endpoints b c).ker)
    (lift : ∀ z : Cell → K, ∃ x ∈ (endpoints b c).ker, ∀ i ∈ S, x i = z i)
    (paths : PermanentDegeneration.HasCoordinatePaths (endpoints b c).ker weights.cell S)
    (v : I → Cell) (cover : ∀ j ∈ S, ∃ i, v i = j) (y : Cell → K[X]) :
    ∃ Q : I → Cell → K[X],
      (∀ i j, firstJet K (Q i j) = (Pi.single (v i) 1 : Cell → DualNumber K) j) ∧
      ∃ W : Submodule (RatFunc K) (I → RatFunc K), 25 ≤ finrank (RatFunc K) W + Fintype.card n ∧
        W ≤ ((algebraMap K[X] (RatFunc K)).mapMatrix (frameHessian y Q)).toBilin'.orthogonal W := by
  classical
  obtain ⟨Q,atJet,spans⟩ := padded_generic_frame_weighted weights.cell b c S card lift paths v cover
  let f := algebraMap K[X] (RatFunc K)
  let τ := f X
  let g (j : Cell) := τ^(2*weights.cell j)
  have nt : τ ≠ 0 := fun h ↦ Polynomial.X_ne_zero (RatFunc.algebraMap_injective K (h.trans f.map_zero.symm))
  have ng (j : Cell) : g j ≠ 0 := pow_ne_zero _ nt
  let centre (j : Cell) := f (y j) / g j
  let u (i : I) (j : Cell) := f (Q i j) / g j
  let H := (hessian (per (RatFunc K) Idx) centre).toBilin'
  have norm := congrArg (MvPolynomial.map (algebraMap K (RatFunc K))) rep
  rw [mapped_permanent,mapped_regular_det] at norm
  obtain ⟨J,inKer,dim,iso⟩ := normalized_isotropic_directions (per_homogeneous (RatFunc K) Idx) _ _ _ norm centre
  let F := (Pi.basisFun (RatFunc K) I).constr (RatFunc K) u
  let W := J.comap F
  have onto : J ≤ F.range := inKer.trans (spans.trans (Submodule.span_le.mpr (by
    rintro _ ⟨i,rfl⟩
    exact ⟨(Pi.basisFun (RatFunc K) I) i,(Pi.basisFun (RatFunc K) I).constr_basis _ u i⟩)))
  have dw := Submodule.finrank_map_le F W
  rw [show W.map F = J from Submodule.map_comap_eq_self onto] at dw
  change 25 ≤ _ at dim
  refine ⟨Q,atJet,W,dim.trans (Nat.add_le_add_right dw _),?_⟩
  obtain ⟨a,law⟩ := weights.twist_character (τ^2)
  have scale : twist g (per (RatFunc K) Idx) = MvPolynomial.C a * per (RatFunc K) Idx := by
    simpa only [g,pow_mul] using law
  have cy : (fun j ↦ g j*centre j) = f ∘ y := by
    funext j
    dsimp [centre]
    field_simp [ng]
  have cu (i : I) : (fun j ↦ g j*u i j) = f ∘ Q i := by
    funext j
    dsimp [u]
    field_simp [ng]
  have gram : f.mapMatrix (frameHessian y Q) = a • (H.comp F F).toMatrix' := by
    rw [frameHessian_map]
    ext i j
    rw [frameHessian_pairing]
    have h := scaled_hessian_bilin scale centre (u i) (u j)
    rw [cy,cu,cu] at h
    have fv (k : I) : F (Pi.single k 1) = u k := by
      simpa only [Pi.basisFun_apply,F] using (Pi.basisFun (RatFunc K) I).constr_basis _ u k
    simpa only [Matrix.smul_apply,smul_eq_mul,LinearMap.BilinForm.toMatrix'_apply,
      LinearMap.BilinForm.comp_apply,fv] using h
  change W ≤ (f.mapMatrix (frameHessian y Q)).toBilin'.orthogonal W
  rw [gram,map_smul,Matrix.toBilin'_toMatrix']
  intro x hx z hz
  change a * H (F z) (F x) = 0
  rw [show H (F z) (F x) = 0 from iso hx _ hz,mul_zero]

theorem normalized_frame_isotropy (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (S : Finset Cell)
    (card : S.card = finrank K (endpoints b c).ker)
    (lift : ∀ z : Cell → K, ∃ x ∈ (endpoints b c).ker, ∀ i ∈ S, x i = z i)
    (paths : PermanentDegeneration.HasCoordinatePaths (endpoints b c).ker weight S)
    (v : I → Cell) (cover : ∀ j ∈ S, ∃ i, v i = j) (y : Cell → K[X]) :
    ∃ Q : I → Cell → K[X],
      (∀ i j, firstJet K (Q i j) = (Pi.single (v i) 1 : Cell → DualNumber K) j) ∧
      ∃ W : Submodule (RatFunc K) (I → RatFunc K), 25 ≤ finrank (RatFunc K) W + Fintype.card n ∧
        W ≤ ((algebraMap K[X] (RatFunc K)).mapMatrix (frameHessian y Q)).toBilin'.orthogonal W := by
  exact normalized_frame_isotropy_weighted standardGridWeights b c D rep S card lift paths v cover y

theorem coordinate_frame_isotropy_weighted (weights : GridWeights) (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (S : Finset Cell)
    (card : S.card = finrank K (endpoints b c).ker)
    (lift : ∀ z : Cell → K, ∃ x ∈ (endpoints b c).ker, ∀ i ∈ S, x i = z i)
    (paths : PermanentDegeneration.HasCoordinatePaths (endpoints b c).ker weights.cell S)
    (v : I → Cell) (cover : ∀ j ∈ S, ∃ i, v i = j) (z : Cell → K) :
    ∃ V : Submodule K (I → K), 25 ≤ finrank K V + Fintype.card n ∧
      V ≤ ((hessian (per K Idx) z).submatrix v v).toBilin'.orthogonal V := by
  classical
  obtain ⟨Q,atJet,W,dim,iso⟩ := normalized_frame_isotropy_weighted weights b c D rep S card lift paths v cover (C ∘ z)
  let e := evalRingHom (0 : K)
  have ez : e ∘ C ∘ z = z := by ext j; simp [e]
  have eq : (fun i ↦ e ∘ Q i) = fun i ↦ Pi.single (v i) (1 : K) := by
    funext i j
    have h := congrArg TrivSqZeroExt.fst (atJet i j)
    rw [(firstJet_components (Q i j)).1,coeff_zero_eq_eval_zero] at h
    by_cases same : j = v i <;> simpa [e,same] using h
  obtain ⟨V,dv,orth⟩ := RationalSpecialization.specialize_isotropic_plane (frameHessian (C ∘ z) Q)
    (finrank (RatFunc K) W) W le_rfl iso
  refine ⟨V,by omega,?_⟩
  change V ≤ (e.mapMatrix (frameHessian (C ∘ z) Q)).toBilin'.orthogonal V at orth
  rw [frameHessian_map,ez,eq,frameHessian_units] at orth
  exact orth

theorem coordinate_frame_isotropy (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (S : Finset Cell)
    (card : S.card = finrank K (endpoints b c).ker)
    (lift : ∀ z : Cell → K, ∃ x ∈ (endpoints b c).ker, ∀ i ∈ S, x i = z i)
    (paths : PermanentDegeneration.HasCoordinatePaths (endpoints b c).ker weight S)
    (v : I → Cell) (cover : ∀ j ∈ S, ∃ i, v i = j) (z : Cell → K) :
    ∃ V : Submodule K (I → K), 25 ≤ finrank K V + Fintype.card n ∧
      V ≤ ((hessian (per K Idx) z).submatrix v v).toBilin'.orthogonal V := by
  exact coordinate_frame_isotropy_weighted standardGridWeights b c D rep S card lift paths v cover z

#print axioms coordinate_frame_isotropy
end PermanentFive
