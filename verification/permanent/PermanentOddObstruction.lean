import PermanentGenericFrame
import QuinticIsotropicDirections
import QuinticSquareGram

/-! A simple zero of a twelve-coordinate Hessian determinant excludes a
size-twenty representation whose pivot support lies in those coordinates. -/

noncomputable section
open Matrix Module Polynomial QuinticPencil
namespace PermanentFive
variable {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]

theorem normalized_excludes_odd_block (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (small : Fintype.card n ≤ 19) (S : Finset Cell)
    (card : S.card = finrank K (endpoints b c).ker)
    (lift : ∀ z : Cell → K, ∃ x ∈ (endpoints b c).ker, ∀ i ∈ S, x i = z i)
    (paths : PermanentDegeneration.HasCoordinatePaths (endpoints b c).ker weight S) :
    ¬ HasOddBlock K S := by
  classical
  rintro ⟨v,Y,cover,zero,slope⟩
  obtain ⟨Q,atJet,spans⟩ := padded_generic_frame b c S card lift paths v cover
  let f := algebraMap K[X] (RatFunc K)
  let τ := f X
  let g (j : Cell) := τ^(2*weight j)
  have nt : τ ≠ 0 := fun h ↦ Polynomial.X_ne_zero (RatFunc.algebraMap_injective K (h.trans f.map_zero.symm))
  have ng (j : Cell) : g j ≠ 0 := pow_ne_zero _ nt
  let y (j : Cell) := liftJet (Y j)
  let centre (j : Cell) := f (y j) / g j
  let u (i : Fin 12) (j : Cell) := f (Q i j) / g j
  let H := (hessian (per (RatFunc K) Idx) centre).toBilin'
  let P := frameHessian y Q
  have norm := congrArg (MvPolynomial.map (algebraMap K (RatFunc K))) rep
  rw [mapped_permanent,mapped_regular_det] at norm
  have hom : (per (RatFunc K) Idx).IsHomogeneous 5 := per_homogeneous _ _
  obtain ⟨J,inKer,dim,iso⟩ := normalized_isotropic_directions hom _ _ _ norm centre
  have six : 6 ≤ finrank (RatFunc K) J := by change 25 ≤ _ at dim; omega
  have sym : H.IsSymm := by
    apply Matrix.isSymm_toBilin'_iff_isSymm.mpr
    ext i j
    change MvPolynomial.eval centre (MvPolynomial.pderiv j (MvPolynomial.pderiv i _)) = _
    rw [MvPolynomial.pderiv_comm j i]
    rfl
  have sq := gram_square_from_six H sym u (by decide) J six (inKer.trans spans) iso
  obtain ⟨a,law⟩ := weight_twist (τ^2)
  have scale : twist g (per (RatFunc K) Idx) = MvPolynomial.C a * per (RatFunc K) Idx := by
    simpa only [g,pow_mul] using law
  have cy : (fun j ↦ g j*centre j) = f ∘ y := by
    funext j
    dsimp [centre]
    field_simp [ng]
  have cu (i : Fin 12) : (fun j ↦ g j*u i j) = f ∘ Q i := by
    funext j
    dsimp [u]
    field_simp [ng]
  have eq : f.mapMatrix P = a • Matrix.of (fun i j ↦ H (u i) (u j)) := by
    rw [show P = frameHessian y Q from rfl,frameHessian_map]
    ext i j
    rw [frameHessian_pairing]
    have h := scaled_hessian_bilin scale centre (u i) (u j)
    rw [cy,cu,cu] at h
    exact h
  have square : IsSquare (f P.det) := by
    rw [RingHom.map_det,eq,Matrix.det_smul,Fintype.card_fin]
    exact IsSquare.mul ⟨a^6,by rw [← pow_add]⟩ sq
  have jY : firstJet K ∘ y = Y := funext fun j ↦ firstJet_lift (Y j)
  have jQ : (fun i ↦ firstJet K ∘ Q i) = (fun i ↦ Pi.single (v i) (1 : DualNumber K)) := by
    funext i j
    exact atJet i j
  have evaluated : firstJet K P.det = ((hessian (per (DualNumber K) Idx) Y).submatrix v v).det := by
    rw [RingHom.map_det,show P = frameHessian y Q from rfl,frameHessian_map,jY,jQ,frameHessian_units]
  exact jet_nonsquare P.det (by rw [evaluated]; exact zero) (by rw [evaluated]; exact slope) square

#print axioms normalized_excludes_odd_block
end PermanentFive
