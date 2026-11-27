import PermanentGenericFrame
import QuinticIsotropicDirections
import QuinticSignedGram

/-! A simple zero on an even-dimensional frame rules out a normalized pencil
whose universal isotropic directions fill at least half the frame. -/

noncomputable section
open Matrix Module Polynomial QuinticPencil
namespace PermanentFive
variable {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]

theorem normalized_excludes_simple_zero (d : ℕ) (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (small : Fintype.card n + d ≤ 25) (S : Finset Cell)
    (card : S.card = finrank K (endpoints b c).ker)
    (lift : ∀ z : Cell → K, ∃ x ∈ (endpoints b c).ker, ∀ i ∈ S, x i = z i)
    (paths : PermanentDegeneration.HasCoordinatePaths (endpoints b c).ker weight S) :
    ¬ HasSimpleZeroBlock K (2*d) S := by
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
  let u (i : Fin (2*d)) (j : Cell) := f (Q i j) / g j
  let H := (hessian (per (RatFunc K) Idx) centre).toBilin'
  let P := frameHessian y Q
  have norm := congrArg (MvPolynomial.map (algebraMap K (RatFunc K))) rep
  rw [mapped_permanent,mapped_regular_det] at norm
  have hom : (per (RatFunc K) Idx).IsHomogeneous 5 := per_homogeneous _ _
  obtain ⟨J,inKer,dim,iso⟩ := normalized_isotropic_directions hom _ _ _ norm centre
  have half : d ≤ finrank (RatFunc K) J := by change 25 ≤ _ at dim; omega
  have sym : H.IsSymm := by
    apply Matrix.isSymm_toBilin'_iff_isSymm.mpr
    ext i j
    change MvPolynomial.eval centre (MvPolynomial.pderiv j (MvPolynomial.pderiv i _)) = _
    rw [MvPolynomial.pderiv_comm j i]
    rfl
  have sq := gram_signed_square_from_half d H sym u (Fintype.card_fin _) J half (inKer.trans spans) iso
  obtain ⟨a,law⟩ := weight_twist (τ^2)
  have scale : twist g (per (RatFunc K) Idx) = MvPolynomial.C a * per (RatFunc K) Idx := by
    simpa only [g,pow_mul] using law
  have cy : (fun j ↦ g j*centre j) = f ∘ y := by
    funext j
    dsimp [centre]
    field_simp [ng]
  have cu (i : Fin (2*d)) : (fun j ↦ g j*u i j) = f ∘ Q i := by
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
  let sign : K := (splitSign d : K)
  have nsign : sign ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.sumComm (Fin d) (Fin d))) with h | h <;>
      simp [sign,splitSign,h]
  let poly := Polynomial.C sign * P.det
  have square : IsSquare (f poly) := by
    change IsSquare (f (Polynomial.C sign * P.det))
    rw [map_mul,RingHom.map_det,eq,Matrix.det_smul,Fintype.card_fin]
    have cs : f (Polynomial.C sign) = (splitSign d : RatFunc K) := by
      simp [f,sign]
    rw [cs,mul_left_comm]
    apply IsSquare.mul _ sq
    exact ⟨a^d,by rw [← pow_add,two_mul]⟩
  have jY : firstJet K ∘ y = Y := funext fun j ↦ firstJet_lift (Y j)
  have jQ : (fun i ↦ firstJet K ∘ Q i) = (fun i ↦ Pi.single (v i) (1 : DualNumber K)) := by
    funext i j
    exact atJet i j
  have evaluated : firstJet K P.det = ((hessian (per (DualNumber K) Idx) Y).submatrix v v).det := by
    rw [RingHom.map_det,show P = frameHessian y Q from rfl,frameHessian_map,jY,jQ,frameHessian_units]
  have signed : firstJet K poly = TrivSqZeroExt.inlHom K K sign *
      ((hessian (per (DualNumber K) Idx) Y).submatrix v v).det := by
    change firstJet K (Polynomial.C sign * P.det) = _
    rw [map_mul,evaluated]
    simp [firstJet]
  apply jet_nonsquare poly _ _ square
  · simp [signed,zero]
  · simp [signed,slope,nsign]

#print axioms normalized_excludes_simple_zero
end PermanentFive
