import QuinticSaturation
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-! A fixed centre of a quintic pencil admits many kernel directions
for which the transferred endpoints lift. The loss in dimension is
bounded by the defect of the endpoint range from maximal isotropic size. -/

noncomputable section
open LinearMap Module
namespace QuinticSaturation
variable {K V W Z T : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup Z] [Module K Z] [AddCommGroup T] [Module K T]

private theorem many_preimages [FiniteDimensional K W] [FiniteDimensional K Z]
    (P : V →ₗ[K] W) (R : Z →ₗ[K] W) (h : ℕ)
    (small : finrank K ↥(P.range ⊔ R.range) ≤ h) :
    ∃ J : Submodule K Z, finrank K Z + finrank K P.range ≤ finrank K J + h ∧
      ∀ z ∈ J, R z ∈ P.range := by
  let M := P.range ⊔ R.range
  let U := P.range.comap M.subtype
  let incl := R.codRestrict M (fun z ↦ (show R.range ≤ M from le_sup_right) ⟨z,rfl⟩)
  let q := U.mkQ.comp incl
  have quota := U.finrank_quotient_add_finrank
  have used : finrank K U = finrank K P.range :=
    (Submodule.comapSubtypeEquivOfLe (show P.range ≤ M from le_sup_left)).finrank_eq
  have rank := q.finrank_range_add_finrank_ker
  have le := q.range.finrank_le
  change finrank K M ≤ h at small
  refine ⟨q.ker,by omega,?_⟩
  intro z hz
  have eq : (Submodule.Quotient.mk (incl z) : M ⧸ U) = 0 := hz
  exact (Submodule.Quotient.mk_eq_zero U).mp eq

private def transferred (B : V →ₗ[K] Dual K T) (C : V →ₗ[K] T) (D : V →ₗ[K] End K T)
    (y : V) : V →ₗ[K] Dual K T × T where
  toFun z := ((B y).comp (D z),D z (C y))
  map_add' x z := by
    apply Prod.ext
    · ext v; simp
    · simp
  map_smul' a z := by
    apply Prod.ext
    · ext v; simp
    · simp

/-- At any fixed centre there is a subspace of liftable directions whose
codimension inside the kernel is at most the defect in endpoint dimension. -/
theorem many_lifts [CharZero K] [FiniteDimensional K V] [FiniteDimensional K T]
    (B : V →ₗ[K] Dual K T) (C : V →ₗ[K] T) (D : V →ₗ[K] End K T)
    (quadratic : ∀ x, B x (C x) = 0) (cubic : ∀ x, B x (D x (C x)) = 0)
    (quartic : ∀ x, B x (D x (D x (C x))) = 0) (y : V) :
    ∃ J : Submodule K (B.prod C).ker,
      finrank K (B.prod C).ker + finrank K (B.prod C).range ≤ finrank K J + finrank K T ∧
      ∀ z ∈ J, ∃ w, (∀ v, B w v = B y (D z.val v)) ∧ C w = D z.val (C y) := by
  let P := B.prod C
  let R := (transferred B C D y).comp P.ker.subtype
  let G := dualProd K T
  let M := P.range ⊔ R.range
  have bz (z : P.ker) : B (z : V) = 0 := congrArg Prod.fst z.property
  have cz (z : P.ker) : C (z : V) = 0 := congrArg Prod.snd z.property
  have first (z : P.ker) (x : V) : B x (D (z : V) (C x)) = 0 := by
    have h := cubic (x + (z : V))
    simp only [map_add,bz,cz,add_zero,LinearMap.add_apply] at h
    linear_combination h - cubic x
  have square (z : P.ker) : B y (D (z : V) (D (z : V) (C y))) = 0 := by
    have plus := quartic (y + (z : V))
    have minus := quartic (y - (z : V))
    simp only [map_add,map_sub,bz,cz,add_zero,sub_zero,LinearMap.add_apply,LinearMap.sub_apply] at plus minus
    have h : 2 * B y (D (z : V) (D (z : V) (C y))) = 0 := by
      linear_combination plus + minus - 2 * quartic y
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  have pp (u v : V) : G (P u) (P v) = 0 := by
    change B v (C u) + B u (C v) = 0
    have h := quadratic (u+v)
    simp only [map_add,LinearMap.add_apply] at h
    linear_combination h - quadratic u - quadratic v
  have pr (u : V) (z : P.ker) : G (P u) (R z) = 0 := by
    change B y (D (z : V) (C u)) + B u (D (z : V) (C y)) = 0
    have h := first z (u+y)
    simp only [map_add,LinearMap.add_apply] at h
    linear_combination h - first z u - first z y
  have rp (z : P.ker) (u : V) : G (R z) (P u) = 0 :=
    (isSymm_dualProd K T).eq_iff.mp (pr u z)
  have diag (z : P.ker) : G (R z) (R z) = 0 := by
    change B y (D (z : V) (D (z : V) (C y))) + B y (D (z : V) (D (z : V) (C y))) = 0
    rw [square,zero_add]
  have rr (z v : P.ker) : G (R z) (R v) = 0 := by
    have atSum := diag (z+v)
    simp only [map_add,LinearMap.add_apply,diag,zero_add,add_zero] at atSum
    have sym : G (R v) (R z) = G (R z) (R v) := (isSymm_dualProd K T).eq _ _
    have h : 2 * G (R z) (R v) = 0 := by linear_combination atSum - sym
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  have iso : M ≤ G.orthogonal M := by
    intro x hx b hb
    obtain ⟨_,⟨u,rfl⟩,_,⟨v,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨_,⟨j,rfl⟩,_,⟨k,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hb
    simp [pp,pr,rp,rr]
  have nd : G.Nondegenerate :=
    (isSymm_dualProd K T).isRefl.nondegenerate_iff_separatingLeft.mpr
      ((separatingLeft_dualProd K T).mpr (Module.eval_apply_injective K))
  have dims := G.finrank_add_finrank_orthogonal' M
  rw [nd.ker_eq_bot,inf_bot_eq,finrank_bot,add_zero,Module.finrank_prod,Subspace.dual_finrank_eq] at dims
  have le := Submodule.finrank_mono iso
  obtain ⟨J,dim,lifts⟩ := many_preimages P R (finrank K T) (show finrank K M ≤ finrank K T by omega)
  refine ⟨J,dim,?_⟩
  intro z hz
  obtain ⟨w,eq⟩ := lifts z hz
  exact ⟨w,fun v ↦ DFunLike.congr_fun (congrArg Prod.fst eq) v,congrArg Prod.snd eq⟩

#print axioms many_lifts
end QuinticSaturation
