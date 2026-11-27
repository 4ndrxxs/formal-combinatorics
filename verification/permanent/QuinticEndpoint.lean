import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.PowerSeries.Basic

/-! The rank step for the two internal layers of a regular affine pencil of a
homogeneous quintic. All spaces and the three vanishing moments appear explicitly. -/

noncomputable section
open LinearMap Module
namespace QuinticEndpoint

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- Pair two endpoint layers through a bilinear form. -/
def pair (B : LinearMap.BilinForm K W) (P Q : V →ₗ[K] W) : V →ₗ[K] Dual K V :=
  (Q.dualMap.comp B).comp P

/-- The ranges of the zeroth and first layers together are totally isotropic.
Pairing the first with the second layer kills the zeroth layer. Rank-nullity
then bounds the sum of the endpoint rank and the Hessian rank by half the
dimension of the ambient bilinear space. -/
theorem layer_rank (B : LinearMap.BilinForm K W) (nondeg : B.Nondegenerate)
    (P R S : V →ₗ[K] W)
    (pp : ∀ x y, B (P x) (P y) = 0) (pr : ∀ x y, B (P x) (R y) = 0)
    (rp : ∀ x y, B (R x) (P y) = 0) (rr : ∀ x y, B (R x) (R y) = 0)
    (ps : ∀ x y, B (P x) (S y) = 0) :
    2 * (finrank K P.range + finrank K (pair B R S).range) ≤ finrank K W := by
  let L := P.range ⊔ R.range
  have isotropic : L ≤ B.orthogonal L := by
    intro x hx y hy
    obtain ⟨_,⟨i,rfl⟩,_,⟨j,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨_,⟨k,rfl⟩,_,⟨l,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hy
    simp [pp,pr,rp,rr]
  have dim := B.finrank_add_finrank_orthogonal' L
  rw [nondeg.ker_eq_bot,inf_bot_eq,finrank_bot,add_zero] at dim
  have le := Submodule.finrank_mono isotropic
  let test : L →ₗ[K] Dual K V := (S.dualMap.comp B).comp L.subtype
  let includeP : P.range →ₗ[K] L := Submodule.inclusion (show P.range ≤ L from le_sup_left)
  have vanishes (x : P.range) : includeP x ∈ test.ker := by
    obtain ⟨x,⟨y,rfl⟩⟩ := x
    apply LinearMap.ext
    intro z
    exact ps y z
  let intoKer := includeP.codRestrict test.ker vanishes
  have inj : Function.Injective intoKer := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : test.ker ↦ z.val.val) h)
  let r := R.codRestrict L (fun x ↦ (show R.range ≤ L from le_sup_right) ⟨x,rfl⟩)
  have eq : pair B R S = test.comp r := rfl
  have hR := Submodule.finrank_mono (LinearMap.range_comp_le_range r test)
  have hP := LinearMap.finrank_le_finrank_of_injective inj
  have hT := test.finrank_range_add_finrank_ker
  rw [eq]
  omega

/-- Under the three moment equations, the third moment obeys the quintic
endpoint inequality for every self-adjoint transfer operator. -/
theorem moment_rank (B : LinearMap.BilinForm K W) (nondeg : B.Nondegenerate)
    (P : V →ₗ[K] W) (M : W →ₗ[K] W) (adj : ∀ x y, B (M x) y = B x (M y))
    (zero : ∀ x y, B (P x) (P y) = 0) (one : ∀ x y, B (P x) (M (P y)) = 0)
    (two : ∀ x y, B (P x) (M (M (P y))) = 0) :
    2 * (finrank K P.range + finrank K (pair B P (M.comp (M.comp (M.comp P)))).range) ≤ finrank K W := by
  let R := M.comp P
  let S := M.comp R
  have eq : pair B R S = pair B P (M.comp S) := by
    ext x y
    exact adj _ _
  rw [show pair B P (M.comp (M.comp (M.comp P))) = pair B R S from eq.symm]
  exact layer_rank B nondeg P R S zero one (fun x y ↦ (adj _ _).trans (one x y))
    (fun x y ↦ (adj _ _).trans (two x y)) two

#print axioms layer_rank
#print axioms moment_rank
open PowerSeries Finset

/-- A scalar prefactor of constant term one leaves the leading nonzero
coefficient in place, including when that coefficient itself vanishes. -/
theorem initial_moments {F : Type*} [CommSemiring F] (g s : F⟦X⟧) (d : ℕ) (c : F)
    (unit : coeff 0 g = 1) (prod : g * s = monomial d c) :
    ∀ n ≤ d, coeff n s = if n=d then c else 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro nd
    have e := congrArg (fun f : F⟦X⟧ ↦ coeff n f) prod
    change coeff n (g*s) = coeff n (monomial d c) at e
    rw [PowerSeries.coeff_mul,PowerSeries.coeff_monomial,Finset.sum_eq_single (0,n)] at e
    · simpa only [unit,one_mul] using e
    · rintro ⟨i,j⟩ mem diff
      have sum : i+j=n := mem_antidiagonal.mp mem
      have ij : j<n := by
        by_contra h
        have hi : i=0 := by omega
        have hj : j=n := by omega
        exact diff (by simp [hi,hj])
      simp [ih j ij (by omega),show j≠d by omega]
    · simp

/-- A coefficient identity supplied by a quintic Schur complement suffices for
the full Hessian rank estimate. The formal series can have arbitrary higher coefficients. -/
theorem series_rank (B : LinearMap.BilinForm K W) (nondeg : B.Nondegenerate)
    (P : V →ₗ[K] W) (M : W →ₗ[K] W) (adj : ∀ x y, B (M x) y = B x (M y))
    (H : V →ₗ[K] Dual K V) (g : K⟦X⟧) (unit : coeff 0 g = 1)
    (series : ∀ x y, g * PowerSeries.mk (fun j ↦ B (P x) ((M^j) (P y))) =
      monomial 3 (H x y)) :
    2 * (finrank K P.range + finrank K H.range) ≤ finrank K W := by
  have vals (x y : V) (n : ℕ) (hn : n ≤ 3) :
      B (P x) ((M^n) (P y)) = if n=3 then H x y else 0 := by
    simpa only [PowerSeries.coeff_mk] using (initial_moments g _ 3 (H x y) unit (series x y) n hn)
  have h0 (x y : V) : B (P x) (P y)=0 := by simpa using vals x y 0 (by decide)
  have h1 (x y : V) : B (P x) (M (P y))=0 := by simpa using vals x y 1 (by decide)
  have h2 (x y : V) : B (P x) (M (M (P y)))=0 := by
    simpa [pow_succ] using vals x y 2 (by decide)
  have eq : H = pair B P (M.comp (M.comp (M.comp P))) := by
    ext x y
    simpa [pair,pow_succ] using (vals x y 3 (by decide)).symm
  rw [eq]
  exact moment_rank B nondeg P M adj h0 h1 h2

#print axioms initial_moments
#print axioms series_rank

end QuinticEndpoint
