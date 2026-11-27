import PencilFourSmallPrime
import PencilShiftBasis
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! A bad closed point of degree at most fourteen for any four-step
twenty-dimensional matrix pencil with full slope. -/
noncomputable section
open Matrix Finset Polynomial PencilWeight
namespace PencilLayers
variable {K n m : Type*} [Field K] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

private theorem mapped_conjugate_rank {R : Type*} [CommRing R] (g : R →+* K)
    (A T U : Matrix n n R) (tu : T*U=1) (ut : U*T=1) (d : ℕ) :
    (((U*A*T).map g)^d).rank=((A.map g)^d).rank := by
  have tu' : g.mapMatrix T * g.mapMatrix U=1 := by rw [←map_mul,tu,map_one]
  have ut' : g.mapMatrix U * g.mapMatrix T=1 := by rw [←map_mul,ut,map_one]
  change (g.mapMatrix (U*A*T)^d).rank=(g.mapMatrix A^d).rank
  rw [map_mul,map_mul,conjugate_pow _ _ _ tu' ut',conjugate_rank _ _ _ tu']

private theorem small_bad_layers (A : Matrix (Layer 4) (Layer 4) K[X])
    (a : Matrix (Layer 4) (Layer 4) K) (top : ∀ i j, PencilWeight.Top (A i j) 1 (a i j))
    (nil : A^4=0) (nil₁ : a^4=0) (full₁ : (a^3).rank=5) :
    ∃ p : K[X], ∃ hp : Irreducible p, p.natDegree < 15 ∧
      (let _ := Fact.mk hp; ((A.map (AdjoinRoot.mk p))^3).rank ≠ 5) := by
  obtain ⟨V,vnz⟩ := PencilChain.exists_full_frame (k:=Fin 5) (s:=4) (Or.inr rfl) a nil₁
    (by simpa using full₁)
  let T := PencilChain.frame 4 a V
  let U := T⁻¹
  have unit : IsUnit T.det := isUnit_iff_ne_zero.mpr vnz
  have tu : T*U=1 := Matrix.mul_nonsing_inv _ unit
  have ut : U*T=1 := Matrix.nonsing_inv_mul _ unit
  have slope : U*a*T=shift K 4 := by
    rw [Matrix.mul_assoc,frame_shift a nil₁ V,←Matrix.mul_assoc,ut,Matrix.one_mul]
  let cp : Matrix (Layer 4) (Layer 4) K →+* Matrix (Layer 4) (Layer 4) K[X] := (C : K →+* K[X]).mapMatrix
  have pt : cp T * cp U=1 := by rw [←map_mul,tu,map_one]
  have pu : cp U * cp T=1 := by rw [←map_mul,ut,map_one]
  let B := cp U*A*cp T
  have lead (i j) : PencilWeight.Top (B i j) 1 (shift K 4 i j) := by
    rw [←slope]
    exact constant_conjugate_top A a T U top i j
  have stop : B^4=0 := by
    change (cp U*A*cp T)^4=0
    rw [conjugate_pow _ _ _ pt pu,nil,Matrix.mul_zero,Matrix.zero_mul]
  have ss : (shift K 4)^4=0 := by
    rw [←slope,conjugate_pow _ _ _ tu ut,nil₁,Matrix.mul_zero,Matrix.zero_mul]
  have sr : ((shift K 4)^3).rank=5 := by
    rw [←slope,conjugate_pow _ _ _ tu ut,conjugate_rank _ _ _ tu,full₁]
  obtain ⟨p,hp,d,loss⟩ := normalized_small_bad_prime B lead stop ss sr
  refine ⟨p,hp,d,?_⟩
  let _ : Fact (Irreducible p) := ⟨hp⟩
  change ((A.map (AdjoinRoot.mk p))^3).rank ≠ 5
  change (((cp U*A*cp T).map (AdjoinRoot.mk p))^3).rank ≠ 5 at loss
  rwa [mapped_conjugate_rank _ _ _ _ pt pu] at loss

private theorem power_reindex {R : Type*} [CommRing R] (e : m ≃ n) (M : Matrix n n R) (d : ℕ) :
    (M.submatrix e e)^d=(M^d).submatrix e e :=
  (map_pow (Matrix.reindexAlgEquiv R R e.symm) M d).symm

theorem four_step_small_prime (A : Matrix n n K[X]) (a : Matrix n n K)
    (size : Fintype.card n=20) (top : ∀ i j, PencilWeight.Top (A i j) 1 (a i j))
    (nil : A^4=0) (nil₁ : a^4=0) (full₁ : (a^3).rank=5) :
    ∃ p : K[X], ∃ hp : Irreducible p, p.natDegree ≤ 14 ∧
      (let _ := Fact.mk hp; ((A.map (AdjoinRoot.mk p))^3).rank ≠ 5) := by
  let e : Layer 4 ≃ n := Fintype.equivOfCardEq (by rw [size]; decide)
  have n₀ : (A.submatrix e e)^4=0 := by rw [power_reindex,nil]; rfl
  have n₁ : (a.submatrix e e)^4=0 := by rw [power_reindex,nil₁]; rfl
  have r : ((a.submatrix e e)^3).rank=5 := by rw [power_reindex,Matrix.rank_submatrix,full₁]
  obtain ⟨p,hp,d,lose⟩ := small_bad_layers (A.submatrix e e) (a.submatrix e e)
    (fun i j ↦ top (e i) (e j)) n₀ n₁ r
  refine ⟨p,hp,by omega,?_⟩
  let _ : Fact (Irreducible p) := ⟨hp⟩
  change (((A.map (AdjoinRoot.mk p)).submatrix e e)^3).rank ≠ 5 at lose
  change ((A.map (AdjoinRoot.mk p))^3).rank ≠ 5
  rwa [power_reindex,Matrix.rank_submatrix] at lose

#print axioms four_step_small_prime
end PencilLayers
