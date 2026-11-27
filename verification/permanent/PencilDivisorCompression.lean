import PencilPolynomialWeights
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Matrix.Rank

/-! At a rank-dropping prime of maximal possible degree, a row missing
from the slope is forced to vanish. The proof uses a single minor with
one constant row for each matrix coefficient. -/
noncomputable section
open Polynomial Matrix Finset PencilWeight
namespace PencilCompression
variable {K I J k : Type*} [Field K] [Fintype J] [Fintype k] [DecidableEq k]

theorem prime_dvd_minor (p : K[X]) [Fact (Irreducible p)] (A : Matrix I J K[X])
    (small : (A.map (AdjoinRoot.mk p)).rank < Fintype.card k) (r : k → I) (c : k → J) :
    p ∣ (A.submatrix r c).det := by
  rw [←AdjoinRoot.mk_eq_zero,(AdjoinRoot.mk p).map_det]
  by_contra nz
  have eq : ((A.map (AdjoinRoot.mk p)).submatrix r c).rank = Fintype.card k :=
    Matrix.rank_of_det_ne_zero nz
  have le := Matrix.rank_submatrix_le (A.map (AdjoinRoot.mk p)) r c
  omega

theorem top_constant {q : K[X]} (h : PencilWeight.Top q 1 0) :
    q.natDegree ≤ 0 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  by_cases eq : j=1
  · simpa only [eq] using h.2
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h.1 (by omega))

theorem det_identity_row (a : k) (v : k → K) :
    ((1 : Matrix k k K).updateRow a v).det = v a := by
  classical
  have expand : (∑ i : k, v i • (1 : Matrix k k K) i) = v := by
    ext j
    simp [Finset.sum_apply,Matrix.one_apply]
  rw [←expand,Matrix.det_updateRow_sum,Matrix.det_one,smul_eq_mul,mul_one]
  exact congrFun expand.symm a

theorem isolation (p : K[X]) [Fact (Irreducible p)] (large : Fintype.card k ≤ p.natDegree)
    (A : Matrix I J K[X]) (N : Matrix I J K)
    (top : ∀ i j, PencilWeight.Top (A i j) 1 (N i j))
    (small : (A.map (AdjoinRoot.mk p)).rank < Fintype.card k)
    (r : k → I) (c : k → J) (a : k)
    (blank : ∀ j, N (r a) (c j) = 0)
    (unitRows : ∀ i, i ≠ a → ∀ j, N (r i) (c j) = (1 : Matrix k k K) i j) :
    A (r a) (c a) = 0 := by
  classical
  let M := A.submatrix r c
  let v : k → K := fun j ↦ (A (r a) (c j)).coeff 0
  let L := (1 : Matrix k k K).updateRow a v
  let w : k → ℕ := fun i ↦ if i=a then 0 else 1
  have low (j : k) : (A (r a) (c j)).natDegree ≤ 0 :=
    top_constant (blank j ▸ top (r a) (c j))
  have ht : ∀ i j, PencilWeight.Top (M.transpose i j) (w j) (L.transpose i j) := by
    intro i j
    by_cases eq : j=a
    · subst j
      simpa [M,L,w,v,Matrix.transpose_apply] using
        (show PencilWeight.Top (A (r a) (c i)) 0 ((A (r a) (c i)).coeff 0) from ⟨low i,rfl⟩)
    · simpa [M,L,w,eq,Matrix.transpose_apply,unitRows j eq i] using top (r j) (c i)
  have weighted := top_det M.transpose w L.transpose ht
  rw [Matrix.det_transpose,Matrix.det_transpose] at weighted
  have smaller : (∑ i : k, w i) < Fintype.card k := by
    classical
    rw [←Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    have ew : ∀ i ∈ (univ.erase a : Finset k), w i = 1 :=
      fun i hi ↦ ite_eq_right (Finset.mem_erase.mp hi).1
    rw [Finset.sum_congr rfl ew]
    simp [w,Finset.card_erase_of_mem (Finset.mem_univ a)]
    have := Fintype.card_pos_iff.mpr (⟨a⟩ : Nonempty k)
    omega
  have dvd := prime_dvd_minor p A small r c
  have zero : M.det = 0 := by
    by_contra nz
    exact (not_lt_of_ge (natDegree_le_of_dvd dvd nz)) (weighted.1.trans_lt (smaller.trans_le large))
  have lowcoeff : v a=0 := by
    have eq := weighted.2
    rw [zero,coeff_zero,show L.det = v a from det_identity_row a v] at eq
    exact eq.symm
  rw [eq_C_of_natDegree_le_zero (low a)]
  exact (congrArg C lowcoeff).trans (map_zero _)

theorem outside_row (p : K[X]) [Fact (Irreducible p)] (large : Fintype.card k ≤ p.natDegree)
    (A : Matrix I J K[X]) (N : Matrix I J K) (top : ∀ i j, PencilWeight.Top (A i j) 1 (N i j))
    (small : (A.map (AdjoinRoot.mk p)).rank < Fintype.card k)
    (r : k → I) (c : k → J) (pin : ∀ i j, N (r i) (c j) = (1 : Matrix k k K) i j)
    (x : I) (y : J) (blank : ∀ j, N x j = 0)
    (hit : ∃ a : k, ∀ i, i ≠ a → N (r i) y = 0) : A x y = 0 := by
  classical
  obtain ⟨a,ha⟩ := hit
  let r' := Function.update r a x
  let c' := Function.update c a y
  have isolated := isolation p large A N top small r' c' a
    (fun j ↦ by simpa [r'] using blank (c' j)) (by
      intro i hi j
      by_cases eq : j=a
      · subst j
        simpa [r',c',hi,Matrix.one_apply] using ha i hi
      · simpa [r',c',hi,eq] using pin i j)
  simpa [r',c'] using isolated

#print axioms isolation
end PencilCompression
