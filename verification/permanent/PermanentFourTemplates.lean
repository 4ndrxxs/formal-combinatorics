import PermanentFourPairs

/-! Three normalized integer configurations have nonsingular principal
minors of order eight in every field of characteristic different from two. -/
noncomputable section
open Matrix Finset PermanentFive QuinticPencil PermanentBorder
namespace PermanentOrderFour
variable {K : Type*} [Field K]

def grid {R : Type*} (M : F → F → R) (e : Cell4) := M e.1 e.2
def model (k : T) : Cell4 → ℤ := grid <|
  ![![![1,1,0,0],![1,1,0,0],![0,0,1,1],![0,0,1,-1]],![![1,1,1,1],![1,1,1,-1],![1,1,0,0],![1,-1,0,0]],![![1,1,1,1],![1,1,0,0],![0,0,1,-1],![0,0,1,1]]] k
private def pick (k : T) : Fin 8 → Cell4 :=
  ![![(0,2),(0,3),(2,0),(2,2),(2,3),(3,0),(3,2),(3,3)],![(0,0),(0,1),(0,2),(2,0),(2,2),(2,3),(3,0),(3,2)],![(0,0),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)]] k
private def inverseNumerator (k : T) : Matrix (Fin 8) (Fin 8) ℤ := Matrix.of fun i j ↦
  ![![![0,0,-1,0,0,1,0,0],![0,0,1,0,0,1,0,0],![-1,1,0,0,0,0,0,0],![0,0,0,0,0,0,0,1],![0,0,0,0,0,0,1,0],![1,1,0,0,0,0,0,0],![0,0,0,0,1,0,0,0],![0,0,0,1,0,0,0,0]],![![0,0,0,1,1,0,1,-1],![0,0,0,1,-1,0,1,-1],![0,0,0,2,0,0,0,0],![1,1,2,0,1,1,0,0],![1,-1,0,1,0,0,1,0],![0,0,0,1,0,0,1,0],![1,1,0,0,1,1,0,0],![-1,-1,0,0,0,0,0,0]],![![4,2,-1,-1,-1,-1,2,-2],![2,0,0,0,0,0,0,-2],![-1,0,0,0,0,1,0,1],![-1,0,0,0,1,0,0,1],![-1,0,0,1,0,0,0,0],![-1,0,1,0,0,0,0,0],![2,0,0,0,0,0,0,0],![-2,-2,1,1,0,0,0,0]]] k i j

set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
private theorem inverse_minor : ∀ k : T,
    inverseNumerator k*(table (model k)).submatrix (pick k) (pick k)=(2:ℤ) • 1 := by decide +kernel
set_option maxRecDepth 20000 in
private theorem vanish : ∀ k : T, integralValue (model k)=0 := by decide +kernel

theorem template_lower (two_ne : (2:K)≠0) (k : T) :
    8≤(H (castPoint K (model k))).rank := by
  let f := Int.castRingHom K
  let A := (table (model k)).map f
  have inv : (inverseNumerator k).map f*A.submatrix (pick k) (pick k)=(2:K) • 1 := by
    change (inverseNumerator k).map f*((table (model k)).submatrix (pick k) (pick k)).map f=_
    have cast (d : ℤ) (M : Matrix (Fin 8) (Fin 8) ℤ) : (d • M).map f=(d:K) • M.map f := by
      ext i j
      change (Int.castRingHom K) (d • M i j)=(d:K)*(Int.castRingHom K) (M i j)
      simp
    rw [←Matrix.map_mul,inverse_minor,cast]
    simp [f]
  have r := (Matrix.rank_mul_le_right ((inverseNumerator k).map f) (A.submatrix (pick k) (pick k))).trans
    (Matrix.rank_submatrix_le A (pick k) (pick k))
  rw [inv,Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero two_ne),
    Matrix.rank_one,Fintype.card_fin] at r
  rw [←hess_eq,cast_hessian]
  exact r

theorem unique_corner (x y : Cell4 → K) (away : ∀ e : Cell4, e≠(3,3) → x e=y e)
    (zx : PermanentBorder.value x=0) (zy : PermanentBorder.value y=0) (p : grad x (3,3)≠0) : x=y := by
  have oldRow (r : F) (hr : r≠3) (j : F) : x (r,j)=y (r,j) :=
    away _ (fun e ↦ hr (congrArg Prod.fst e))
  have oldBottom (j : F) (hj : j≠3) : x (3,j)=y (3,j) := away _ (fun e ↦ hj (congrArg Prod.snd e))
  have o0 := oldRow 0 (by decide)
  have o1 := oldRow 1 (by decide)
  have o2 := oldRow 2 (by decide)
  have g (j : F) : grad x (3,j)=grad y (3,j) := by simp [grad,otherThree,three,o0,o1,o2]
  have ny : grad y (3,3)≠0 := by rwa [←g]
  rw [value_eq] at zx zy
  simp only [Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,
    add_zero] at zx zy
  have e0 := oldBottom 0 (by decide)
  have e1 := oldBottom 1 (by decide)
  have e2 := oldBottom 2 (by decide)
  change x (3,0)*grad x (3,0)+(x (3,1)*grad x (3,1)+(x (3,2)*grad x (3,2)+x (3,3)*grad x (3,3)))=0 at zx
  change y (3,0)*grad y (3,0)+(y (3,1)*grad y (3,1)+(y (3,2)*grad y (3,2)+y (3,3)*grad y (3,3)))=0 at zy
  simp only [e0,e1,e2,g] at zx
  have ce : x (3,3)=y (3,3) := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show (x (3,3)-y (3,3))*grad y (3,3)=0 from ?_)).resolve_right ny
    linear_combination zx-zy
  funext e
  by_cases h : e=(3,3)
  · exact h ▸ ce
  · exact away _ h

theorem away_excludes (two_ne : (2:K)≠0) (k : T) (z : Cell4 → K)
    (h : SmallChart z) (same : ∀ e : Cell4, e≠(3,3) → z e=castPoint K (model k) e) : False := by
  have zero : PermanentBorder.value (castPoint K (model k))=0 := by rw [cast_value,vanish,Int.cast_zero]
  have eq := unique_corner z (castPoint K (model k)) same h.flat zero h.smooth
  have small := h.small
  rw [eq] at small
  have le := template_lower two_ne k
  omega

#print axioms template_lower
#print axioms away_excludes
end PermanentOrderFour
