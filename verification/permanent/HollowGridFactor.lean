import HollowHessianSchur

/-! A nonzero symmetric array attached to pairs of grid coordinates,
hollow in both factors and symmetric under each separate interchange,
has no rank five. At rank at most five its entries separate into a
row factor and a column factor. -/
noncomputable section
open Matrix FourAnchor
namespace HollowGrid
variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]

structure PairSymmetric (H : Matrix (I × J) (I × J) K) : Prop where
  rows : ∀ r i j, H (r,i) (r,j)=0
  cols : ∀ i r s, H (r,i) (s,i)=0
  swapRow : ∀ r s i j, H (r,i) (s,j)=H (s,i) (r,j)
  swapCol : ∀ r s i j, H (r,i) (s,j)=H (r,j) (s,i)

omit [Fintype I] [Fintype J] in
theorem PairSymmetric.sym {H : Matrix (I × J) (I × J) K} (P : PairSymmetric H) :
    ∀ u v, H u v=H v u := by
  rintro ⟨r,i⟩ ⟨s,j⟩
  exact (P.swapRow r s i j).trans (P.swapCol s r i j)

def corners (a b : I) (p q : J) : Fin 4 → I×J := ![(a,p),(a,q),(b,p),(b,q)]

theorem normalized_factorization (H : Matrix (I × J) (I × J) K) (P : PairSymmetric H)
    (rank : H.rank ≤ 5) (a b : I) (p q : J) (one : H (a,p) (b,q)=1) :
    H.rank=4 ∧ ∃ (R S : I → K) (C D : J → K), ∀ r s i j,
      H (r,i) (s,j) = (R r*S s+S r*R s)*(C i*D j+D i*C j) := by
  classical
  let z := corners a b p q
  have a1 := (P.swapCol a b q p).trans one
  have a2 := (P.sym (b,p) (a,q)).trans a1
  have a3 := (P.sym (b,q) (a,p)).trans one
  have anc : H.submatrix z z=flip K := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [z,corners,FourAnchor.flip,P.rows,P.cols,one,a1,a2,a3]
  let R (r : I) := H (r,p) (a,q)
  let S (r : I) := H (r,p) (b,q)
  let C (i : J) := H (a,i) (b,p)
  let D (i : J) := H (a,i) (b,q)
  have rp (r : I) : vector H z (r,p)=![0,R r,0,S r] := by
    funext j
    fin_cases j <;> simp [vector,z,corners,R,S,P.cols]
  have rq (r : I) : vector H z (r,q)=![R r,0,S r,0] := by
    funext j
    fin_cases j <;> simp [vector,z,corners,R,S,P.cols,P.swapCol r a q p,P.swapCol r b q p]
  have ca (i : J) : vector H z (a,i)=![0,0,C i,D i] := by
    funext j
    fin_cases j <;> simp [vector,z,corners,C,D,P.rows]
  have cb (i : J) : vector H z (b,i)=![C i,D i,0,0] := by
    funext j
    fin_cases j <;> simp [vector,z,corners,C,D,P.rows,P.swapRow b a i p,P.swapRow b a i q]
  have goodP (r : I) (w : I×J) : H (r,p) w=proj H z (r,p) w :=
    determined H P.sym rank z anc _ (P.rows _ _ _) (by simp [proj,rp,contraction]) w
  have goodQ (r : I) (w : I×J) : H (r,q) w=proj H z (r,q) w :=
    determined H P.sym rank z anc _ (P.rows _ _ _) (by simp [proj,rq,contraction]) w
  have pair (r : I) (i : J) : vector H z (r,i)=![R r*C i,R r*D i,S r*C i,S r*D i] := by
    funext j
    fin_cases j
    · change H (r,i) (a,p)=_
      rw [P.swapCol,goodP,proj,rp,ca]
      simp [contraction]
    · change H (r,i) (a,q)=_
      rw [P.swapCol,goodQ,proj,rq,ca]
      simp [contraction]
    · change H (r,i) (b,p)=_
      rw [P.swapCol,goodP,proj,rp,cb]
      simp [contraction]
    · change H (r,i) (b,q)=_
      rw [P.swapCol,goodQ,proj,rq,cb]
      simp [contraction]
  have zero (r : I) : R r*S r+S r*R r=0 := by
    have h := (goodP r (r,q)).symm.trans (P.rows r p q)
    simpa [proj,rp,rq,contraction] using h
  have complete (r : I) (i : J) (w : I×J) : H (r,i) w=proj H z (r,i) w := by
    apply determined H P.sym rank z anc _ (P.rows _ _ _)
    rw [proj,pair]
    simp [contraction]
    linear_combination 2*C i*D i*(zero r)
  have fac : H=H.submatrix id z*flip K*H.submatrix z id := by
    ext u v
    rw [product_entry H P.sym z id]
    exact complete u.1 u.2 v
  have upper : H.rank≤4 := by
    conv_lhs => rw [fac]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)
  have nflip : (FourAnchor.flip K).det ≠ 0 := flip_det_ne_zero
  have lower := Matrix.rank_submatrix_le H z z
  rw [anc,Matrix.rank_of_det_ne_zero nflip] at lower
  have four : H.rank=4 := le_antisymm upper lower
  refine ⟨four,R,S,C,D,?_⟩
  intro r s i j
  rw [complete,proj,pair,pair]
  simp [contraction]
  ring

#print axioms normalized_factorization
end HollowGrid
