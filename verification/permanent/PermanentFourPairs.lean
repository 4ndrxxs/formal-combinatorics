import PermanentFourNormalize
import PermanentNullPairSupport

/-! Pair equations on three coordinates determine the possible supports
of a normalized last-row radical vector and the three associated columns. -/
noncomputable section
open Matrix Equiv Finset PermanentFive QuinticPencil PermanentBorder
namespace PermanentOrderFour
abbrev T := Fin 3
variable {K : Type*} [Field K]
def column (z : Cell4 → K) (j : F) (i : T) : K := z (i.castSucc,j)
def deltaColumn (z : Cell4 → K) : T → K := column z 0-column z 1
def PairValue (a b : T → K) (i j : T) : K := a i*b j+a j*b i
def Paired (a b : T → K) := ∀ i j, i≠j → PairValue a b i j=0

private theorem pair_from_three {a b : T → K} (x : PairValue a b 0 1=0)
    (y : PairValue a b 0 2=0) (z : PairValue a b 1 2=0) : Paired a b := by
  have swap (i j : T) : PairValue a b i j=PairValue a b j i := add_comm _ _
  intro i j h
  fin_cases i <;> fin_cases j <;> first | exact (h rfl).elim | assumption |
    (rw [swap]; assumption)

theorem Paired.symm {a b : T → K} (p : Paired a b) : Paired b a := by
  intro i j h
  simpa [PairValue,mul_comm,add_comm] using p i j h

theorem Paired.zero_at {a b : T → K} (p : Paired a b) (an : a≠0) {i : T} (z : a i=0) :
    b i=0 := by
  obtain ⟨j,hj⟩ : ∃ j, a j≠0 := by by_contra! h; exact an (funext h)
  have ne : j≠i := fun e ↦ hj (e ▸ z)
  have h := p j i ne
  simpa [PairValue,z,hj] using h

theorem Paired.dependent {a b c : T → K} (ab : Paired a b) (ac : Paired a c)
    (an : a≠0) (cn : c≠0) : ∃ t : K, ∀ i, b i=t*c i := by
  obtain ⟨j,hj⟩ : ∃ j, a j≠0 := by by_contra! h; exact an (funext h)
  have cj : c j≠0 := fun h ↦ hj (ac.symm.zero_at cn h)
  refine ⟨b j/c j,fun i ↦ ?_⟩
  by_cases e : j=i
  · subst i
    simp [cj]
  · have p : a j*(b i*c j-b j*c i)=0 := by
      have hb := ab j i e
      have hc := ac j i e
      unfold PairValue at hb hc
      linear_combination c j*hb-b j*hc
    have h := (mul_eq_zero.mp p).resolve_left hj
    field_simp [cj]
    linear_combination h

theorem core_column_nonzero (z : Cell4 → K) (p : grad z (3,3)≠0) (j : T) :
    column z j.castSucc≠0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  fin_cases j <;> simp [column] at h0 h1 h2 <;>
    simp [grad,otherThree,three,h0,h1,h2] at p
theorem side_column_nonzero {z : Cell4 → K} (h : SideNonzero z) : column z 3≠0 := by
  intro zero
  obtain ⟨j,hj,hit⟩ := h
  have e (i : T) : z (i.castSucc,3)=0 := congrFun zero i
  fin_cases j <;> first | exact hit (e 0) | exact hit (e 1) | exact hit (e 2) | exact hj rfl

private theorem singleton_impossible (z : Cell4 → K) (p : grad z (3,3)≠0)
    (r : RowRel z (shape K 0)) : False := by
  have h0 := r (0,3)
  have h1 := r (1,3)
  have h2 := r (2,3)
  apply p
  simp [-mul_eq_zero,H,shape,two,otherTwo,grad,three,otherThree] at h0 h1 h2 ⊢
  linear_combination z (0,0)*h0+z (1,0)*h1+z (2,0)*h2

private theorem full_pairs (z : Cell4 → K) (r : RowRel z (shape K 2)) (two_ne : (2:K)≠0)
    (j : T) : Paired (column z 3) (column z j.castSucc) := by
  have h00 := r (0,0)
  have h01 := r (0,1)
  have h02 := r (0,2)
  have h10 := r (1,0)
  have h11 := r (1,1)
  have h12 := r (1,2)
  have h20 := r (2,0)
  have h21 := r (2,1)
  have h22 := r (2,2)
  apply pair_from_three
  · apply (mul_eq_zero.mp (show (2:K)*PairValue (column z 3) (column z j.castSucc) 0 1=0 from ?_)).resolve_left two_ne
    fin_cases j
    · simp [-mul_eq_zero,H,shape,two,otherTwo,Fin.sum_univ_succ,PairValue,column] at h20 h21 h22 ⊢
      linear_combination h20+h21-h22
    · simp [-mul_eq_zero,H,shape,two,otherTwo,Fin.sum_univ_succ,PairValue,column] at h20 h21 h22 ⊢
      linear_combination h20+h21+h22
    · simp [-mul_eq_zero,H,shape,two,otherTwo,Fin.sum_univ_succ,PairValue,column] at h20 h21 h22 ⊢
      linear_combination -h20+h21+h22
  · apply (mul_eq_zero.mp (show (2:K)*PairValue (column z 3) (column z j.castSucc) 0 2=0 from ?_)).resolve_left two_ne
    fin_cases j
    · simp [-mul_eq_zero,H,shape,two,otherTwo,Fin.sum_univ_succ,PairValue,column] at h10 h11 h12 ⊢
      linear_combination h10+h11-h12
    · simp [-mul_eq_zero,H,shape,two,otherTwo,Fin.sum_univ_succ,PairValue,column] at h10 h11 h12 ⊢
      linear_combination h10+h11+h12
    · simp [-mul_eq_zero,H,shape,two,otherTwo,Fin.sum_univ_succ,PairValue,column] at h10 h11 h12 ⊢
      linear_combination -h10+h11+h12
  · apply (mul_eq_zero.mp (show (2:K)*PairValue (column z 3) (column z j.castSucc) 1 2=0 from ?_)).resolve_left two_ne
    fin_cases j
    · simp [-mul_eq_zero,H,shape,two,otherTwo,Fin.sum_univ_succ,PairValue,column] at h00 h01 h02 ⊢
      linear_combination h00+h01-h02
    · simp [-mul_eq_zero,H,shape,two,otherTwo,Fin.sum_univ_succ,PairValue,column] at h00 h01 h02 ⊢
      linear_combination h00+h01+h02
    · simp [-mul_eq_zero,H,shape,two,otherTwo,Fin.sum_univ_succ,PairValue,column] at h00 h01 h02 ⊢
      linear_combination -h00+h01+h02

private theorem full_impossible (z : Cell4 → K) (h : SmallChart z) (r : RowRel z (shape K 2))
    (two_ne : (2:K)≠0) : False := by
  let u := column z 3
  have un : u≠0 := side_column_nonzero h.side
  have ps (j : T) : Paired u (column z j.castSucc) := full_pairs z r two_ne j
  by_cases all : ∀ i, u i≠0
  · have hz := PermanentSupport.three_kill u (column z 0) two_ne (ps 0)
      (show (0:T)≠1 by decide) (show (0:T)≠2 by decide) (show (1:T)≠2 by decide)
      (all _) (all _) (all _)
    exact core_column_nonzero z h.smooth 0 (funext hz)
  · push Not at all
    obtain ⟨i,hi⟩ := all
    have zero (j : T) := (ps j).zero_at un hi
    have core := core_column_nonzero (transposePoint z) h.transpose.smooth i
    apply core
    funext j
    exact zero j

theorem two_support (z : Cell4 → K) (h : SmallChart z) (two_ne : (2:K)≠0) (k : T)
    (r : RowRel z (shape K k)) : k=1 := by
  fin_cases k
  · exact (singleton_impossible z h.smooth r).elim
  · rfl
  · exact (full_impossible z h r two_ne).elim

structure ColumnPairs (z : Cell4 → K) : Prop where
  edge : Paired (column z 2) (column z 3)
  outerDiff : Paired (column z 3) (deltaColumn z)
  innerDiff : Paired (column z 2) (deltaColumn z)
theorem column_pairs (z : Cell4 → K) (r : RowRel z (shape K 1)) : ColumnPairs z := by
  constructor
  · apply pair_from_three
    · have eq := r (2,0)
      simp [-mul_eq_zero,H,shape,two,otherTwo,Fin.sum_univ_succ,PairValue,column] at eq ⊢
      linear_combination -eq
    · have eq := r (1,0)
      simp [-mul_eq_zero,H,shape,two,otherTwo,Fin.sum_univ_succ,PairValue,column] at eq ⊢
      linear_combination -eq
    · have eq := r (0,0)
      simp [-mul_eq_zero,H,shape,two,otherTwo,Fin.sum_univ_succ,PairValue,column] at eq ⊢
      linear_combination -eq
  · apply pair_from_three
    · have eq := r (2,2)
      simp [-mul_eq_zero,H,shape,two,otherTwo,Fin.sum_univ_succ,PairValue,column,deltaColumn,Pi.sub_apply] at eq ⊢
      linear_combination -eq
    · have eq := r (1,2)
      simp [-mul_eq_zero,H,shape,two,otherTwo,Fin.sum_univ_succ,PairValue,column,deltaColumn,Pi.sub_apply] at eq ⊢
      linear_combination -eq
    · have eq := r (0,2)
      simp [-mul_eq_zero,H,shape,two,otherTwo,Fin.sum_univ_succ,PairValue,column,deltaColumn,Pi.sub_apply] at eq ⊢
      linear_combination -eq
  · apply pair_from_three
    · have eq := r (2,3)
      simp [-mul_eq_zero,H,shape,two,otherTwo,Fin.sum_univ_succ,PairValue,column,deltaColumn,Pi.sub_apply] at eq ⊢
      linear_combination -eq
    · have eq := r (1,3)
      simp [-mul_eq_zero,H,shape,two,otherTwo,Fin.sum_univ_succ,PairValue,column,deltaColumn,Pi.sub_apply] at eq ⊢
      linear_combination -eq
    · have eq := r (0,3)
      simp [-mul_eq_zero,H,shape,two,otherTwo,Fin.sum_univ_succ,PairValue,column,deltaColumn,Pi.sub_apply] at eq ⊢
      linear_combination -eq

#print axioms two_support
#print axioms column_pairs
end PermanentOrderFour
