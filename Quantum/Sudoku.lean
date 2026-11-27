module

public import Quantum.Disjoint

/-! Quantum Sudoku on a finite index set. The ambient Hilbert space has one
    coordinate for each position in a block, so its dimension is the order
    of the full square. Rows, columns and blocks are actual orthonormal bases. -/
@[expose] public section
noncomputable section
namespace QuantumSudoku
open Finset Complex
open scoped BigOperators ComplexConjugate

abbrev Index (I : Type*) := I × I
abbrev H (I : Type*) [Fintype I] := EuclideanSpace ℂ (Index I)
abbrev Slice (I : Type*) [Fintype I] := EuclideanSpace ℂ I
abbrev Grid (I : Type*) [Fintype I] := Index I → Index I → H I

variable {I : Type*} [Fintype I] [DecidableEq I]

def BasisLine (v : Index I → H I) : Prop := ∃ b : OrthonormalBasis (Index I) ℂ (H I), ⇑b=v

structure Valid (v : Grid I) : Prop where
  row : ∀ r, BasisLine (v r)
  column : ∀ c, BasisLine (fun r => v r c)
  block : ∀ i j, BasisLine (fun p => v (i,p.1) (j,p.2))

def probability (v w : H I) : ℝ := ‖inner ℂ v w‖^2

/-- Equivalence under a single complex unitary and independent phases per cell. -/
def Equivalent (v w : Grid I) : Prop :=
  ∃ U : H I ≃ₗᵢ[ℂ] H I, ∀ p q, ∃ z : Circle, U (v p q) = (z:ℂ) • w p q

def point (x : I) : Slice I := EuclideanSpace.single x 1
def slot (v : Slice I) (y : I) : H I := WithLp.toLp 2
  (fun p : I × I => if p.2=y then v p.1 else 0)

@[simp] theorem point_at (x t : I) : point x t = if t=x then 1 else 0 := by
  simp [point,PiLp.single_apply,eq_comm]

@[simp] theorem point_inner (x t : I) : inner ℂ (point x) (point t) = if x=t then 1 else 0 := by
  simp [point,EuclideanSpace.inner_single_left,PiLp.single_apply]

@[simp] theorem slot_inner (v w : Slice I) (b c : I) :
    inner ℂ (slot v b) (slot w c) = if b=c then inner ℂ v w else 0 := by
  rw [PiLp.inner_apply,Fintype.sum_prod_type]
  by_cases h : b=c
  · subst c
    simp [slot,PiLp.inner_apply]
  · simp [slot,h,Ne.symm h]

def fromBands [AddGroup I] (B : I → I → Slice I) : Grid I :=
  fun r c => slot (B r.1 (r.2+c.1)) (r.1+c.2)

theorem basis_of_gram [Nonempty I] (v : Index I → H I)
    (h : ∀ p q, inner ℂ (v p) (v q) = if p=q then 1 else 0) : BasisLine v := by
  have ho := orthonormal_iff_ite.mpr h
  exact ⟨OrthonormalBasis.mk ho
    (ho.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)).ge,
    OrthonormalBasis.coe_mk _ _⟩

theorem fromBands_valid [AddGroup I] (B : I → I → Slice I)
    (hB : ∀ i x y, inner ℂ (B i x) (B i y) = if x=y then 1 else 0) :
    Valid (fromBands B) := by
  constructor
  · rintro ⟨i,a⟩
    apply basis_of_gram
    rintro ⟨j,b⟩ ⟨k,c⟩
    simp only [fromBands,slot_inner,hB]
    by_cases hj : j=k <;> by_cases hb : b=c <;> simp [hj,hb]
  · rintro ⟨j,b⟩
    apply basis_of_gram
    rintro ⟨i,a⟩ ⟨k,c⟩
    by_cases hi : i=k
    · subst k
      simp [fromBands,hB]
    · simp [fromBands,hi]
  · intro i j
    apply basis_of_gram
    rintro ⟨a,b⟩ ⟨x,y⟩
    simp only [fromBands,slot_inner,hB]
    by_cases ha : a=x <;> by_cases hb : b=y <;> simp [ha,hb]

/-- A four-state cyclic product of inner products. Independent unit phases
    cancel exactly, so it is invariant under labelled projective equivalence. -/
def fourOverlap (a b c d : H I) : ℂ :=
  inner ℂ a b * inner ℂ b c * inner ℂ c d * inner ℂ d a

private theorem circle_norm (z : Circle) : conj (z : ℂ) * (z : ℂ) = 1 := by
  rw [RCLike.conj_mul,Circle.norm_coe]
  norm_num

omit [DecidableEq I] in
theorem fourOverlap_smul (a b c d : H I) (p q r s : Circle) :
    fourOverlap ((p:ℂ) • a) ((q:ℂ) • b) ((r:ℂ) • c) ((s:ℂ) • d) = fourOverlap a b c d := by
  simp only [fourOverlap,inner_smul_left,inner_smul_right]
  calc
    _ = (conj (p:ℂ)*p)*(conj (q:ℂ)*q)*(conj (r:ℂ)*r)*(conj (s:ℂ)*s)*
        (inner ℂ a b * inner ℂ b c * inner ℂ c d * inner ℂ d a) := by ring
    _ = _ := by simp [circle_norm]

omit [DecidableEq I] in
theorem equivalent_four {v w : Grid I} (h : Equivalent v w)
    (a b c d : Index I × Index I) :
    fourOverlap (v a.1 a.2) (v b.1 b.2) (v c.1 c.2) (v d.1 d.2) =
    fourOverlap (w a.1 a.2) (w b.1 b.2) (w c.1 c.2) (w d.1 d.2) := by
  obtain ⟨u,hu⟩ := h
  obtain ⟨p,hp⟩ := hu a.1 a.2
  obtain ⟨q,hq⟩ := hu b.1 b.2
  obtain ⟨r,hr⟩ := hu c.1 c.2
  obtain ⟨s,hs⟩ := hu d.1 d.2
  calc
    _ = fourOverlap (u (v a.1 a.2)) (u (v b.1 b.2)) (u (v c.1 c.2)) (u (v d.1 d.2)) := by
      simp [fourOverlap,u.inner_map_map]
    _ = _ := by rw [hp,hq,hr,hs,fourOverlap_smul]

end QuantumSudoku
