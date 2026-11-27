import PencilDivisorCompression
import PencilChainDegree
import NilpotentRankProfile

/-! Four layers of five coordinates and the constant image and kernel
forced by a high-degree degeneration of a normalized pencil. -/
noncomputable section
open Matrix Finset Polynomial
namespace PencilLayers
abbrev Layer (s : ℕ) := Fin s × Fin 5

def head (s : ℕ) : Layer s ↪ Layer (s+1) where
  toFun x := (x.1.castSucc,x.2)
  inj' := by
    rintro ⟨a,b⟩ ⟨c,d⟩ h
    exact Prod.ext (Fin.ext (congrArg (fun x ↦ x.1.val) h)) (congrArg (fun x : Layer (s+1) ↦ x.2) h)

def tail (s : ℕ) : Layer s ↪ Layer (s+1) where
  toFun x := (x.1.succ,x.2)
  inj' := by
    rintro ⟨a,b⟩ ⟨c,d⟩ h
    exact Prod.ext (Fin.succ_injective _ (congrArg Prod.fst h)) (congrArg (fun x : Layer (s+1) ↦ x.2) h)

def shift (R : Type*) [Zero R] [One R] (s : ℕ) : Matrix (Layer s) (Layer s) R :=
  Matrix.of fun i j ↦ if i.1.val=j.1.val+1 ∧ i.2=j.2 then 1 else 0

variable {K : Type*} [Field K]

theorem pinned (i j : Layer 3) :
    shift K 4 (tail 3 i) (head 3 j) = (1 : Matrix (Layer 3) (Layer 3) K) i j := by
  have eq : (i.1.val=j.1.val ∧ i.2=j.2) ↔ i=j :=
    ⟨fun h ↦ Prod.ext (Fin.ext h.1) h.2,fun h ↦ h ▸ ⟨rfl,rfl⟩⟩
  change (if i.1.val+1=j.1.val+1 ∧ i.2=j.2 then (1:K) else 0) = _
  simp [Matrix.one_apply,eq]

private theorem unique_hit {T : Type*} [Nonempty T] (P : T → Prop)
    (uniq : ∀ i j, P i → P j → i=j) : ∃ a : T, ∀ i, i ≠ a → ¬P i := by
  classical
  by_cases ex : ∃ a, P a
  · obtain ⟨a,ha⟩ := ex
    exact ⟨a,fun i ne hi ↦ ne (uniq i a hi ha)⟩
  · exact ⟨Classical.arbitrary _,fun i _ hi ↦ ex ⟨i,hi⟩⟩

private theorem row_hit (y : Layer 4) :
    ∃ a : Layer 3, ∀ i, i ≠ a → shift K 4 (tail 3 i) y = 0 := by
  let P := fun i : Layer 3 ↦ i.1.val=y.1.val ∧ i.2=y.2
  obtain ⟨a,ha⟩ := unique_hit P (fun i j hi hj ↦
    Prod.ext (Fin.ext (hi.1.trans hj.1.symm)) (hi.2.trans hj.2.symm))
  refine ⟨a,fun i ni ↦ ?_⟩
  have ne := ha i ni
  change (if i.1.val+1=y.1.val+1 ∧ i.2=y.2 then (1:K) else 0)=0
  simpa only [Nat.add_right_cancel_iff] using (ite_eq_right ne : (if P i then (1:K) else 0)=0)

private theorem col_hit (x : Layer 4) :
    ∃ a : Layer 3, ∀ i, i ≠ a → shift K 4 x (head 3 i) = 0 := by
  let P := fun i : Layer 3 ↦ x.1.val=i.1.val+1 ∧ x.2=i.2
  obtain ⟨a,ha⟩ := unique_hit P (fun i j hi hj ↦
    Prod.ext (Fin.ext (Nat.add_right_cancel (hi.1.symm.trans hj.1))) (hi.2.symm.trans hj.2))
  refine ⟨a,fun i ni ↦ ?_⟩
  have ne := ha i ni
  exact (ite_eq_right ne : (if P i then (1:K) else 0)=0)

theorem insufficient_rank (A : Matrix (Layer 4) (Layer 4) K) (nil : A^4=0)
    (drop : (A^3).rank ≠ 5) : A.rank < 15 := by
  by_contra! full
  have a := Matrix.rank_mul_ge A A
  have b := Matrix.rank_mul_ge (A^2) A
  rw [←sq] at a
  rw [←pow_succ] at b
  change (A^2).rank + A.rank ≤ (A^3).rank + _ at b
  have n : Fintype.card (Layer 4)=20 := by decide
  rw [n] at a b
  let T := A.toLin'
  have tn : T^4=0 := by
    change A.toLin'^4=0
    rw [←Matrix.toLin'_pow,nil]
    exact map_zero _
  have rk (j : ℕ) : Module.finrank K (T^j).range=(A^j).rank := by
    change Module.finrank K (A.toLin'^j).range=_
    rw [←Matrix.toLin'_pow]
    rfl
  have profile := NilpotentProfile.four_step_profile T ((Module.finrank_pi K).trans n) tn
    (by rw [rk]; omega)
  apply drop
  exact (rk 3).symm.trans profile.2.2

theorem fixed_flags (p : K[X]) [Fact (Irreducible p)] (large : 15 ≤ p.natDegree)
    (A : Matrix (Layer 4) (Layer 4) K[X])
    (top : ∀ i j, PencilWeight.Top (A i j) 1 (shift K 4 i j))
    (small : (A.map (AdjoinRoot.mk p)).rank < 15) :
    (∀ x : Fin 5, ∀ j, A (0,x) j = 0) ∧ (∀ i, ∀ y : Fin 5, A i (3,y)=0) := by
  have nc : Fintype.card (Layer 3)=15 := by decide
  constructor
  · intro x j
    apply PencilCompression.outside_row p (nc ▸ large) A (shift K 4) top (nc ▸ small)
      (tail 3) (head 3) pinned _ _ _ (row_hit j)
    intro l
    simp [shift]
  · intro i y
    have partialRank : (A.transpose.map (AdjoinRoot.mk p)).rank < Fintype.card (Layer 3) := by
      change (A.map (AdjoinRoot.mk p)).transpose.rank < _
      rw [Matrix.rank_transpose,nc]
      exact small
    apply PencilCompression.outside_row p (nc ▸ large) A.transpose (shift K 4).transpose
      (fun x j ↦ top j x) partialRank (head 3) (tail 3) _ _ _ _ (col_hit i)
    · intro l m
      change shift K 4 (tail 3 m) (head 3 l) = _
      rw [pinned]
      simp [Matrix.one_apply,eq_comm]
    · intro l
      have lt := l.1.isLt
      have ne : l.1.val ≠ 4 := by omega
      simp [shift,ne]

#print axioms fixed_flags
end PencilLayers
