module
public import Mathlib

/-! Finite Boolean decompositions of a commuting family of orthogonal projections.
The operator ring and the Hilbert space on which it acts need not be finite-dimensional. -/
@[expose] public section
noncomputable section
open Finset
namespace WeberCompletion

variable {A : Type*} [Ring A] [StarRing A]
variable {K J : Type*}

structure Partition [Fintype K] (f : K → A) : Prop where
  projection : ∀ k, IsStarProjection (f k)
  orthogonal : ∀ i j, i≠j → f i*f j=0
  total : ∑ k, f k=1

/-- Split all joint eigenspaces, including possible zero summands. The last clause
keeps the construction inside the double commutant of the specified projections. -/
theorem atom_decomposition (s : Finset J) (P : J → A) (proj : ∀ j∈s, IsStarProjection (P j))
    (comm : ∀ j∈s, ∀ k∈s, Commute (P j) (P k)) :
    ∃ (K : Type) (_ : Fintype K) (f : K → A), Partition f ∧
      (∀ j∈s, ∀ k, P j*f k=0 ∨ P j*f k=f k) ∧
      (∀ X : A, (∀ j∈s, Commute X (P j)) → ∀ k, Commute X (f k)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Unit,inferInstance,fun _ => 1,⟨fun _ => IsStarProjection.one _,
        fun _ _ h => (h (Subsingleton.elim _ _)).elim,by simp⟩,by simp,?_⟩
    simp [Commute]
  | @insert j s fresh ih =>
    have old (i : J) (hi : i∈s) : i∈insert j s := Finset.mem_insert_of_mem hi
    have pj := proj j (mem_insert_self _ _)
    obtain ⟨K,inst,F,part,eigen,central⟩ := ih (fun i h => proj i (old i h))
      (fun i h k t => comm i (old i h) k (old k t))
    let L (b : Bool) := if b then P j else 1-P j
    let g (x : Bool × K) := L x.1*F x.2
    have lp (b : Bool) : IsStarProjection (L b) := by cases b <;> simp [L,pj,pj.one_sub]
    have lc (b : Bool) (k : K) : Commute (L b) (F k) := by
      apply central
      intro i hi
      have h := comm j (mem_insert_self _ _) i (old i hi)
      cases b <;> simpa [L] using (by first | exact h | exact (Commute.one_left _).sub_left h)
    have lf (b c : Bool) (i k : K) :
        g (b,i)*g (c,k)=(L b*L c)*(F i*F k) := by
      change (L b*F i)*(L c*F k)=_
      calc
        _ = L b*(F i*L c)*F k := by noncomm_ring
        _ = _ := by rw [← (lc c i).eq]; noncomm_ring
    have lo (b c : Bool) (ne : b≠c) : L b*L c=0 := by
      cases b <;> cases c <;> simp_all [L,pj.mul_one_sub_self,pj.one_sub_mul_self]
    refine ⟨Bool × K,inferInstance,g,⟨fun x => (lp x.1).mul (part.projection _) (lc _ _),?_,?_⟩,?_,?_⟩
    · rintro ⟨b,i⟩ ⟨c,k⟩ ne
      rw [lf]
      by_cases bc : b=c
      · subst c
        have ik : i≠k := by rintro rfl; exact ne rfl
        rw [part.orthogonal i k ik,mul_zero]
      · rw [lo b c bc,zero_mul]
    · simp [g,Fintype.sum_prod_type,← Finset.mul_sum,part.total,L]
    · intro i hi
      rcases mem_insert.mp hi with rfl | h
      · rintro ⟨b,k⟩
        cases b
        · left; simp [g,L,← mul_assoc,pj.mul_one_sub_self]
        · right; simp [g,L,← mul_assoc,pj.isIdempotentElem.eq]
      · rintro ⟨b,k⟩
        have c : Commute (P i) (L b) := by
          have q := comm i (old i h) j (mem_insert_self _ _)
          cases b
          · exact (Commute.one_right _).sub_right q
          · exact q
        change P i*(L b*F k)=0 ∨ P i*(L b*F k)=L b*F k
        rw [← mul_assoc,c.eq,mul_assoc]
        exact (eigen i h k).imp (fun z => by rw [z,mul_zero]) (fun z => by rw [z])
    · intro X hx u
      apply Commute.mul_right _ (central X (fun i hi => hx i (old i hi)) _)
      have q := hx j (mem_insert_self _ _)
      cases u.1
      · exact (Commute.one_right _).sub_right q
      · exact q

variable [Fintype K]

def select (F : K → A) (p : K → Prop) : A := by
  classical exact ∑ k, if p k then F k else 0

theorem Partition.select_mul {F : K → A} (h : Partition F) (p q : K → Prop) :
    select F p * select F q = select F (fun k => p k ∧ q k) := by
  classical
  unfold select
  rw [sum_mul]
  apply sum_congr rfl
  intro k _
  rw [mul_sum,sum_eq_single k]
  · by_cases hp : p k <;> by_cases hq : q k <;> simp [hp,hq,(h.projection k).isIdempotentElem.eq]
  · intro i _ ne
    by_cases hp : p k <;> by_cases hq : q i <;> simp [hp,hq,h.orthogonal k i ne.symm]
  · simp

theorem Partition.select_projection {F : K → A} (h : Partition F) (p : K → Prop) :
    IsStarProjection (select F p) := by
  classical
  constructor
  · change select F p * select F p = _
    simp [h.select_mul]
  · change star (select F p)=select F p
    unfold select
    rw [star_sum]
    apply sum_congr rfl
    intro k _
    by_cases hp : p k <;> simp [hp,(h.projection k).isSelfAdjoint.star_eq]

theorem Partition.select_commute {F : K → A} (h : Partition F) (p q : K → Prop) :
    Commute (select F p) (select F q) := by
  change select F p * select F q = _
  rw [h.select_mul,h.select_mul]
  simp only [and_comm]

end WeberCompletion
