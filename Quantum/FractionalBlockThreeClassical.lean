module
public import Quantum.FractionalBlockThreeGrid

/-! Four rows exclude a positive first-block event in every classical
Sudoku obeying the measured support. The resulting noncontextuality
inequality holds on the full scalar classical convex hull. -/
@[expose] public section
noncomputable section
namespace FractionalBlockThree
open QuantumSudoku FractionalLayouts FractionalBlockBell FractionalPolygons.Sudoku Complex Finset
open scoped BigOperators

theorem clash {I : Type*} {f : Site I → Index I}
    (hf : ∀ d k, Function.Injective (fun j => f (arrange d (k,j))))
    (u v : Site I) (edge : Adjacent u v) : f u≠f v := by
  rcases u with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rcases v with ⟨⟨h,i⟩,⟨j,k⟩⟩
  rcases edge with ⟨ne,row|col|blocks⟩
  · change (a,b)=(h,i) at row
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj row
    exact fun e => ne (Prod.ext rfl (hf .row (a,b) e))
  · change (c,d)=(j,k) at col
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj col
    exact fun e => ne (Prod.ext (hf .column (c,d) e) rfl)
  · change a=h ∧ c=j at blocks
    obtain ⟨rfl,rfl⟩ := blocks
    intro e
    have eq : (b,d)=(i,k) := hf .block (a,c) e
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    exact ne rfl

private instance (x y : Site F) : Decidable (Adjacent x y) := by unfold Adjacent; infer_instance

private theorem four_rows {f : Site F → Index F}
    (hf : ∀ d k, Function.Injective (fun j => f (arrange d (k,j))))
    (zeros : ∀ r c, f (cell r c)=outcome → permitted r c) :
    f (cell 0 6)≠outcome := by
  intro first
  have row (r : Fin 9) : ∃ c, f (cell r c)=outcome ∧ permitted r c := by
    obtain ⟨c,hc⟩ := (Finite.injective_iff_bijective.mp (hf .row (order.symm r))).surjective outcome
    have yes : f (cell r (order c))=outcome := by simpa [cell,arrange] using hc
    exact ⟨order c,yes,zeros _ _ yes⟩
  have conflict {r c s d : Fin 9} (edge : Adjacent (cell r c) (cell s d))
      (a : f (cell r c)=outcome) (b : f (cell s d)=outcome) : False :=
    clash hf _ _ edge (a.trans b.symm)
  obtain ⟨a,ya,ha⟩ := row 2
  have a4 : f (cell 2 4)=outcome := by
    rcases (show a=4 ∨ a=8 by simpa [permitted] using ha) with rfl|rfl
    · exact ya
    · exact (conflict (by decide +kernel) first ya).elim
  obtain ⟨b,yb,hb⟩ := row 4
  have b3 : f (cell 4 3)=outcome := by
    rcases (show b=3 ∨ b=4 ∨ b=6 by simpa [permitted] using hb) with rfl|rfl|rfl
    · exact yb
    · exact (conflict (by decide +kernel) a4 yb).elim
    · exact (conflict (by decide +kernel) first yb).elim
  obtain ⟨c,yc,hc⟩ := row 5
  have c7 : f (cell 5 7)=outcome := by
    rcases (show c=3 ∨ c=5 ∨ c=7 by simpa [permitted] using hc) with rfl|rfl|rfl
    · exact (conflict (by decide +kernel) b3 yc).elim
    · exact (conflict (by decide +kernel) b3 yc).elim
    · exact yc
  obtain ⟨d,yd,hd⟩ := row 8
  rcases (show d=3 ∨ d=6 ∨ d=7 by simpa [permitted] using hd) with rfl|rfl|rfl
  · exact conflict (by decide +kernel) b3 yd
  · exact conflict (by decide +kernel) first yd
  · exact conflict (by decide +kernel) c7 yd

def badMass (p : P) := ∑ q : Fin 9×Fin 9, if permitted q.1 q.2 then 0 else p (cell q.1 q.2) outcome

theorem classical_inequality {p : P} (h : Classical p) : p (cell 0 6) outcome≤badMass p := by
  obtain ⟨f,hf,hp⟩ := h
  have pn (u : Site F) : 0≤p u outcome := by rw [hp]; split <;> norm_num
  have each (q : Fin 9×Fin 9) : 0≤(if permitted q.1 q.2 then 0 else p (cell q.1 q.2) outcome) :=
    by split <;> first | exact le_rfl | exact pn _
  rw [hp]
  split
  · rename_i target
    have miss : ∃ r c, f (cell r c)=outcome ∧ ¬permitted r c := by
      by_contra! good
      exact four_rows hf good target
    obtain ⟨r,c,yes,bad⟩ := miss
    have t := Finset.single_le_sum (s:=univ) (fun q _ => each q) (mem_univ (r,c))
    simpa [badMass,bad,hp,yes] using t
  · exact Finset.sum_nonneg fun q _ => each q

theorem hull_inequality {p : P} (h : p∈convexHull ℝ {p | Classical p}) :
    p (cell 0 6) outcome≤badMass p := by
  have cv : Convex ℝ {p : P | p (cell 0 6) outcome≤badMass p} := by
    intro p hp q hq a b ha hb _
    have linear : badMass (a • p+b • q)=a*badMass p+b*badMass q := by
      simp only [badMass,Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      split <;> simp
    change a*p (cell 0 6) outcome+b*q (cell 0 6) outcome≤_
    rw [linear]
    exact add_le_add (mul_le_mul_of_nonneg_left hp ha) (mul_le_mul_of_nonneg_left hq hb)
  exact convexHull_min (fun p hp => classical_inequality hp) cv h

theorem reading_bad : badMass reading=0 := by
  apply Finset.sum_eq_zero
  intro q _
  split
  · rfl
  · exact forbidden_zero _ _ (by assumption)

theorem outside : blockReadout 0 v∉convexHull ℝ {p | Classical p} := by
  intro h
  have b := hull_inequality h
  change reading (cell 0 6) outcome≤badMass reading at b
  rw [target,reading_bad] at b
  norm_num at b

#print axioms hull_inequality
#print axioms outside
end FractionalBlockThree

