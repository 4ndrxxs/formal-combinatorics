module
public import Quantum.DiagonalSixTiles

/-! Opposite cells of each tile are orthogonal. Two ternary resolutions with
matching zero products force commuting half-tile and sector projections. -/
@[expose] public section
noncomputable section
namespace DiagonalSix
open Complex Matrix Finset
open scoped Matrix BigOperators

theorem bit_either : ∀ t u v : Bit, t≠u → v=t ∨ v=u := by decide +kernel

theorem sum_three (f : Tri → M) (i j k : Tri) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    ∑ l, f l=f i+f j+f k := by
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> first | contradiction | ac_rfl

namespace Model
variable (g : Model)

theorem leftMissing (i j : Tri) (a : Pair) : g.X (label i j)*g.e i j a=0 := by
  simpa only [Matrix.conjTranspose_mul,g.Xherm,show (g.e i j a)ᴴ=g.e i j a from g.herm _ _,
    Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose (g.missing i j a)

theorem supported (i j : Tri) (a : Pair) : g.e i j a*g.P (label i j)=g.e i j a := by
  have h := g.missing i j a
  rw [X,mul_sub,mul_one,sub_eq_zero] at h
  exact h.symm

theorem acrossRows (i j : Tri) (h : i≠j) (a b : Pair) (ht : a.1≠b.1) :
    g.e i j a*g.P i*g.e i j b=0 := by
  rw [P,tile,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro c _
  rcases bit_either _ _ c.1 ht with l | r
  · have eq := g.rowOrth (i,a.1) (j,a.2) (i,c.2) (fun eq => h (congrArg Prod.fst eq).symm)
    simp only [e,l,eq,zero_mul]
  · have eq := g.rowOrth (i,b.1) (i,c.2) (j,b.2) (fun eq => h (congrArg Prod.fst eq))
    simp only [e,r,mul_assoc,eq,mul_zero]

theorem acrossCols (i j : Tri) (h : i≠j) (a b : Pair) (ht : a.2≠b.2) :
    g.e i j a*g.P j*g.e i j b=0 := by
  rw [P,tile,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro c _
  rcases bit_either _ _ c.2 ht with l | r
  · have eq := g.colOrth (j,a.2) (i,a.1) (j,c.1) (fun eq => h (congrArg Prod.fst eq))
    simp only [e,l,eq,zero_mul]
  · have eq := g.colOrth (j,b.2) (j,c.1) (i,b.1) (fun eq => h (congrArg Prod.fst eq).symm)
    simp only [e,r,mul_assoc,eq,mul_zero]

theorem tileProd (i j : Tri) (a b : Pair) :
    g.e i j a*g.e i j b=if a=b then g.e i j a else 0 := by
  by_cases hij : i=j
  · subst j; exact g.diagProd i a b
  by_cases hab : a=b
  · subst b; simp [g.idem,e]
  rw [if_neg hab]
  by_cases hr : a.1=b.1
  · have hs : a.2≠b.2 := fun e => hab (Prod.ext hr e)
    dsimp [e]
    rw [hr]
    exact g.rowOrth _ _ _ (fun e => hs (congrArg (fun c : Idx => c.2) e))
  by_cases hc : a.2=b.2
  · dsimp [e]
    rw [hc]
    exact g.colOrth _ _ _ (fun e => hr (congrArg (fun r : Idx => r.2) e))
  obtain ⟨hki,hkj⟩ := label_ne i j hij
  have h := g.diagTotal
  rw [sum_three _ i j (label i j) hij hki.symm hkj.symm] at h
  have z := congrArg (fun m : M => g.e i j a*m*g.e i j b) h
  simp only [mul_add,add_mul,g.acrossRows i j hij a b hr,g.acrossCols i j hij a b hc,
    g.supported,zero_add,mul_one] at z
  linear_combination (norm := abel) -z

def rowHalf (r : Idx) (j : Tri) : M := ∑ s : Bit, g.p r (label r.1 j,s)
def colHalf (c : Idx) (i : Tri) : M := ∑ t : Bit, g.p (label c.1 i,t) c

theorem sum_relabel (f : Tri → M) (i : Tri) : ∑ j, f (label i j)=∑ j, f j := by
  let e : Equiv.Perm Tri := ⟨label i,label i,label_invol i,label_invol i⟩
  exact Equiv.sum_comp e f

theorem rowHalf_total (r : Idx) : ∑ j, g.rowHalf r j=1 := by
  unfold rowHalf
  rw [sum_relabel (fun j => ∑ s : Bit, g.p r (j,s))]
  simpa only [Fintype.sum_prod_type] using g.row r

theorem colHalf_total (c : Idx) : ∑ i, g.colHalf c i=1 := by
  unfold colHalf
  rw [sum_relabel (fun i => ∑ t : Bit, g.p (i,t) c)]
  simpa only [Fintype.sum_prod_type] using g.col c

theorem rowHalf_orth (r : Idx) (i j : Tri) (hne : i≠j) : g.rowHalf r i*g.rowHalf r j=0 := by
  unfold rowHalf
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro t _
  rw [Finset.mul_sum]
  exact Finset.sum_eq_zero (fun s _ => g.rowOrth _ _ _ (fun e =>
    hne ((Function.LeftInverse.injective (label_invol r.1)) (congrArg Prod.fst e))))

theorem colHalf_orth (c : Idx) (i j : Tri) (hne : i≠j) : g.colHalf c i*g.colHalf c j=0 := by
  unfold colHalf
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro t _
  rw [Finset.mul_sum]
  exact Finset.sum_eq_zero (fun s _ => g.colOrth _ _ _ (fun e =>
    hne ((Function.LeftInverse.injective (label_invol c.1)) (congrArg Prod.fst e))))

theorem rowHalf_missing (r : Idx) (j : Tri) : g.rowHalf r j*g.X j=0 := by
  unfold rowHalf
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro s _
  simpa only [e,label_invol] using g.missing r.1 (label r.1 j) (r.2,s)

theorem colHalf_missing (c : Idx) (i : Tri) : g.colHalf c i*g.X i=0 := by
  unfold colHalf
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro t _
  have hl : label (label c.1 i) c.1=i := (label_swap _ _).trans (label_invol _ _)
  simpa only [e,hl] using g.missing (label c.1 i) c.1 (t,c.2)

theorem triple_commute (f : Tri → M) (hf : ∑ i, f i=1)
    (ho : ∀ i k, i≠k → f i*f k=0) (hz : ∀ i, f i*g.X i=0)
    (hm : ∀ i, (f i)ᴴ=f i) (i j : Tri) : f i*g.X j=g.X j*f i := by
  have left (k) : g.X k*f k=0 := by
    simpa only [Matrix.conjTranspose_mul,g.Xherm,hm,Matrix.conjTranspose_zero]
      using congrArg Matrix.conjTranspose (hz k)
  have off (a b k : Tri) (hk : a≠k) : f a*g.X b*f k=0 := by
    by_cases ha : a=b
    · subst b; rw [hz,zero_mul]
    by_cases hb : b=k
    · subst b; rw [mul_assoc,left,mul_zero]
    have h := g.Xtotal
    rw [sum_three _ a b k ha hk hb] at h
    have z := congrArg (fun m : M => f a*m*f k) h
    simp only [mul_add,add_mul,hz,zero_mul,mul_one,ho _ _ hk,zero_add,
      mul_assoc (f a) (g.X k),left,mul_zero,add_zero] at z
    exact z
  calc
    f i*g.X j = f i*g.X j*(∑ k, f k) := by rw [hf,mul_one]
    _ = f i*g.X j*f i := by
      rw [Finset.mul_sum,Finset.sum_eq_single i]
      · intro k _ hk; exact off _ _ _ hk.symm
      · simp
    _ = (∑ k, f k)*(g.X j*f i) := by
      rw [Finset.sum_mul,Finset.sum_eq_single i,mul_assoc]
      · intro k _ hk; rw [← mul_assoc]; exact off _ _ _ hk
      · simp
    _ = _ := by rw [hf,one_mul]

theorem halves_cell (r c : Idx) :
    g.rowHalf r (label r.1 c.1)*g.colHalf c (label c.1 r.1)=g.p r c := by
  rcases r with ⟨i,t⟩
  rcases c with ⟨j,s⟩
  simp only [rowHalf,colHalf,label_invol,Finset.sum_mul,Finset.mul_sum]
  change ∑ u : Bit, ∑ v : Bit, g.e i j (t,v)*g.e i j (u,s)=g.e i j (t,s)
  simp [g.tileProd,Fin.sum_univ_two]
  <;> fin_cases t <;> fin_cases s <;> simp

theorem commutes (r c : Idx) (k : Tri) : g.p r c*g.X k=g.X k*g.p r c := by
  have rr := g.triple_commute (g.rowHalf r) (g.rowHalf_total r) (g.rowHalf_orth r)
    (g.rowHalf_missing r) (fun i => by simp [rowHalf,Matrix.conjTranspose_sum,g.herm]) (label r.1 c.1) k
  have cc := g.triple_commute (g.colHalf c) (g.colHalf_total c) (g.colHalf_orth c)
    (g.colHalf_missing c) (fun i => by simp [colHalf,Matrix.conjTranspose_sum,g.herm]) (label c.1 r.1) k
  rw [← g.halves_cell r c,mul_assoc,cc,← mul_assoc,rr,mul_assoc]

end Model
end DiagonalSix
