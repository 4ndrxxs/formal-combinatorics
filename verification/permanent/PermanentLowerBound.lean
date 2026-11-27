import PermanentWitnesses
import PermanentSymmetry
import PermanentHoleFit
import PermanentMissingWitness
import Mathlib.Algebra.CharZero.Infinite

/-! A finite lower bound for regular affine determinantal representations
of the generic permanent of order five. -/

noncomputable section
open MvPolynomial Matrix Equiv Finset
namespace PermanentFive
open QuinticPencil

private def board (S : Finset Cell) : PermanentSupports.Grid :=
  fun i j ↦ if (i,j) ∈ S then 1 else 0

private def selected (S : Finset Cell) (p : Perm Idx) : Finset Idx :=
  univ.filter (fun i ↦ (i,p i) ∈ S)

private lemma board_size (S : Finset Cell) : PermanentSupports.size (board S) = S.card := by
  change (∑ i : Idx, ∑ j : Idx, ((if (i,j) ∈ S then 1 else 0 : Fin 2) : ℕ)) = S.card
  simp only [apply_ite Fin.val]
  rw [← Fintype.sum_prod_type']
  simp

private lemma board_hits (S : Finset Cell) (p : Perm Idx) :
    PermanentSupports.hits (board S) p = (selected S p).card := by
  change (∑ i : Idx, ((if (i,p i) ∈ S then 1 else 0 : Fin 2) : ℕ)) = _
  rw [selected,Finset.card_filter]
  simp [apply_ite Fin.val]

private def prefixSet (d : ℕ) : Finset Idx := univ.filter (fun i ↦ i.val < d)
private theorem count3 : (prefixSet 3).card = 3 := by decide +kernel
private theorem count4 : (prefixSet 4).card = 4 := by decide +kernel

private def Fits (S : Finset Cell) (e : Perm Cell) (z : Cell → ℤ) :=
  ∀ j, z j ≠ 0 → e j ∈ S

private def Symm (K : Type*) [CommRing K] (e : Perm Cell) :=
  rename e (per K Idx) = per K Idx

private theorem matching_fits (K : Type*) [Field K] (S : Finset Cell) (p : Perm Idx)
    (d : ℕ) (le : (prefixSet d).card ≤ PermanentSupports.hits (board S) p) :
    ∃ e : Perm Cell, Symm K e ∧ Fits S e (matchPoint d) := by
  rw [board_hits] at le
  obtain ⟨q,move⟩ := move_into (prefixSet d) (selected S p) le
  refine ⟨q.prodCongr (q.trans p),row_column_rename _ _,?_⟩
  rintro ⟨i,j⟩ nonzero
  have eq : i = j ∧ i.val < d := by simpa [matchPoint] using nonzero
  obtain ⟨rfl,small⟩ := eq
  simpa [selected] using move i (by simpa [prefixSet] using small)

private theorem rows_fits (K : Type*) [Field K] (S : Finset Cell)
    (lines : ∀ i j, board S i j = board S i 0)
    (count : ∑ i : PermanentSupports.I, (board S i 0 : ℕ) = 3) :
    ∃ e : Perm Cell, Symm K e ∧ Fits S e rowPoint := by
  let active : Finset Idx := univ.filter (fun i ↦ (i,0) ∈ S)
  have card : active.card = 3 := by
    dsimp only [active]
    rw [Finset.card_filter]
    simpa [board,apply_ite Fin.val] using count
  obtain ⟨q,move⟩ := move_into (prefixSet 3) active (le_of_eq (count3.trans card.symm))
  refine ⟨q.prodCongr (Equiv.refl Idx),row_column_rename _ _,?_⟩
  rintro ⟨i,j⟩ hi
  have sm : i.val < 3 := by simpa [rowPoint] using hi
  have entry : (q i,0) ∈ S := by simpa [active] using move i (by simpa [prefixSet] using sm)
  have h := lines (q i) j
  simpa [board,entry] using h

private theorem cols_fits (K : Type*) [Field K] (S : Finset Cell)
    (lines : ∀ i j, board S i j = board S 0 j)
    (count : ∑ j : PermanentSupports.I, (board S 0 j : ℕ) = 3) :
    ∃ e : Perm Cell, Symm K e ∧ Fits S e rowPoint := by
  let active : Finset Idx := univ.filter (fun j ↦ (0,j) ∈ S)
  have card : active.card = 3 := by
    dsimp only [active]
    rw [Finset.card_filter]
    simpa [board,apply_ite Fin.val] using count
  obtain ⟨q,move⟩ := move_into (prefixSet 3) active (le_of_eq (count3.trans card.symm))
  refine ⟨(Equiv.prodComm Idx Idx).trans ((Equiv.refl Idx).prodCongr q),
    rename_comp transpose_rename (row_column_rename _ _),?_⟩
  rintro ⟨i,j⟩ hi
  have sm : i.val < 3 := by simpa [rowPoint] using hi
  have entry : (0,q i) ∈ S := by simpa [active] using move i (by simpa [prefixSet] using sm)
  have h := lines j (q i)
  simpa [board,entry] using h

variable {K : Type*} [Field K] [CharZero K]

private def Admits (S : Finset Cell) (m : ℕ) (K : Type*) [Field K] :=
  ∀ z : Cell → K, (∀ j ∉ S, z j = 0) →
    (∀ i, MvPolynomial.eval z (pderiv i (per K Idx)) = 0) ∧
    26 + (hessian (per K Idx) z).rank ≤ m + S.card

omit [CharZero K] in
private theorem test_point {S : Finset Cell} {m : ℕ} (adm : Admits S m K) {e : Perm Cell}
    (sym : Symm K e) {z : Cell → ℤ} (fits : Fits S e z) :
    (∀ i, MvPolynomial.eval ((Int.castRingHom K) ∘ z) (pderiv i (per K Idx)) = 0) ∧
    26 + (hessian (per K Idx) ((Int.castRingHom K) ∘ z)).rank ≤ m + S.card := by
  let v := (Int.castRingHom K) ∘ z
  have supported (x : Cell) (hx : x ∉ S) : (v ∘ e.symm) x = 0 := by
    have h : z (e.symm x) = 0 := by
      by_contra nz
      exact hx (by simpa using fits (e.symm x) nz)
    simp [v,h]
  obtain ⟨sing,rank⟩ := adm (v ∘ e.symm) supported
  obtain ⟨grad,equal⟩ := transport e sym v
  exact ⟨fun i ↦ (grad i).symm.trans (sing (e i)),by rwa [equal] at rank⟩

/-- Over a field of characteristic zero, a regular affine determinantal
representation of the generic five-by-five permanent has size at least 16. -/
theorem regular_bound {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (F : Cell → Matrix n n K) (regular : Fintype.card n = A.rank+1)
    (rep : per K Idx = (affineMatrix A F).det) : 16 ≤ Fintype.card n := by
  by_contra! small
  obtain ⟨S,adm⟩ := regular_coordinate_support A F regular rep
  have hS : Admits S (Fintype.card n) K := adm
  have base := (adm 0 (by simp)).2
  have large : 10 < S.card := by omega
  have bound (p : Perm Idx) : PermanentSupports.hits (board S) p ≤ 3 := by
    by_contra! four
    obtain ⟨e,sym,fit⟩ := matching_fits K S p 4 (by rw [count4]; omega)
    have impossible := (test_point hS sym fit).1 (4,4)
    rw [four_gradient] at impossible
    exact one_ne_zero impossible
  have max := PermanentSupports.size_le (board S) 3 bound
  rw [board_size] at max
  obtain ⟨p,hits⟩ := PermanentSupports.exists_three (board S) (by rwa [board_size]) bound
  obtain ⟨e,sym,fit⟩ := matching_fits K S p 3 (by rw [count3,hits])
  have r := (test_point hS sym fit).2
  have r4 := match_rank K
  have card : S.card = 15 := by omega
  obtain rows | cols := PermanentSupports.extremal (board S) (by rwa [board_size]) bound
  · obtain ⟨e,sym,fit⟩ := rows_fits K S rows.1 rows.2
    have h := (test_point hS sym fit).2
    have h5 := row_rank K
    omega
  · obtain ⟨e,sym,fit⟩ := cols_fits K S cols.1 cols.2
    have h := (test_point hS sym fit).2
    have h5 := row_rank K
    omega

private theorem active_hole (i j : Idx) (nz : rowHole (i,j) ≠ 0) :
    i.val < 3 ∧ (i,j) ≠ ((0,0) : Cell) := by
  by_cases e : (i,j) = ((0,0) : Cell)
  · simp [rowHole,e] at nz
  · exact ⟨by simpa [rowHole,rowPoint,e] using nz,e⟩

omit [CharZero K] in
private theorem hole_fits (S : Finset Cell) (large : 14 ≤ S.card)
    (lines : (∃ R : Finset Idx, R.card=3 ∧ S ⊆ R.product univ) ∨
      (∃ C : Finset Idx, C.card=3 ∧ S ⊆ (univ : Finset Idx).product C)) :
    ∃ e : Perm Cell, Symm K e ∧ Fits S e rowHole := by
  classical
  rcases lines with ⟨R,hR,sub⟩ | ⟨C,hC,sub⟩
  · obtain ⟨q,v,fit⟩ := almost_rows S R hR sub large
    refine ⟨q.prodCongr v,row_column_rename _ _,?_⟩
    rintro ⟨i,j⟩ nz
    exact fit i j (active_hole i j nz).1 (active_hole i j nz).2
  · let S' := S.map (Equiv.prodComm Idx Idx).toEmbedding
    have mem (i j : Idx) : (i,j) ∈ S' ↔ (j,i) ∈ S := by
      simp [S',Finset.mem_map_equiv]
    have sub' : S' ⊆ C.product univ := by
      rintro ⟨i,j⟩ h
      exact mem_product.mpr ⟨(mem_product.mp (sub ((mem i j).mp h))).2,mem_univ _⟩
    have large' : 14 ≤ S'.card := by simpa [S'] using large
    obtain ⟨q,v,fit⟩ := almost_rows S' C hC sub' large'
    refine ⟨(q.prodCongr v).trans (Equiv.prodComm Idx Idx),
      rename_comp (row_column_rename _ _) transpose_rename,?_⟩
    rintro ⟨i,j⟩ nz
    exact (mem (q i) (v j)).mp (fit i j (active_hole i j nz).1 (active_hole i j nz).2)

/-- A coordinate support satisfying the size-sixteen endpoint inequalities
has exactly ten entries. -/
theorem size_sixteen_support (S : Finset Cell)
    (adm : ∀ z : Cell → K, (∀ j ∉ S, z j = 0) →
      (∀ i, MvPolynomial.eval z (pderiv i (per K Idx)) = 0) ∧
      26 + (hessian (per K Idx) z).rank ≤ 16 + S.card) : S.card = 10 := by
  have hS : Admits S 16 K := adm
  have base := (adm 0 (by simp)).2
  have bound (p : Perm Idx) : PermanentSupports.hits (board S) p ≤ 3 := by
    by_contra! four
    obtain ⟨e,sym,fit⟩ := matching_fits K S p 4 (by rw [count4]; omega)
    have impossible := (test_point hS sym fit).1 (4,4)
    rw [four_gradient] at impossible
    exact one_ne_zero impossible
  have max := PermanentSupports.size_le (board S) 3 bound
  rw [board_size] at max
  by_contra neq
  have more : 10 < S.card := by omega
  obtain ⟨p,hits⟩ := PermanentSupports.exists_three (board S) (by rwa [board_size]) bound
  obtain ⟨e,sym,fit⟩ := matching_fits K S p 3 (by rw [count3,hits])
  have r := (test_point hS sym fit).2
  have r4 := match_rank K
  have large : 14 ≤ S.card := by omega
  have counts (q : Perm Idx) :
      (univ.filter (fun i ↦ q i ∈ PermanentCover.neighbors S i)).card ≤ 3 := by
    have h := bound q
    rw [board_hits] at h
    simpa [PermanentCover.neighbors,selected] using h
  obtain ⟨e',sym',fit'⟩ := hole_fits (K:=K) S large (PermanentCover.parallel_lines S 3
    (Or.inr rfl) (by simpa using large) counts)
  have r' := (test_point hS sym' fit').2
  have rank6 := row_hole_rank K
  omega

private def tailPoint (c : Cell) : ℤ := if c.1=c.2 ∧ 2 ≤ c.1.val then 1 else 0
private def perInteger (x : Cell → ℤ) : ℤ := (Matrix.of fun i j ↦ x (i,j)).permanent

set_option maxRecDepth 12000 in
private theorem diagonal_values :
    perInteger (tailPoint + matchPoint 2) = 1 ∧
    perInteger (tailPoint - matchPoint 2) = 1 ∧ perInteger tailPoint = 0 := by decide +kernel

omit [CharZero K] in
private theorem per_integer_cast (x : Cell → ℤ) :
    MvPolynomial.eval ((Int.castRingHom K) ∘ x) (per K Idx) = (perInteger x : K) := by
  simp [per,perInteger,Matrix.permanent,PermanentCuts.generic,Function.comp_def]

omit [CharZero K] in
private theorem eval_symmetry (e : Perm Cell) (sym : Symm K e) (x : Cell → K) :
    MvPolynomial.eval (x ∘ e.symm) (per K Idx) = MvPolynomial.eval x (per K Idx) := by
  change rename e (per K Idx) = per K Idx at sym
  calc
    _ = MvPolynomial.eval (x ∘ e.symm) (rename e (per K Idx)) := congrArg _ sym.symm
    _ = _ := by rw [MvPolynomial.eval_rename]; simp [Function.comp_assoc]

/-- A common direction space for vanishing second differences cannot
contain two independent cells in different rows and columns. -/
theorem even_support_bound (S : Finset Cell)
    (even : ∀ z : Cell → K, (∀ j ∉ S, z j = 0) → ∀ y : Cell → K,
      MvPolynomial.eval (y+z) (per K Idx) + MvPolynomial.eval (y-z) (per K Idx) =
        2 * MvPolynomial.eval y (per K Idx)) : S.card ≤ 5 := by
  classical
  by_contra! large
  have has : ∃ p : Perm Idx, 2 ≤ PermanentSupports.hits (board S) p := by
    by_contra! no
    have h := PermanentSupports.size_le (board S) 1 (fun p ↦ by have := no p; omega)
    rw [board_size] at h
    omega
  obtain ⟨p,hp⟩ := has
  have two : (prefixSet 2).card = 2 := by decide +kernel
  obtain ⟨e,sym,fit⟩ := matching_fits K S p 2 (by rwa [two])
  let cast := Int.castRingHom K
  let z := (cast ∘ matchPoint 2) ∘ e.symm
  let y := (cast ∘ tailPoint) ∘ e.symm
  have sup (j : Cell) (hj : j ∉ S) : z j = 0 := by
    have zero : matchPoint 2 (e.symm j) = 0 := by
      by_contra nz
      exact hj (by simpa using fit (e.symm j) nz)
    simp [z,zero]
  have eq := even z sup y
  have plus : y+z = (cast ∘ (tailPoint + matchPoint 2)) ∘ e.symm := by
    ext i; simp [y,z,Function.comp_def]
  have minus : y-z = (cast ∘ (tailPoint - matchPoint 2)) ∘ e.symm := by
    ext i; simp [y,z,Function.comp_def]
  dsimp only [y] at eq
  rw [plus,minus,eval_symmetry e sym,eval_symmetry e sym,eval_symmetry e sym] at eq
  simp only [cast,per_integer_cast,diagonal_values.1,diagonal_values.2.1,diagonal_values.2.2] at eq
  norm_num at eq

#print axioms even_support_bound
#print axioms size_sixteen_support
#print axioms regular_bound
end PermanentFive
