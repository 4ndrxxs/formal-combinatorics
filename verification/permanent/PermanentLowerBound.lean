import PermanentWitnesses
import PermanentSymmetry
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

#print axioms regular_bound
end PermanentFive
