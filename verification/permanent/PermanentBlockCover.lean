import PermanentPrincipal
import PermanentBlockShapes
import PermanentCover

/-! The three-line cover reduces every support of size at most thirteen
to one of four nonsingular thirteen-cell blocks. -/

noncomputable section
open Equiv Finset MvPolynomial
namespace PermanentFive
variable {K : Type*} [Field K]

/-- Coordinate changes needed in the covering argument. -/
inductive GridAction : Perm Cell → Prop
  | rowCol (r c : Perm Idx) : GridAction (r.prodCongr c)
  | transpose : GridAction (Equiv.prodComm Idx Idx)

theorem GridAction.rename {e : Perm Cell} (a : GridAction e) (R : Type*) [CommRing R] :
    MvPolynomial.rename e (per R Idx) = per R Idx := by
  cases a with
  | rowCol r c => exact row_column_rename r c
  | transpose => exact transpose_rename

/-- Downward-closure and equivariance suffice for the four-board reduction. -/
structure CoverRule (P : Finset Cell → Prop) : Prop where
  mono : ∀ {S T}, P T → S ⊆ T → P S
  relabel : ∀ {S T}, P T → (e : Perm Cell) → GridAction e → (∀ i ∈ S, e.symm i ∈ T) → P S

variable {P : Finset Cell → Prop}

/-- Put the first of two indices at zero and, when distinct, the second
at one. For two indices of the three-row strip this preserves the strip. -/
private def align (a b : Idx) : Perm Idx :=
  (swap a 0).trans (swap ((swap a 0) b) (if b=a then 0 else 1))

private theorem align_first : ∀ a b : Idx, align a b a = 0 := by decide +kernel
private theorem align_second : ∀ a b : Idx, align a b b = (if b=a then 0 else 1) := by decide +kernel
private theorem align_inside : ∀ a b i : Idx, a.val < 3 → b.val < 3 → i.val < 3 →
    (align a b i).val < 3 := by decide +kernel
private theorem strip_card : threeRows.card = 15 := by decide +kernel

private theorem in_strip (rule : CoverRule P) (S : Finset Cell) (sub : S ⊆ threeRows) (small : S.card ≤ 13)
    (row : P rowPairBoard) (col : P colPairBoard)
    (cross : P crossPairBoard) : P S := by
  have count := Finset.card_sdiff_of_subset sub
  rw [strip_card] at count
  obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp (show 1 < (threeRows \ S).card by omega)
  obtain ⟨ha,na⟩ := mem_sdiff.mp ha
  obtain ⟨hb,nb⟩ := mem_sdiff.mp hb
  let r := align a.1 b.1
  let c := align a.2 b.2
  let e := r.prodCongr c
  have sym : GridAction e.symm := .rowCol r.symm c.symm
  have mem (i : Cell) (hi : i ∈ S) : e i ∈ threeRows := by
    have h := align_inside a.1 b.1 i.1 (by simpa [threeRows] using ha)
      (by simpa [threeRows] using hb) (by simpa [threeRows] using sub hi)
    simpa [threeRows,e,r] using h
  have first : e a = ((0,0) : Cell) :=
    Prod.ext (align_first a.1 b.1) (align_first a.2 b.2)
  have second : e b = ((if b.1=a.1 then 0 else 1),(if b.2=a.2 then 0 else 1)) :=
    Prod.ext (align_second a.1 b.1) (align_second a.2 b.2)
  have omitFirst (i : Cell) (hi : i ∈ S) : e i ≠ ((0,0) : Cell) :=
    fun h ↦ na ((e.injective (h.trans first.symm)) ▸ hi)
  have omitSecond (i : Cell) (hi : i ∈ S) : e i ≠ e b :=
    fun h ↦ nb ((e.injective h) ▸ hi)
  by_cases hr : b.1 = a.1
  · have hc : b.2 ≠ a.2 := fun h ↦ ne (Prod.ext hr h).symm
    have eb : e b = ((0,1) : Cell) := by simpa [hr,hc] using second
    apply rule.relabel row e.symm sym
    intro i hi
    exact mem_erase.mpr ⟨fun h ↦ omitSecond i hi (h.trans eb.symm),mem_erase.mpr ⟨omitFirst i hi,mem i hi⟩⟩
  · by_cases hc : b.2 = a.2
    · have eb : e b = ((1,0) : Cell) := by simpa [hr,hc] using second
      apply rule.relabel col e.symm sym
      intro i hi
      exact mem_erase.mpr ⟨fun h ↦ omitSecond i hi (h.trans eb.symm),mem_erase.mpr ⟨omitFirst i hi,mem i hi⟩⟩
    · have eb : e b = ((1,1) : Cell) := by simpa [hr,hc] using second
      apply rule.relabel cross e.symm sym
      intro i hi
      exact mem_erase.mpr ⟨fun h ↦ omitSecond i hi (h.trans eb.symm),mem_erase.mpr ⟨omitFirst i hi,mem i hi⟩⟩

private def headIndices (d : ℕ) : Finset Idx := univ.filter (fun i ↦ i.val < d)
private theorem head0 : (headIndices 0).card = 0 := by decide +kernel
private theorem head1 : (headIndices 1).card = 1 := by decide +kernel
private theorem head2 : (headIndices 2).card = 2 := by decide +kernel
private theorem head3 : (headIndices 3).card = 3 := by decide +kernel

private theorem align_cover (rule : CoverRule P) (S : Finset Cell) (R C : Finset Idx) (r c : ℕ)
    (hr : R.card ≤ (headIndices r).card) (hc : C.card ≤ (headIndices c).card)
    (cov : ∀ i ∈ S, i.1 ∈ R ∨ i.2 ∈ C) :
    ∃ T : Finset Cell, T.card = S.card ∧ (∀ i ∈ T, i.1.val < r ∨ i.2.val < c) ∧
      (P T → P S) := by
  obtain ⟨p,hp⟩ := move_into R (headIndices r) hr
  obtain ⟨q,hq⟩ := move_into C (headIndices c) hc
  let e := p.prodCongr q
  let T := S.map e.toEmbedding
  refine ⟨T,Finset.card_map _,?_,?_⟩
  · intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
    rcases cov j hj with a | b
    · exact Or.inl (Finset.mem_filter.mp (hp j.1 a)).2
    · exact Or.inr (Finset.mem_filter.mp (hq j.2 b)).2
  · intro witness
    apply rule.relabel witness e.symm (.rowCol p.symm q.symm)
    intro i hi
    exact Finset.mem_map.mpr ⟨i,hi,rfl⟩

private theorem sided (rule : CoverRule P) (S : Finset Cell) (small : S.card ≤ 13)
    (R C : Finset Idx) (cost : R.card+C.card ≤ 3) (orient : C.card ≤ R.card)
    (cov : ∀ i ∈ S, i.1 ∈ R ∨ i.2 ∈ C)
    (row : P rowPairBoard) (col : P colPairBoard)
    (cross : P crossPairBoard) (mixed : P mixedBoard) :
    P S := by
  by_cases zero : C.card = 0
  · obtain ⟨T,card,h,back⟩ := align_cover rule S R C 3 0 (by rw [head3]; omega)
      (by rw [head0]; omega) cov
    apply back (in_strip rule T (fun i hi ↦ ?_) (card ▸ small) row col cross)
    have bound := h i hi
    simpa [threeRows] using bound
  · obtain ⟨T,_,h,back⟩ := align_cover rule S R C 2 1 (by rw [head2]; omega)
      (by rw [head1]; omega) cov
    exact back (rule.mono mixed (fun i hi ↦ by simpa [mixedBoard] using h i hi))

/-- The four fixed principal blocks suffice for every small support with
matching number at most three. -/
theorem small_cover_property (rule : CoverRule P) (S : Finset Cell) (small : S.card ≤ 13)
    (matching : ∀ p : Perm Idx, (univ.filter (fun i ↦ p i ∈ PermanentCover.neighbors S i)).card ≤ 3)
    (row : P rowPairBoard) (col : P colPairBoard)
    (cross : P crossPairBoard) (mixed : P mixedBoard) :
    P S := by
  obtain ⟨R,C,cost,covers⟩ := PermanentCover.cover (PermanentCover.neighbors S) 3 (by decide) matching
  have cov (i : Cell) (hi : i ∈ S) : i.1 ∈ R ∨ i.2 ∈ C :=
    covers i.1 i.2 (by simpa [PermanentCover.neighbors] using hi)
  by_cases orient : C.card ≤ R.card
  · exact sided rule S small R C cost orient cov row col cross mixed
  · let e := Equiv.prodComm Idx Idx
    let T := S.map e.toEmbedding
    have transCov (i : Cell) (hi : i ∈ T) : i.1 ∈ C ∨ i.2 ∈ R := by
      obtain ⟨j,hj,rfl⟩ := mem_map.mp hi
      exact (cov j hj).symm
    have witness := sided rule T (by simpa [T] using small) C R (by omega) (by omega)
      transCov row col cross mixed
    apply rule.relabel witness e.symm .transpose
    intro i hi
    exact mem_map.mpr ⟨i,hi,rfl⟩

theorem small_covered_block (S : Finset Cell) (small : S.card ≤ 13)
    (matching : ∀ p : Perm Idx, (univ.filter (fun i ↦ p i ∈ PermanentCover.neighbors S i)).card ≤ 3)
    (row : HasThirteenBlock K rowPairBoard) (col : HasThirteenBlock K colPairBoard)
    (cross : HasThirteenBlock K crossPairBoard) (mixed : HasThirteenBlock K mixedBoard) :
    HasThirteenBlock K S := by
  let rule : CoverRule (HasThirteenBlock K) :=
    ⟨fun w h ↦ w.mono h,fun w e h sub ↦ w.relabel e (h.rename K) sub⟩
  exact small_cover_property rule S small matching row col cross mixed

#print axioms small_covered_block
end PermanentFive
