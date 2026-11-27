import PermanentFullLine

/-! In a size-twenty-one pencil the actual endpoint kernel must intersect
every union of selected rows and columns. The lower bound for the
intersection dimension is the smaller of the two numbers of selected lines. -/

noncomputable section
open Matrix Module QuinticPencil
namespace PermanentFive
variable {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]

/-- Pushing the selected rows and columns past their complementary rectangle.
The original weights break ties between cells. -/
def priorityWeights (R C : Finset Idx) : GridWeights where
  row i := 5*i.val + if i ∈ R then 100 else 0
  col j := j.val + if j ∈ C then 100 else 0

private theorem ordinary_residue (R C : Finset Idx) (u : Cell) :
    (priorityWeights R C).cell u % 100 = weight u := by
  rcases u with ⟨i,j⟩
  have hi := i.isLt
  have hj := j.isLt
  by_cases hr : i ∈ R <;> by_cases hc : j ∈ C <;>
    simp only [priorityWeights,GridWeights.cell,weight,hr,hc,ite_true,ite_false,add_zero]
    <;> omega

theorem priority_injective (R C : Finset Idx) : Function.Injective (priorityWeights R C).cell := by
  intro a b eq
  apply weight_injective
  obtain eq' := congrArg (fun v : ℕ ↦ v % 100) eq
  simpa only [ordinary_residue] using eq'

private theorem outside_before_inside (R C : Finset Idx) (a b : Cell)
    (ha : a.1 ∉ R) (hb : a.2 ∉ C) (inside : b.1 ∈ R ∨ b.2 ∈ C) :
    (priorityWeights R C).cell a < (priorityWeights R C).cell b := by
  have hi := a.1.isLt
  have hj := a.2.isLt
  by_cases hr : b.1 ∈ R <;> by_cases hc : b.2 ∈ C <;>
    simp_all only [priorityWeights,GridWeights.cell,ite_true,ite_false,add_zero,or_self]
    <;> omega

/-- Matrices supported on the union of the rows in R and the columns in C. -/
def rowsColsSpace (K : Type*) [Field K] (R C : Finset Idx) : Submodule K (Cell → K) where
  carrier := {x | ∀ u : Cell, u.1 ∉ R → u.2 ∉ C → x u = 0}
  zero_mem' := by intro _ _ _; rfl
  add_mem' := by
    intro x y hx hy u hu hv
    simp [hx u hu hv,hy u hu hv]
  smul_mem' := by
    intro k x hx u hu hv
    simp [hx u hu hv]

private theorem line_overlap (R C : Finset Idx) (S : Finset Cell) (full : ContainsFullLine S) :
    min R.card C.card ≤ (S.filter (fun u ↦ u.1 ∈ R ∨ u.2 ∈ C)).card := by
  obtain ⟨axis,i,h⟩ := full
  cases axis with
  | false =>
    let f (j : Idx) : Cell := (i,j)
    have inj : Function.Injective f := fun _ _ e ↦ congrArg Prod.snd e
    calc
      min R.card C.card ≤ C.card := min_le_right _ _
      _ = (C.image f).card := (Finset.card_image_of_injective _ inj).symm
      _ ≤ _ := Finset.card_le_card (by
        intro u hu
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hu
        exact Finset.mem_filter.mpr ⟨h j,Or.inr hj⟩)
  | true =>
    let f (j : Idx) : Cell := (j,i)
    have inj : Function.Injective f := fun _ _ e ↦ congrArg Prod.fst e
    calc
      min R.card C.card ≤ R.card := min_le_left _ _
      _ = (R.image f).card := (Finset.card_image_of_injective _ inj).symm
      _ ≤ _ := Finset.card_le_card (by
        intro u hu
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hu
        exact Finset.mem_filter.mpr ⟨h j,Or.inl hj⟩)

/-- For every choice of rows and columns the actual endpoint kernel contains
at least min(|R|,|C|) independent matrices supported on their union. -/
theorem kernel_rows_cols_dimension (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (small : Fintype.card n ≤ 20)
    (R C : Finset Idx) :
    min R.card C.card ≤ finrank K ↥((endpoints b c).ker ⊓ rowsColsSpace K R C) := by
  let L := (endpoints b c).ker
  let w := priorityWeights R C
  obtain ⟨S,card,lift,leading,paths⟩ :=
    PermanentDegeneration.coordinate_paths_with_leading L w.cell (priority_injective R C)
  have full := normalized_full_line_weighted w b c D rep small S card lift paths
  let T := S.filter (fun u ↦ u.1 ∈ R ∨ u.2 ∈ C)
  refine (line_overlap R C S full).trans ?_
  apply PermanentDegeneration.card_le_finrank_of_leading _ w.cell (priority_injective R C) T
  intro i hi
  obtain ⟨hs,hselect⟩ := Finset.mem_filter.mp hi
  obtain ⟨x,hx,one,earlier⟩ := leading i hs
  exact ⟨x,⟨hx,fun j hr hc ↦ earlier j (outside_before_inside R C j i hr hc hselect)⟩,one,earlier⟩

/-- On each of the twenty-five single-row/single-column crosses the nine
endpoint columns have a nontrivial linear dependency. -/
theorem kernel_on_every_cross (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (small : Fintype.card n ≤ 20) (r k : Idx) :
    ∃ x ∈ (endpoints b c).ker, x ≠ 0 ∧ ∀ u : Cell, u.1 ≠ r → u.2 ≠ k → x u = 0 := by
  let V : Submodule K (Cell → K) := (endpoints b c).ker ⊓ rowsColsSpace K {r} {k}
  have pos : 1 ≤ finrank K V := by
    simpa only [Finset.card_singleton,min_self] using
      kernel_rows_cols_dimension b c D rep small {r} {k}
  have ne : V ≠ ⊥ := by
    intro eq
    rw [eq,finrank_bot] at pos
    omega
  obtain ⟨x,hx,nz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ne
  exact ⟨x,hx.1,nz,fun u hr hc ↦ hx.2 u (by simpa using hr) (by simpa using hc)⟩

#print axioms kernel_rows_cols_dimension
#print axioms kernel_on_every_cross
end PermanentFive
