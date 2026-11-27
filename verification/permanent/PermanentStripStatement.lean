import PermanentTenKernel
import PermanentFifteenNilpotence
import Mathlib.Basic.Complex.Basic

/-! Literal coordinate statement for two-row and three-row strips over the
complex numbers. Rows and columns are indexed from zero to four. -/

open Matrix Module PermanentFive QuinticPencil

private def ParallelLines (d : ℕ) (S : Finset Cell) : Prop :=
  ∃ I : Finset (Fin 5), I.card = d ∧
    ((∀ u : Cell, u ∈ S ↔ u.1 ∈ I) ∨ (∀ u : Cell, u ∈ S ↔ u.2 ∈ I))

private theorem orbit_lines {S T : Finset Cell} {d : ℕ} (h : SameBoard S T)
    (seed : ParallelLines d S) : ParallelLines d T := by
  induction h with
  | refl => exact seed
  | @move T e act _ ih =>
    obtain ⟨I,card,row | col⟩ := ih
    · cases act with
      | rowCol r c =>
        refine ⟨I.map r.toEmbedding,by simpa using card,Or.inl ?_⟩
        rintro ⟨i,j⟩
        simpa using row (r.symm i,c.symm j)
      | transpose =>
        exact ⟨I,card,Or.inr (fun u ↦ by simpa using row (u.2,u.1))⟩
    · cases act with
      | rowCol r c =>
        refine ⟨I.map c.toEmbedding,by simpa using card,Or.inr ?_⟩
        rintro ⟨i,j⟩
        simpa using col (r.symm i,c.symm j)
      | transpose =>
        exact ⟨I,card,Or.inl (fun u ↦ by simpa using col (u.2,u.1))⟩

private theorem literal_lines (L : Submodule ℂ (Cell → ℂ)) (S : Finset Cell) (d : ℕ)
    (strip : ParallelLines d S) (eq : L = boardSpace ℂ S) :
    ∃ I : Finset (Fin 5), I.card = d ∧
      ((∀ x, x ∈ L ↔ ∀ i ∉ I, ∀ j, x (i,j) = 0) ∨
       (∀ x, x ∈ L ↔ ∀ j ∉ I, ∀ i, x (i,j) = 0)) := by
  obtain ⟨I,card,hr | hc⟩ := strip
  · refine ⟨I,card,Or.inl ?_⟩
    intro x
    rw [eq]
    exact ⟨fun h i hi j ↦ h (i,j) (fun hs ↦ hi ((hr _).mp hs)),
      fun h u hu ↦ h u.1 (fun hi ↦ hu ((hr _).mpr hi)) u.2⟩
  · refine ⟨I,card,Or.inr ?_⟩
    intro x
    rw [eq]
    exact ⟨fun h j hj i ↦ h (i,j) (fun hs ↦ hj ((hc _).mp hs)),
      fun h u hu ↦ h u.2 (fun hj ↦ hu ((hc _).mpr hj)) u.1⟩

theorem complex_size_twenty_one_strips
    (b c : Fin 20 → Cell → ℂ) (D : Fin 20 → Fin 20 → Cell → ℂ)
    (rep : per ℂ Idx = regularDet b c D) :
    (∀ d ∈ ({2,3} : Finset ℕ), finrank ℂ (endpoints b c).ker = 5*d →
      ∃ I : Finset (Fin 5), I.card = d ∧
        ((∀ x, x ∈ (endpoints b c).ker ↔ ∀ i ∉ I, ∀ j, x (i,j) = 0) ∨
         (∀ x, x ∈ (endpoints b c).ker ↔ ∀ j ∉ I, ∀ i, x (i,j) = 0))) ∧
    (finrank ℂ (endpoints b c).ker = 15 → ∀ x ∈ (endpoints b c).ker,
       (Matrix.of (fun a e ↦ ∑ j, D a e j*x j))^4 = 0) := by
  constructor
  · intro d hd dim
    simp only [Finset.mem_insert,Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · obtain ⟨S,h,eq⟩ := ten_kernel_equals_strip b c D rep (by decide) dim
      apply literal_lines _ S _ (orbit_lines h ?_) eq
      refine ⟨{0,1},by decide,Or.inl ?_⟩
      rintro ⟨i,j⟩
      fin_cases i <;> fin_cases j <;> decide +kernel
    · obtain ⟨S,h,eq⟩ := fifteen_kernel_equals_strip b c D rep (by decide) dim
      apply literal_lines _ S _ (orbit_lines h ?_) eq
      refine ⟨{0,1,2},by decide,Or.inl ?_⟩
      rintro ⟨i,j⟩
      fin_cases i <;> fin_cases j <;> decide +kernel
  · intro dim x hx
    exact fifteen_transfer_fourth_zero b c D rep (by decide) dim x hx

#print axioms complex_size_twenty_one_strips
