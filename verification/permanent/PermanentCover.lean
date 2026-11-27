import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Set

/-! A cover of a five-by-five support by whole rows and whole columns.
Dummy columns turn a lower bound on the matching size into the ordinary
finite Hall condition. -/

noncomputable section
namespace PermanentCover
open Finset Function
abbrev Idx := Fin 5

private theorem extend_matching (adj : Idx → Finset Idx) (k : ℕ)
    (f : Idx → Idx ⊕ Fin k) (inj : Injective f)
    (ok : ∀ i, f i ∈ (adj i).disjSum univ) :
    ∃ p : Equiv.Perm Idx, 5 ≤ (univ.filter (fun i ↦ p i ∈ adj i)).card + k := by
  classical
  let A : Finset Idx := univ.filter (fun i ↦ ∃ j : Idx, f i = Sum.inl j)
  have choices (i : A) : ∃ j : Idx, f i = Sum.inl j := (mem_filter.mp i.property).2
  choose g hg using choices
  have gi : Injective g := by
    intro a b eq
    exact Subtype.ext (inj ((hg a).trans ((congrArg Sum.inl eq).trans (hg b).symm)))
  let e : {i : Idx // i ∈ A} ≃ {j : Idx // j ∈ Set.range g} := Equiv.ofInjective g gi
  let p := e.extendSubtype
  have sub : A ⊆ univ.filter (fun i ↦ p i ∈ adj i) := by
    intro i hi
    have e1 : p i = g ⟨i,hi⟩ := e.extendSubtype_apply_of_mem i hi
    have h := ok i
    rw [hg ⟨i,hi⟩] at h
    exact mem_filter.mpr ⟨mem_univ _,by simpa [e1] using h⟩
  have missing (i : ↥(Aᶜ)) : ∃ j : Fin k, f i = Sum.inr j := by
    cases h : f i with
    | inl j =>
      exact False.elim ((mem_compl.mp i.property) (mem_filter.mpr ⟨mem_univ _,j,h⟩))
    | inr j => exact ⟨j,rfl⟩
  choose b hb using missing
  have bi : Injective b := by
    intro x y eq
    exact Subtype.ext (inj ((hb x).trans ((congrArg Sum.inr eq).trans (hb y).symm)))
  have small : Aᶜ.card ≤ k := by simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective b bi
  have total := Finset.card_compl_add_card A
  have le := card_le_card sub
  exact ⟨p,by simp only [Fintype.card_fin] at total; omega⟩

/-- If each permutation meets at most d occupied cells, the support is
covered by at most d individual rows and columns in total. -/
theorem cover (adj : Idx → Finset Idx) (d : ℕ) (hd : d ≤ 4)
    (bound : ∀ p : Equiv.Perm Idx, (univ.filter (fun i ↦ p i ∈ adj i)).card ≤ d) :
    ∃ R C : Finset Idx, R.card + C.card ≤ d ∧ ∀ i j, j ∈ adj i → i ∈ R ∨ j ∈ C := by
  classical
  let k := 4 - d
  let augmented (i : Idx) : Finset (Idx ⊕ Fin k) := (adj i).disjSum univ
  have fails : ¬ ∀ A : Finset Idx, A.card ≤ (A.biUnion augmented).card := by
    intro hall
    obtain ⟨f,inj,ok⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' augmented).mp hall
    obtain ⟨p,large⟩ := extend_matching adj k f inj ok
    have small := bound p
    dsimp [k] at large
    omega
  push Not at fails
  obtain ⟨A,small⟩ := fails
  have nonempty : A.Nonempty := by
    by_contra! empty
    simp [empty] at small
  obtain ⟨a,ha⟩ := nonempty
  let N := A.biUnion adj
  have eq : A.biUnion augmented = N.disjSum (univ : Finset (Fin k)) := by
    ext u
    cases u with
    | inl j => simp [augmented,N]
    | inr j => simpa [augmented] using (show ∃ i, i ∈ A from ⟨a,ha⟩)
  rw [eq,card_disjSum,card_univ,Fintype.card_fin] at small
  have total := Finset.card_compl_add_card A
  simp only [Fintype.card_fin] at total
  refine ⟨Aᶜ,N,by dsimp [k] at small; omega,?_⟩
  intro i j hij
  by_cases hi : i ∈ A
  · exact Or.inr (mem_biUnion.mpr ⟨i,hi,hij⟩)
  · exact Or.inl (mem_compl.mpr hi)

def neighbors (S : Finset (Idx × Idx)) (i : Idx) : Finset Idx :=
  univ.filter (fun j ↦ (i,j) ∈ S)

private theorem capacity (S : Finset (Idx × Idx)) (R C : Finset Idx)
    (covers : ∀ i j, j ∈ neighbors S i → i ∈ R ∨ j ∈ C) :
    S.card ≤ R.card * 5 + (5-R.card)*C.card := by
  classical
  let A := R.product (univ : Finset Idx)
  let B := Rᶜ.product C
  have disjoint : Disjoint A B := Finset.disjoint_left.mpr (fun x hx hy ↦
    (mem_compl.mp (mem_product.mp hy).1) (mem_product.mp hx).1)
  have sub : S ⊆ A ∪ B := by
    rintro ⟨i,j⟩ h
    by_cases hi : i ∈ R
    · exact mem_union_left _ (mem_product.mpr ⟨hi,mem_univ _⟩)
    · have hj := (covers i j (by simpa [neighbors] using h)).resolve_left hi
      exact mem_union_right _ (mem_product.mpr ⟨mem_compl.mpr hi,hj⟩)
  have h := card_le_card sub
  rw [card_union_of_disjoint disjoint] at h
  change S.card ≤ (R ×ˢ (univ : Finset Idx)).card + (Rᶜ ×ˢ C).card at h
  simpa only [card_product,card_compl,card_univ,Fintype.card_fin] using h

private theorem pure_counts (r c d : ℕ) (cases : d = 2 ∨ d = 3) (cost : r+c ≤ d)
    (large : (if d=2 then 10 else 14) ≤ r*5 + (5-r)*c) :
    (r=d ∧ c=0) ∨ (r=0 ∧ c=d) := by
  have hr : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases cases with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl <;>
    norm_num at * <;> omega

/-- Near-full supports with matching number at most three use parallel
lines. At matching number two and ten entries all occupied lines are full. -/
theorem parallel_lines (S : Finset (Idx × Idx)) (d : ℕ) (cases : d=2 ∨ d=3)
    (large : (if d=2 then 10 else 14) ≤ S.card)
    (bound : ∀ p : Equiv.Perm Idx, (univ.filter (fun i ↦ p i ∈ neighbors S i)).card ≤ d) :
    (∃ R : Finset Idx, R.card=d ∧ S ⊆ R.product univ) ∨
    (∃ C : Finset Idx, C.card=d ∧ S ⊆ (univ : Finset Idx).product C) := by
  classical
  obtain ⟨R,C,cost,covers⟩ := cover (neighbors S) d (by omega) bound
  have cap := capacity S R C covers
  obtain ⟨hr,hc⟩ | ⟨hr,hc⟩ := pure_counts _ _ _ cases cost (large.trans cap)
  · have emp := card_eq_zero.mp hc
    refine Or.inl ⟨R,hr,?_⟩
    rintro ⟨i,j⟩ hij
    have h := covers i j (by simpa [neighbors] using hij)
    exact mem_product.mpr ⟨h.resolve_right (by simp [emp]),mem_univ _⟩
  · have emp := card_eq_zero.mp hr
    refine Or.inr ⟨C,hc,?_⟩
    rintro ⟨i,j⟩ hij
    have h := covers i j (by simpa [neighbors] using hij)
    exact mem_product.mpr ⟨mem_univ _,h.resolve_left (by simp [emp])⟩

#print axioms cover
#print axioms parallel_lines
end PermanentCover
