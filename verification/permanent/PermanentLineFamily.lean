import PermanentIndexFourBlock
import PermanentAmbientEight
import PermanentSimpleZeroBound

/-! Closure rules for testing all subboards without a full coordinate line. -/

noncomputable section
open Matrix Module Equiv Finset QuinticPencil
namespace PermanentFive
variable {K : Type*} [Field K]

def linePoint (column : Bool) (i j : Idx) : Cell := if column then (j,i) else (i,j)
def ContainsFullLine (S : Finset Cell) : Prop :=
  ∃ column i, ∀ j, linePoint column i j ∈ S

def LineTest (K : Type*) [Field K] (S : Finset Cell) : Prop :=
  ContainsFullLine S ∨ HasIndexFourBlock K S ∨ HasSimpleZeroBlock K 10 S ∨
    (HasAmbientEight K S ∧ S.card ≤ 12)

def LineTestFamily (K : Type*) [Field K] (T : Finset Cell) : Prop := ∀ S ⊆ T, LineTest K S

private theorem recover_line (S : Finset Cell) (e : Perm Cell) (act : GridAction e)
    (h : ContainsFullLine (S.map e.symm.toEmbedding)) : ContainsFullLine S := by
  obtain ⟨axis,i,inside⟩ := h
  have mem (j : Idx) : e (linePoint axis i j) ∈ S := by
    simpa only [Finset.mem_map_equiv,Equiv.symm_symm] using inside j
  cases act with
  | rowCol r c =>
    cases axis with
    | false =>
      exact ⟨false,r i,fun j ↦ by simpa [linePoint] using mem (c.symm j)⟩
    | true =>
      exact ⟨true,c i,fun j ↦ by simpa [linePoint] using mem (r.symm j)⟩
  | transpose =>
    cases axis with
    | false => exact ⟨true,i,mem⟩
    | true => exact ⟨false,i,mem⟩

theorem line_family_rule : CoverRule (LineTestFamily K) := by
  constructor
  · intro S T ht sub B hb
    exact ht B (hb.trans sub)
  · intro S T ht e act sub B hb
    let C := B.map e.symm.toEmbedding
    have inc : C ⊆ T := by
      rintro _ h
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp h
      exact sub i (hb hi)
    have back : ∀ i ∈ B, e.symm i ∈ C := fun i hi ↦ Finset.mem_map.mpr ⟨i,hi,rfl⟩
    rcases ht C inc with full|witt|ten|⟨ambient,small⟩
    · exact Or.inl (recover_line B e act full)
    · exact Or.inr (Or.inl (witt.relabel e (act.rename K) back))
    · exact Or.inr (Or.inr (Or.inl (ten.relabel e (act.rename (DualNumber K)) back)))
    · obtain ⟨z,support,rank⟩ := ambient
      refine Or.inr (Or.inr (Or.inr ⟨⟨z ∘ e.symm,?_,?_⟩,?_⟩))
      · intro i hi
        apply support
        exact fun hc ↦ hi (by simpa [C,Finset.mem_map_equiv] using hc)
      · rw [(transport e (act.rename K) z).2]
        exact rank
      · simpa [C] using small

theorem family_of_witt {T : Finset Cell} (cert : HasIndexFourBlock K T) : LineTestFamily K T :=
  fun _ sub ↦ Or.inr (Or.inl (cert.mono sub))

theorem family_of_ten {T : Finset Cell} (cert : HasSimpleZeroBlock K 10 T) : LineTestFamily K T :=
  fun _ sub ↦ Or.inr (Or.inr (Or.inl (cert.mono sub)))

theorem family_by_line (T : Finset Cell) (axis : Bool) (i : Idx)
    (next : ∀ j, LineTestFamily K (T.erase (linePoint axis i j))) : LineTestFamily K T := by
  classical
  intro S sub
  by_cases full : ∀ j, linePoint axis i j ∈ S
  · exact Or.inl ⟨axis,i,full⟩
  · push Not at full
    obtain ⟨j,missing⟩ := full
    exact next j S (Finset.subset_erase.mpr ⟨sub,missing⟩)

theorem family_by_ambient (T : Finset Cell) (small : T.card ≤ 12) (cert : HasAmbientEight K T)
    (next : ∀ j ∈ T, LineTestFamily K (T.erase j)) : LineTestFamily K T := by
  classical
  intro S sub
  by_cases same : S = T
  · subst S
    exact Or.inr (Or.inr (Or.inr ⟨cert,small⟩))
  · obtain ⟨j,hj,out⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (Finset.card_lt_card (lt_of_le_of_ne sub same))
    exact next j hj S (Finset.subset_erase.mpr ⟨sub,out⟩)

def moveCell (flip : Bool) (r c : Perm Idx) (u : Cell) : Cell :=
  (r.prodCongr c) (if flip then u.swap else u)

theorem move_family {S T : Finset Cell} (ht : LineTestFamily K T)
    (flip : Bool) (r c : Perm Idx) (inc : ∀ j ∈ S, moveCell flip r c j ∈ T) : LineTestFamily K S := by
  cases flip with
  | false =>
    exact line_family_rule.relabel ht (r.prodCongr c).symm (.rowCol r.symm c.symm) inc
  | true =>
    let e := Equiv.prodComm Idx Idx
    let B := S.map e.toEmbedding
    have hB : LineTestFamily K B := by
      apply line_family_rule.relabel ht (r.prodCongr c).symm (.rowCol r.symm c.symm)
      rintro _ hb
      obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hb
      exact inc j hj
    exact line_family_rule.relabel hB e.symm .transpose (fun j hj ↦ Finset.mem_map.mpr ⟨j,hj,rfl⟩)

#print axioms line_family_rule
end PermanentFive
