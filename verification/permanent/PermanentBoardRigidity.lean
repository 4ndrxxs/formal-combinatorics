import PermanentShapeFamily

/-! Rigidity of coordinate pivot boards under grid symmetries, and recovery
of the actual linear space from a support bound and a free projection. -/

noncomputable section
open Matrix Equiv
namespace PermanentFive
variable {K : Type*} [Field K]

def boardSpace (K : Type*) [Field K] (S : Finset Cell) : Submodule K (Cell → K) where
  carrier := {x | ∀ u ∉ S, x u = 0}
  zero_mem' := by intro _ _; rfl
  add_mem' := by intro x y hx hy u hu; simp [hx u hu,hy u hu]
  smul_mem' := by intro a x hx u hu; simp [hx u hu]


def BoardRigidity (good : (Cell → K) → Prop) (S : Finset Cell) : Prop :=
  ∀ L : Submodule K (Cell → K), (∀ x ∈ L, good x) →
    (∀ z : Cell → K, ∃ x ∈ L, ∀ i ∈ S, x i = z i) → L ≤ boardSpace K S

private def pullSpace (e : Perm Cell) (L : Submodule K (Cell → K)) : Submodule K (Cell → K) where
  carrier := {x | x ∘ e.symm ∈ L}
  zero_mem' := L.zero_mem
  add_mem' := fun hx hy ↦ L.add_mem hx hy
  smul_mem' := fun a _ hx ↦ L.smul_mem a hx


private theorem rigid_move (good : (Cell → K) → Prop) (S : Finset Cell) (e : Perm Cell)
    (stable : ∀ y, good (y ∘ e.symm) → good y)
    (rigid : BoardRigidity good (S.map e.symm.toEmbedding)) : BoardRigidity good S := by
  intro L prop free
  let L' := pullSpace e L
  have mem (x : Cell → K) (hx : x ∈ L) : x ∘ e ∈ L' := by
    change (x ∘ e) ∘ e.symm ∈ L
    simpa [Function.comp_assoc] using hx
  have prop' (y : Cell → K) (hy : y ∈ L') : good y := stable _ (prop _ hy)
  have proj (z : Cell → K) : ∃ y ∈ L', ∀ u ∈ S.map e.symm.toEmbedding, y u = z u := by
    obtain ⟨x,hx,eq⟩ := free (z ∘ e.symm)
    refine ⟨x ∘ e,mem _ hx,?_⟩
    intro u hu
    have incl : e u ∈ S := by simpa using hu
    simpa using eq (e u) incl
  have result := rigid L' prop' proj
  intro x hx u hu
  have out : e.symm u ∉ S.map e.symm.toEmbedding := by simpa using hu
  have hz := result (mem x hx) (e.symm u) out
  simpa using hz

theorem BoardRigidity.orbit (good : (Cell → K) → Prop)
    (stable : ∀ (e : Perm Cell), GridAction e → ∀ y, good (y ∘ e.symm) → good y)
    {M S : Finset Cell} (base : BoardRigidity good M) (h : SameBoard M S) : BoardRigidity good S := by
  induction h with
  | refl => exact base
  | move e act _ ih => exact rigid_move good _ e (stable e act) ih

theorem eq_board_of_free (S : Finset Cell) (L : Submodule K (Cell → K))
    (cut : L ≤ boardSpace K S) (free : ∀ z : Cell → K, ∃ x ∈ L, ∀ i ∈ S, x i = z i) :
    L = boardSpace K S := by
  refine le_antisymm cut ?_
  intro x hx
  obtain ⟨y,hy,inside⟩ := free x
  have eq : y = x := by
    funext u
    by_cases hu : u ∈ S
    · exact inside u hu
    · exact (cut hy u hu).trans (hx u hu).symm
  exact eq ▸ hy

#print axioms BoardRigidity.orbit
end PermanentFive
