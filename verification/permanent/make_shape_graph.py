"""Emit the independently kernel-checked finite reduction for full-line boards."""
from check_quintic_layout import permutation_term
from check_quintic_restricted import vector
from check_quintic_line_cover import STRIP, MIXED, board_order, canonical


def graph_source(nodes, labels):
    boards = sorted(nodes,key=board_order)
    perms = []
    def index(p):
        if p not in perms:
            perms.append(p)
        return perms.index(p)
    for board in boards:
        kind = labels[board]
        if kind[0] == "rank":
            index(kind[2][1])
            index(kind[2][2])
        for _, (_, r, c) in nodes[board].values():
            index(r)
            index(c)
    n = len(boards)
    k = len(perms)
    tags, rows = [], []
    for i, board in enumerate(boards):
        label = labels[board]
        if label[0] == "rank":
            flip,r,c = label[2]
            tags.append(f".minor {label[1]} {str(flip).lower()} {index(r)} {index(c)}")
        else:
            tags.append(f".allowed {label[1]}")
        packed = [0]*25
        for x, (child,(flip,r,c)) in nodes[board].items():
            j = boards.index(child)
            assert j < i
            packed[x] = 1+((2*j+int(flip))*k+index(r))*k+index(c)
        rows.append(vector(vector(map(str,packed[j:j+5])) for j in range(0,25,5)))
    src = """import PermanentShapeFamily

/-! Exhaust all full-line subboards of the two three-line covers.
A zero edge denotes a deletion with no complete line. Each positive edge
encodes its smaller target and the row/column relabelling. -/

open Equiv Finset
namespace PermanentFive
"""
    src += f"private def permutation : Fin {k} → Perm Idx :=\n  "+vector(permutation_term(p) for p in perms)+"\n\n"
    src += f"""private inductive Own where
  | allowed (j : Fin 12)
  | minor (j : Fin 4) (flip : Bool) (r c : Fin {k})

private def tag : Fin {n} → Own :=
  ![{", ".join(tags)}]

private def edge : Fin {n} → Idx → Idx → ℕ :=
  !["""
    src += ",\n    ".join(rows)+"]\n\n"
    src += f"""private def child (v : ℕ) : Fin {n} := ⟨(v-1)/{2*k*k}%{n},Nat.mod_lt _ (by decide)⟩
private def flipped (v : ℕ) : Bool := (v-1)/{k*k}%2 == 1
private def rowPerm (v : ℕ) : Fin {k} := ⟨(v-1)/{k}%{k},Nat.mod_lt _ (by decide)⟩
private def colPerm (v : ℕ) : Fin {k} := ⟨(v-1)%{k},Nat.mod_lt _ (by decide)⟩

private def ownFacts (i : Fin {n}) : Prop :=
  match tag i with
  | .allowed j => shapeBoard i = shapeModel j
  | .minor j fl r c => (shapeBoard i).card < shapeRank j+5 ∧
      ∀ u ∈ shapePattern j, moveCell fl (permutation r) (permutation c) u ∈ shapeBoard i

private instance (i : Fin {n}) : Decidable (ownFacts i) := by
  unfold ownFacts
  cases tag i <;> infer_instance

private instance (S : Finset Cell) : Decidable (ContainsFullLine S) := by
  unfold ContainsFullLine
  infer_instance

private def edgeFacts (i : Fin {n}) (x : Cell) : Prop :=
  let v := edge i x.1 x.2
  if v=0 then ¬ContainsFullLine ((shapeBoard i).erase x) else
    (child v).val < i.val ∧ ∀ u ∈ (shapeBoard i).erase x,
      moveCell (flipped v) (permutation (rowPerm v)) (permutation (colPerm v)) u ∈ shapeBoard (child v)

private instance (i : Fin {n}) (x : Cell) : Decidable (edgeFacts i x) := by
  unfold edgeFacts
  infer_instance

set_option maxRecDepth 50000 in
set_option maxHeartbeats 96000000 in
private theorem certified (i : Fin {n}) : ownFacts i ∧ ∀ x ∈ shapeBoard i, edgeFacts i x := by
  fin_cases i <;> decide +kernel

theorem shape_graph_tests {{K : Type*}} [Field K] (S : Finset Cell)
    (matching : ∀ p : Perm Idx, (univ.filter (fun i ↦ p i ∈ PermanentCover.neighbors S i)).card ≤ 3)
    (minors : ∀ j, AmbientWitness K (shapePattern j) (shapeRank j)) : ShapeTest K S := by
  have all (k : ℕ) : ∀ i : Fin {n}, i.val = k → ShapeFamily K (shapeBoard i) := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro i ik
      obtain ⟨own,edges⟩ := certified i
      apply shape_family_by_deletion
      · intro _
        cases h : tag i with
        | allowed j =>
          have eq : shapeBoard i = shapeModel j := by simpa only [ownFacts,h] using own
          rw [eq]
          exact Or.inl ⟨j,SameBoard.refl⟩
        | minor j fl r c =>
          have v : (shapeBoard i).card < shapeRank j+5 ∧
              ∀ u ∈ shapePattern j, moveCell fl (permutation r) (permutation c) u ∈ shapeBoard i := by
            simpa only [ownFacts,h] using own
          exact Or.inr ⟨shapeRank j,move_ambient (minors j) _ _ _ v.2,v.1⟩
      · intro x hx
        let v := edge i x.1 x.2
        have step := edges x hx
        by_cases hz : v = 0
        · apply no_line_family
          simpa only [edgeFacts,show edge i x.1 x.2 = 0 from hz,ite_true] using step
        · have ok : (child v).val < i.val ∧ ∀ u ∈ (shapeBoard i).erase x,
              moveCell (flipped v) (permutation (rowPerm v)) (permutation (colPerm v)) u ∈ shapeBoard (child v) := by
            simpa only [edgeFacts,show edge i x.1 x.2 ≠ 0 from hz,ite_false,v] using step
          exact move_shape_family (ih (child v).val (ok.1.trans_eq ik) (child v) rfl) _ _ _ ok.2
  have strip : shapeBoard {boards.index(canonical(STRIP)[0])} = threeRows := by decide +kernel
  have mixed : shapeBoard {boards.index(canonical(MIXED)[0])} = mixedBoard := by decide +kernel
  have families := three_line_cover_property (shape_family_rule (K:=K)) S matching
    (strip ▸ all _ {boards.index(canonical(STRIP)[0])} rfl) (mixed ▸ all _ {boards.index(canonical(MIXED)[0])} rfl)
  exact families S (Finset.Subset.refl S)

#print axioms shape_graph_tests
end PermanentFive
"""
    return src
