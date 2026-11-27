"""Emit the small Lean proof table for the deletion graph."""
from check_quintic_discriminant import support_text
from check_quintic_layout import permutation_term
from check_quintic_restricted import vector


def deletion_source(nodes, boards, ten, ambient, find_embedding, strip, mixed):
    templates = (frozenset(5*r+c for r in range(3) for c in range(4)),
                 frozenset((0,1,2,3,5,6,7,8,10,11,12,14)))
    permutations=[]
    def index(p):
        if p not in permutations:
            permutations.append(p)
        return permutations.index(p)

    tags=[]
    tables=[]
    for board in boards:
        kind,line,children=nodes[board]
        data=[]
        if kind=="witt":
            i,(flip,r,c)=find_embedding(board,templates)
            tags.append(f".witt {i} {str(bool(flip)).lower()} {index(r)} {index(c)}")
        elif kind=="ten":
            tags.append(f".ten {ten.index(board)}")
        elif kind=="ambient":
            tags.append(f".ambient {ambient.index(board)}")
        else:
            tags.append(f".line {str(line>=5).lower()} {line%5}")
        for x in range(25):
            if x not in children:
                data.append("(0,false,0,0)")
            else:
                child,(flip,r,c)=children[x]
                assert boards.index(child)<boards.index(board)
                data.append(f"({boards.index(child)},{str(bool(flip)).lower()},{index(r)},{index(c)})")
        if children:
            tables.append(vector(vector(data[k:k+5]) for k in range(0,25,5)))
        else:
            tables.append("(fun _ _ ↦ (0,false,0,0))")

    board_ct=len(boards)
    perm_ct=len(permutations)
    src="""import PermanentLineFamily
import PermanentLineBoards

/-! A finite deletion graph covers every three-line support. Each edge records
a concrete coordinate relabelling into its smaller successor. -/

open Equiv Finset
namespace PermanentFive
"""
    src+="def lineWitt : Fin 2 → Finset Cell :=\n  "+vector(support_text(sorted(t)) for t in templates)+"\n\n"
    src+=f"private def movement : Fin {perm_ct} → Perm Idx :=\n  "+vector(permutation_term(p) for p in permutations)+"\n\n"
    src+=f"""private inductive Kind where
  | witt (target : Fin 2) (flip : Bool) (r c : Fin {perm_ct})
  | ten (target : Fin {len(ten)})
  | ambient (target : Fin {len(ambient)})
  | line (axis : Bool) (i : Idx)

private def kind : Fin {board_ct} → Kind :=
  ![{", ".join(tags)}]

private abbrev Edge := Fin {board_ct} × Bool × Fin {perm_ct} × Fin {perm_ct}
private def edgeData : Fin {board_ct} → Idx → Idx → Edge :=
  !["""
    src+=",\n    ".join(tables)+"]\n\n"
    src+=f"""private def edgeFacts (i : Fin {board_ct}) (x : Cell) : Prop :=
  let d := edgeData i x.1 x.2
  d.1.val < i.val ∧ ∀ u ∈ (lineBoard i).erase x,
    moveCell d.2.1 (movement d.2.2.1) (movement d.2.2.2) u ∈ lineBoard d.1

private instance (i : Fin {board_ct}) (x : Cell) : Decidable (edgeFacts i x) := by
  unfold edgeFacts
  infer_instance

private def valid (i : Fin {board_ct}) : Prop :=
  match kind i with
  | .witt j flip r c => ∀ u ∈ lineBoard i, moveCell flip (movement r) (movement c) u ∈ lineWitt j
  | .ten j => lineBoard i = lineTen j
  | .ambient j => lineBoard i = lineAmbient j ∧ (lineBoard i).card ≤ 12 ∧
      ∀ x ∈ lineBoard i, edgeFacts i x
  | .line axis j => ∀ k, edgeFacts i (linePoint axis j k)

private instance (i : Fin {board_ct}) : Decidable (valid i) := by
  unfold valid
  cases kind i <;> infer_instance

set_option maxRecDepth 36000 in
set_option maxHeartbeats 48000000 in
private theorem verified (i : Fin {board_ct}) : valid i := by
  fin_cases i <;> decide +kernel

theorem line_graph_tests {{K : Type*}} [Field K] (S : Finset Cell)
    (matching : ∀ p : Perm Idx, (univ.filter (fun i ↦ p i ∈ PermanentCover.neighbors S i)).card ≤ 3)
    (witt : ∀ i, HasIndexFourBlock K (lineWitt i)) (ten : ∀ i, HasSimpleZeroBlock K 10 (lineTen i))
    (ambient : ∀ i, HasAmbientEight K (lineAmbient i)) : LineTest K S := by
  have all (k : ℕ) : ∀ i : Fin {board_ct}, i.val = k → LineTestFamily K (lineBoard i) := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro i eq
      have step (x : Cell) (h : edgeFacts i x) : LineTestFamily K ((lineBoard i).erase x) := by
        let d := edgeData i x.1 x.2
        exact move_family (ih d.1.val (h.1.trans_eq eq) d.1 rfl) _ _ _ h.2
      have v := verified i
      cases h : kind i with
      | witt j flip r c =>
        exact move_family (family_of_witt (witt j)) flip (movement r) (movement c) (by simpa only [valid,h] using v)
      | ten j =>
        have same : lineBoard i = lineTen j := by simpa only [valid,h] using v
        rw [same]
        exact family_of_ten (ten j)
      | ambient j =>
        have b : lineBoard i = lineAmbient j ∧ (lineBoard i).card ≤ 12 ∧
            ∀ x ∈ lineBoard i, edgeFacts i x := by simpa only [valid,h] using v
        exact family_by_ambient _ b.2.1 (b.1.symm ▸ ambient j) (fun x hx ↦ step x (b.2.2 x hx))
      | line axis j =>
        have bounds : ∀ k, edgeFacts i (linePoint axis j k) := by simpa only [valid,h] using v
        exact family_by_line _ axis j (fun k ↦ step _ (bounds k))
  have strip_eq : lineBoard {boards.index(strip)} = threeRows := by decide +kernel
  have mixed_eq : lineBoard {boards.index(mixed)} = mixedBoard := by decide +kernel
  have families := three_line_cover_property (line_family_rule (K:=K)) S matching
    (strip_eq ▸ all _ {boards.index(strip)} rfl) (mixed_eq ▸ all _ {boards.index(mixed)} rfl)
  exact families S (Finset.Subset.refl S)

#print axioms line_graph_tests
end PermanentFive
"""
    return src
