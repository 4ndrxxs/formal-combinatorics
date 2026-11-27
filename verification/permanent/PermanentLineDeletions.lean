import PermanentLineFamily
import PermanentLineBoards

/-! A finite deletion graph covers every three-line support. Each edge records
a concrete coordinate relabelling into its smaller successor. -/

open Equiv Finset
namespace PermanentFive
def lineWitt : Fin 2 → Finset Cell :=
  ![{(0,0), (0,1), (0,2), (0,3), (1,0), (1,1), (1,2), (1,3), (2,0), (2,1), (2,2), (2,3)}, {(0,0), (0,1), (0,2), (0,3), (1,0), (1,1), (1,2), (1,3), (2,0), (2,1), (2,2), (2,4)}]

private def movement : Fin 22 → Perm Idx :=
  ![(Equiv.swap 1 2), Equiv.refl Idx, (Equiv.swap 2 3), ((Equiv.swap 0 2).trans (Equiv.swap 1 0)), (Equiv.swap 3 4), (Equiv.swap 0 1), (((Equiv.swap 0 3).trans (Equiv.swap 1 0)).trans (Equiv.swap 2 1)), ((Equiv.swap 2 4).trans (Equiv.swap 3 2)), (((Equiv.swap 0 2).trans (Equiv.swap 1 0)).trans (Equiv.swap 3 4)), ((Equiv.swap 1 3).trans (Equiv.swap 2 1)), (((Equiv.swap 1 2).trans (Equiv.swap 1 3)).trans (Equiv.swap 1 4)), (((Equiv.swap 1 3).trans (Equiv.swap 2 1)).trans (Equiv.swap 2 4)), ((Equiv.swap 2 3).trans (Equiv.swap 2 4)), ((Equiv.swap 1 2).trans (Equiv.swap 1 3)), ((Equiv.swap 1 2).trans (Equiv.swap 3 4)), (((Equiv.swap 1 4).trans (Equiv.swap 2 1)).trans (Equiv.swap 3 2)), ((((Equiv.swap 0 4).trans (Equiv.swap 1 0)).trans (Equiv.swap 2 1)).trans (Equiv.swap 3 2)), (((Equiv.swap 0 1).trans (Equiv.swap 2 3)).trans (Equiv.swap 2 4)), (Equiv.swap 0 2), (Equiv.swap 2 4), ((Equiv.swap 0 1).trans (Equiv.swap 2 3)), ((Equiv.swap 0 1).trans (Equiv.swap 0 2))]

private inductive Kind where
  | witt (target : Fin 2) (flip : Bool) (r c : Fin 22)
  | ten (target : Fin 10)
  | ambient (target : Fin 4)
  | line (axis : Bool) (i : Idx)

private def kind : Fin 29 → Kind :=
  ![.ten 0, .ten 1, .witt 1 false 0 1, .ten 2, .ten 3, .ten 4, .witt 1 false 1 2, .ten 5, .ten 6, .witt 1 false 3 4, .ten 7, .ten 8, .ten 9, .line false 0, .line false 0, .ambient 0, .witt 1 false 0 1, .ambient 1, .ambient 2, .line false 0, .line false 0, .witt 0 false 1 1, .witt 1 false 1 1, .ambient 3, .line false 0, .line false 0, .line false 0, .line false 0, .line false 0]

private abbrev Edge := Fin 29 × Bool × Fin 22 × Fin 22
private def edgeData : Fin 29 → Idx → Idx → Edge :=
  ![(fun _ _ ↦ (0,false,0,0)),
    (fun _ _ ↦ (0,false,0,0)),
    (fun _ _ ↦ (0,false,0,0)),
    (fun _ _ ↦ (0,false,0,0)),
    (fun _ _ ↦ (0,false,0,0)),
    (fun _ _ ↦ (0,false,0,0)),
    (fun _ _ ↦ (0,false,0,0)),
    (fun _ _ ↦ (0,false,0,0)),
    (fun _ _ ↦ (0,false,0,0)),
    (fun _ _ ↦ (0,false,0,0)),
    (fun _ _ ↦ (0,false,0,0)),
    (fun _ _ ↦ (0,false,0,0)),
    (fun _ _ ↦ (0,false,0,0)),
    ![![(7,true,5,6), (7,true,1,6), (0,true,7,1), (0,true,4,1), (0,true,1,1)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)]],
    ![![(11,true,5,8), (11,true,1,3), (3,true,7,1), (3,true,4,1), (3,true,1,1)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)]],
    ![![(8,false,5,6), (8,false,5,9), (8,false,5,2), (8,false,5,1), (0,false,0,0)], ![(8,false,1,6), (8,false,1,9), (8,false,1,2), (8,false,1,1), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (1,false,7,1)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (1,false,4,1)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (1,false,1,1)]],
    (fun _ _ ↦ (0,false,0,0)),
    ![![(10,false,3,10), (9,false,5,11), (9,false,5,12), (6,false,5,4), (0,false,0,0)], ![(10,false,0,13), (9,false,1,9), (9,false,1,2), (0,false,0,0), (6,false,1,1)], ![(4,false,1,1), (0,false,0,0), (0,false,0,0), (2,false,5,4), (2,false,1,1)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)]],
    ![![(12,false,5,8), (12,false,5,14), (12,false,5,4), (8,false,5,4), (0,false,0,0)], ![(11,false,1,6), (11,false,1,9), (11,false,1,2), (0,false,0,0), (7,false,1,1)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (5,false,7,1), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (5,false,4,1), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (5,false,1,1), (0,false,0,0)]],
    ![![(18,false,5,6), (14,true,15,1), (14,true,7,1), (14,true,4,1), (13,true,1,1)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)]],
    ![![(18,false,1,16), (18,false,1,15), (18,false,1,7), (18,false,1,4), (15,false,1,1)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)]],
    (fun _ _ ↦ (0,false,0,0)),
    (fun _ _ ↦ (0,false,0,0)),
    ![![(17,false,3,17), (17,false,3,12), (16,false,18,19), (16,false,3,12), (0,false,0,0)], ![(17,false,0,20), (17,false,0,2), (16,false,21,7), (0,false,0,0), (16,false,0,2)], ![(17,false,1,5), (17,false,1,1), (0,false,0,0), (16,false,5,4), (16,false,1,1)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)]],
    ![![(20,false,5,16), (19,false,5,15), (19,false,5,7), (19,false,5,4), (19,false,5,1)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)]],
    ![![(22,false,3,6), (22,false,3,9), (22,false,3,2), (22,false,3,1), (21,false,1,1)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)]],
    ![![(23,false,3,3), (23,false,3,0), (23,false,3,1), (22,false,0,4), (22,false,1,1)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)]],
    ![![(26,false,3,6), (26,false,3,9), (26,false,3,2), (26,false,3,1), (25,false,5,1)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)]],
    ![![(27,false,3,16), (27,false,3,15), (27,false,3,7), (27,false,3,4), (27,false,3,1)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)], ![(0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0), (0,false,0,0)]]]

private def edgeFacts (i : Fin 29) (x : Cell) : Prop :=
  let d := edgeData i x.1 x.2
  d.1.val < i.val ∧ ∀ u ∈ (lineBoard i).erase x,
    moveCell d.2.1 (movement d.2.2.1) (movement d.2.2.2) u ∈ lineBoard d.1

private instance (i : Fin 29) (x : Cell) : Decidable (edgeFacts i x) := by
  unfold edgeFacts
  infer_instance

private def valid (i : Fin 29) : Prop :=
  match kind i with
  | .witt j flip r c => ∀ u ∈ lineBoard i, moveCell flip (movement r) (movement c) u ∈ lineWitt j
  | .ten j => lineBoard i = lineTen j
  | .ambient j => lineBoard i = lineAmbient j ∧ (lineBoard i).card ≤ 12 ∧
      ∀ x ∈ lineBoard i, edgeFacts i x
  | .line axis j => ∀ k, edgeFacts i (linePoint axis j k)

private instance (i : Fin 29) : Decidable (valid i) := by
  unfold valid
  cases kind i <;> infer_instance

set_option maxRecDepth 36000 in
set_option maxHeartbeats 48000000 in
private theorem verified (i : Fin 29) : valid i := by
  fin_cases i <;> decide +kernel

theorem line_graph_tests {K : Type*} [Field K] (S : Finset Cell)
    (matching : ∀ p : Perm Idx, (univ.filter (fun i ↦ p i ∈ PermanentCover.neighbors S i)).card ≤ 3)
    (witt : ∀ i, HasIndexFourBlock K (lineWitt i)) (ten : ∀ i, HasSimpleZeroBlock K 10 (lineTen i))
    (ambient : ∀ i, HasAmbientEight K (lineAmbient i)) : LineTest K S := by
  have all (k : ℕ) : ∀ i : Fin 29, i.val = k → LineTestFamily K (lineBoard i) := by
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
  have strip_eq : lineBoard 28 = threeRows := by decide +kernel
  have mixed_eq : lineBoard 24 = mixedBoard := by decide +kernel
  have families := three_line_cover_property (line_family_rule (K:=K)) S matching
    (strip_eq ▸ all _ 28 rfl) (mixed_eq ▸ all _ 24 rfl)
  exact families S (Finset.Subset.refl S)

#print axioms line_graph_tests
end PermanentFive
