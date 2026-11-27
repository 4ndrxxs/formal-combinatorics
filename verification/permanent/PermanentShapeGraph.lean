import PermanentShapeFamily

/-! Exhaust all full-line subboards of the two three-line covers.
A zero edge denotes a deletion with no complete line. Each positive edge
encodes its smaller target and the row/column relabelling. -/

open Equiv Finset
namespace PermanentFive
private def permutation : Fin 33 → Perm Idx :=
  ![Equiv.refl Idx, (Equiv.swap 0 1), (Equiv.swap 1 2), ((((Equiv.swap 0 2).trans (Equiv.swap 1 3)).trans (Equiv.swap 0 4)).trans (Equiv.swap 1 0)), ((Equiv.swap 0 2).trans (Equiv.swap 1 0)), (((Equiv.swap 0 2).trans (Equiv.swap 1 3)).trans (Equiv.swap 0 4)), ((Equiv.swap 1 3).trans (Equiv.swap 2 4)), ((Equiv.swap 1 3).trans (Equiv.swap 2 1)), (Equiv.swap 2 3), (((Equiv.swap 0 3).trans (Equiv.swap 1 0)).trans (Equiv.swap 2 1)), ((((Equiv.swap 0 1).trans (Equiv.swap 0 3)).trans (Equiv.swap 2 4)).trans (Equiv.swap 0 2)), ((Equiv.swap 2 4).trans (Equiv.swap 3 2)), (((Equiv.swap 1 2).trans (Equiv.swap 1 4)).trans (Equiv.swap 3 1)), (((Equiv.swap 0 3).trans (Equiv.swap 1 2)).trans (Equiv.swap 1 0)), ((Equiv.swap 0 2).trans (Equiv.swap 1 3)), (Equiv.swap 0 2), ((Equiv.swap 0 1).trans (Equiv.swap 0 2)), (((Equiv.swap 1 4).trans (Equiv.swap 2 1)).trans (Equiv.swap 3 2)), (Equiv.swap 3 4), (((Equiv.swap 1 4).trans (Equiv.swap 2 3)).trans (Equiv.swap 2 1)), ((((Equiv.swap 0 4).trans (Equiv.swap 1 0)).trans (Equiv.swap 2 1)).trans (Equiv.swap 3 2)), (((Equiv.swap 0 1).trans (Equiv.swap 0 2)).trans (Equiv.swap 0 4)), (((Equiv.swap 1 3).trans (Equiv.swap 2 4)).trans (Equiv.swap 1 2)), ((Equiv.swap 1 2).trans (Equiv.swap 1 3)), ((((Equiv.swap 0 1).trans (Equiv.swap 0 2)).trans (Equiv.swap 0 3)).trans (Equiv.swap 0 4)), ((Equiv.swap 1 2).trans (Equiv.swap 1 4)), ((Equiv.swap 0 1).trans (Equiv.swap 2 3)), ((Equiv.swap 2 3).trans (Equiv.swap 2 4)), ((Equiv.swap 1 2).trans (Equiv.swap 3 4)), (((Equiv.swap 1 2).trans (Equiv.swap 1 3)).trans (Equiv.swap 1 4)), (Equiv.swap 2 4), (((Equiv.swap 0 1).trans (Equiv.swap 2 3)).trans (Equiv.swap 2 4)), (((Equiv.swap 0 2).trans (Equiv.swap 1 0)).trans (Equiv.swap 3 4))]

private inductive Own where
  | allowed (j : Fin 12)
  | minor (j : Fin 4) (flip : Bool) (r c : Fin 33)

private def tag : Fin 58 → Own :=
  ![.allowed 0, .allowed 1, .allowed 2, .allowed 3, .minor 0 false 0 3, .allowed 4, .minor 0 false 0 5, .minor 0 false 0 6, .allowed 5, .minor 0 false 8 3, .allowed 6, .minor 0 false 0 10, .minor 0 false 0 11, .minor 0 false 0 3, .minor 0 false 0 6, .minor 0 false 0 5, .minor 0 false 0 5, .minor 0 false 0 12, .minor 0 false 0 6, .allowed 7, .minor 0 false 11 3, .minor 0 false 8 3, .allowed 8, .minor 0 false 0 21, .minor 0 false 0 0, .minor 0 false 0 22, .minor 0 false 0 11, .minor 0 false 0 10, .minor 0 false 0 8, .minor 0 false 0 11, .minor 0 false 0 3, .minor 0 false 0 5, .minor 0 false 0 5, .minor 0 false 0 6, .minor 1 false 0 24, .minor 1 false 0 25, .minor 1 false 0 0, .minor 1 false 0 21, .minor 1 false 0 0, .allowed 9, .minor 1 false 0 11, .minor 1 false 0 8, .minor 3 false 0 27, .minor 1 false 0 11, .allowed 10, .minor 1 true 24 0, .minor 1 false 0 29, .minor 1 false 0 24, .minor 1 false 0 30, .minor 1 false 0 0, .minor 1 false 0 21, .minor 1 false 0 0, .minor 2 false 0 27, .minor 3 false 0 0, .minor 2 false 0 11, .minor 2 false 0 0, .minor 2 false 0 18, .allowed 11]

private def edge : Fin 58 → Idx → Idx → ℕ :=
  ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![2180, 2179, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![2245, 0, 0, 0, 0], ![2179, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![2246, 0, 0, 0, 0], ![0, 2179, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![4361, 4359, 4357, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![8779, 6535, 0, 0, 0], ![4357, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![8717, 8715, 0, 0, 0], ![0, 0, 4357, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![6766, 0, 0, 0, 0], ![6799, 0, 0, 0, 0], ![6535, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![8944, 0, 0, 0, 0], ![8977, 0, 0, 0, 0], ![0, 6535, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![10900, 10898, 10899, 10891, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![15251, 13071, 13069, 0, 0], ![10891, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![15256, 15254, 15255, 0, 0], ![0, 0, 0, 10891, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![13136, 13135, 0, 0, 0], ![13070, 13069, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![15315, 13137, 0, 0, 0], ![15247, 0, 13069, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![19834, 17425, 0, 0, 0], ![13333, 0, 0, 0, 0], ![13069, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![19868, 19603, 0, 0, 0], ![13334, 0, 0, 0, 0], ![0, 13069, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![15326, 15327, 0, 0, 0], ![0, 0, 15255, 15247, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![19849, 19850, 0, 0, 0], ![0, 0, 15511, 0, 0], ![0, 0, 15247, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 19075, 18877, 19108, 18514], ![17986, 0, 0, 0, 0], ![17788, 0, 0, 0, 0], ![18019, 0, 0, 0, 0], ![17425, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![20164, 0, 0, 0, 0], ![19966, 0, 0, 0, 0], ![20197, 0, 0, 0, 0], ![0, 17425, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![20231, 0, 0, 0, 0], ![19802, 0, 0, 0, 0], ![0, 20197, 0, 0, 0], ![0, 19603, 0, 0, 0]],
    ![![21834, 21831, 21825, 21832, 21814], ![21801, 21798, 21792, 21799, 21781], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![26146, 23966, 23967, 23959, 0], ![21781, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![26157, 26154, 26148, 26155, 0], ![0, 0, 0, 0, 21781], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![30560, 30559, 28315, 0, 0], ![23960, 23959, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![37116, 30500, 30501, 0, 0], ![26137, 0, 0, 23959, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![39209, 32673, 32671, 0, 0], ![24223, 0, 0, 0, 0], ![23959, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![37047, 37044, 37038, 0, 0], ![0, 0, 0, 26155, 26137], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![39214, 39212, 39213, 0, 0], ![0, 0, 0, 26401, 0], ![0, 0, 0, 26137, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![35080, 32737, 0, 0, 0], ![35113, 32671, 0, 0, 0], ![28315, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 45211, 34123, 34354, 33760], ![44122, 41383, 0, 0, 0], ![33034, 0, 0, 0, 0], ![33265, 0, 0, 0, 0], ![32671, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![45970, 43561, 0, 0, 0], ![35212, 0, 0, 0, 0], ![35443, 0, 0, 0, 0], ![0, 32671, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![44137, 44138, 0, 0, 0], ![0, 0, 39568, 0, 0], ![0, 0, 39799, 0, 0], ![0, 0, 39205, 0, 0]],
    ![![52326, 50145, 50139, 50146, 50128], ![52293, 50112, 50106, 50113, 50095], ![47917, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![56638, 56636, 54459, 54451, 0], ![50096, 50095, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![60994, 56646, 56640, 56647, 0], ![52273, 0, 0, 0, 50095], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![63172, 58814, 58815, 58807, 0], ![50359, 0, 0, 0, 0], ![50095, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![63183, 63180, 63174, 63181, 0], ![0, 0, 0, 0, 52537], ![0, 0, 0, 0, 52273], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![54521, 54519, 54517, 0, 0], ![54455, 54453, 54451, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![56721, 56703, 54525, 0, 0], ![56630, 56629, 0, 54451, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![61057, 56714, 56701, 0, 0], ![60985, 0, 0, 56647, 56629], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 71347, 71149, 67024, 66430], ![71879, 67521, 67519, 0, 0], ![59170, 0, 0, 0, 0], ![59401, 0, 0, 0, 0], ![58807, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![71884, 71882, 71883, 0, 0], ![0, 0, 0, 63526, 0], ![0, 0, 0, 63757, 0], ![0, 0, 0, 63163, 0]],
    ![![0, 0, 0, 0, 0], ![65573, 65572, 0, 0, 0], ![65606, 65605, 0, 0, 0], ![65342, 65341, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![70622, 69763, 0, 0, 0], ![70292, 69697, 0, 0, 0], ![65936, 0, 0, 0, 0], ![0, 65341, 0, 0, 0]],
    ![![78462, 78459, 76275, 76282, 76264], ![78429, 78426, 76242, 76249, 76231], ![74054, 74053, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![82818, 80637, 80631, 80638, 80620], ![82785, 80604, 80598, 80605, 80587], ![74317, 0, 0, 0, 0], ![74053, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![87191, 87189, 87187, 84943, 0], ![76235, 76233, 76231, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![89396, 89392, 87132, 87139, 0], ![78410, 78409, 0, 0, 76231], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 99661, 99463, 99694, 96922], ![93664, 91484, 91485, 91477, 0], ![80950, 0, 0, 0, 0], ![81181, 0, 0, 0, 0], ![80587, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![93675, 93672, 93666, 93673, 0], ![0, 0, 0, 0, 83128], ![0, 0, 0, 0, 83359], ![0, 0, 0, 0, 82765]],
    ![![106776, 106773, 106767, 104596, 104578], ![106743, 106740, 106734, 104563, 104545], ![100193, 100191, 100189, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![111132, 108951, 108945, 108952, 108934], ![111099, 108918, 108912, 108919, 108901], ![102730, 0, 0, 0, 0], ![102961, 0, 0, 0, 0], ![102367, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![104620, 104618, 104619, 104611, 0], ![104554, 104552, 104553, 104545, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![106821, 106817, 106807, 104629, 0], ![106727, 106725, 106723, 0, 104545], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![119932, 119930, 119931, 119923, 117646], ![119866, 119864, 119865, 119857, 117613], ![113266, 113264, 113265, 113257, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]],
    ![![122121, 122118, 122112, 122119, 122101], ![122055, 122052, 122046, 122053, 122035], ![121989, 121986, 121980, 121987, 121969], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]

private def child (v : ℕ) : Fin 58 := ⟨(v-1)/2178%58,Nat.mod_lt _ (by decide)⟩
private def flipped (v : ℕ) : Bool := (v-1)/1089%2 == 1
private def rowPerm (v : ℕ) : Fin 33 := ⟨(v-1)/33%33,Nat.mod_lt _ (by decide)⟩
private def colPerm (v : ℕ) : Fin 33 := ⟨(v-1)%33,Nat.mod_lt _ (by decide)⟩

private def ownFacts (i : Fin 58) : Prop :=
  match tag i with
  | .allowed j => shapeBoard i = shapeModel j
  | .minor j fl r c => (shapeBoard i).card < shapeRank j+5 ∧
      ∀ u ∈ shapePattern j, moveCell fl (permutation r) (permutation c) u ∈ shapeBoard i

private instance (i : Fin 58) : Decidable (ownFacts i) := by
  unfold ownFacts
  cases tag i <;> infer_instance

private instance (S : Finset Cell) : Decidable (ContainsFullLine S) := by
  unfold ContainsFullLine
  infer_instance

private def edgeFacts (i : Fin 58) (x : Cell) : Prop :=
  let v := edge i x.1 x.2
  if v=0 then ¬ContainsFullLine ((shapeBoard i).erase x) else
    (child v).val < i.val ∧ ∀ u ∈ (shapeBoard i).erase x,
      moveCell (flipped v) (permutation (rowPerm v)) (permutation (colPerm v)) u ∈ shapeBoard (child v)

private instance (i : Fin 58) (x : Cell) : Decidable (edgeFacts i x) := by
  unfold edgeFacts
  infer_instance

set_option maxRecDepth 50000 in
set_option maxHeartbeats 96000000 in
private theorem certified (i : Fin 58) : ownFacts i ∧ ∀ x ∈ shapeBoard i, edgeFacts i x := by
  fin_cases i <;> decide +kernel

theorem shape_graph_tests {K : Type*} [Field K] (S : Finset Cell)
    (matching : ∀ p : Perm Idx, (univ.filter (fun i ↦ p i ∈ PermanentCover.neighbors S i)).card ≤ 3)
    (minors : ∀ j, AmbientWitness K (shapePattern j) (shapeRank j)) : ShapeTest K S := by
  have all (k : ℕ) : ∀ i : Fin 58, i.val = k → ShapeFamily K (shapeBoard i) := by
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
  have strip : shapeBoard 57 = threeRows := by decide +kernel
  have mixed : shapeBoard 53 = mixedBoard := by decide +kernel
  have families := three_line_cover_property (shape_family_rule (K:=K)) S matching
    (strip ▸ all _ 57 rfl) (mixed ▸ all _ 53 rfl)
  exact families S (Finset.Subset.refl S)

#print axioms shape_graph_tests
end PermanentFive
