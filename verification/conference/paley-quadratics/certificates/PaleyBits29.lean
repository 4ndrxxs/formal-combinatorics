import Quantum.Hadamard.ConferenceBitCompletion
open Hadamard.BitTrace Hadamard.DeterminantRatio Matrix
set_option maxHeartbeats 12000000
set_option maxRecDepth 60000
namespace PaleyBits29

def rawFull (i : ℕ) : ℕ := #[204397836, 408795672, 280720433, 24569955, 49139910, 98279820, 196559640, 393119280, 249367649, 498735298, 460599685, 384328459, 231786007, 463572014, 390273117, 243675323, 487350646, 437830381, 338789851, 140708791, 281417582, 25964253, 51928506, 103857012, 207714024, 415428048, 293985185, 51099459, 102198918, 0][i]!
def fullRows (i : Fin 30) : ℕ := rawFull i.val

private theorem fullSymmetric : (wordMatrix fullRows).IsSymm := by
  have h : ∀ i j : Fin 30, sign (fullRows i) j.val=sign (fullRows j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem fullDiagonal : ∀ i : Fin 30, sign (fullRows i) i.val=1 := by decide +kernel
private theorem lower0 : (lowerRow 30 rawFull) 0=true := by decide +kernel
private theorem lower1 : (lowerRow 30 rawFull) 1=true := by decide +kernel
private theorem lower2 : (lowerRow 30 rawFull) 2=true := by decide +kernel
private theorem lower3 : (lowerRow 30 rawFull) 3=true := by decide +kernel
private theorem lower4 : (lowerRow 30 rawFull) 4=true := by decide +kernel
private theorem lower5 : (lowerRow 30 rawFull) 5=true := by decide +kernel
private theorem lower6 : (lowerRow 30 rawFull) 6=true := by decide +kernel
private theorem lower7 : (lowerRow 30 rawFull) 7=true := by decide +kernel
private theorem lower8 : (lowerRow 30 rawFull) 8=true := by decide +kernel
private theorem lower9 : (lowerRow 30 rawFull) 9=true := by decide +kernel
private theorem lower10 : (lowerRow 30 rawFull) 10=true := by decide +kernel
private theorem lower11 : (lowerRow 30 rawFull) 11=true := by decide +kernel
private theorem lower12 : (lowerRow 30 rawFull) 12=true := by decide +kernel
private theorem lower13 : (lowerRow 30 rawFull) 13=true := by decide +kernel
private theorem lower14 : (lowerRow 30 rawFull) 14=true := by decide +kernel
private theorem lower15 : (lowerRow 30 rawFull) 15=true := by decide +kernel
private theorem lower16 : (lowerRow 30 rawFull) 16=true := by decide +kernel
private theorem lower17 : (lowerRow 30 rawFull) 17=true := by decide +kernel
private theorem lower18 : (lowerRow 30 rawFull) 18=true := by decide +kernel
private theorem lower19 : (lowerRow 30 rawFull) 19=true := by decide +kernel
private theorem lower20 : (lowerRow 30 rawFull) 20=true := by decide +kernel
private theorem lower21 : (lowerRow 30 rawFull) 21=true := by decide +kernel
private theorem lower22 : (lowerRow 30 rawFull) 22=true := by decide +kernel
private theorem lower23 : (lowerRow 30 rawFull) 23=true := by decide +kernel
private theorem lower24 : (lowerRow 30 rawFull) 24=true := by decide +kernel
private theorem lower25 : (lowerRow 30 rawFull) 25=true := by decide +kernel
private theorem lower26 : (lowerRow 30 rawFull) 26=true := by decide +kernel
private theorem lower27 : (lowerRow 30 rawFull) 27=true := by decide +kernel
private theorem lower28 : (lowerRow 30 rawFull) 28=true := by decide +kernel
private theorem lower29 : (lowerRow 30 rawFull) 29=true := by decide +kernel
private theorem lowerChecked : allBelow 30 (lowerRow 30 rawFull)=true := by
  have h : allBelow 0 (lowerRow 30 rawFull)=true := rfl
  have h := allBelow_step h lower0
  have h := allBelow_step h lower1
  have h := allBelow_step h lower2
  have h := allBelow_step h lower3
  have h := allBelow_step h lower4
  have h := allBelow_step h lower5
  have h := allBelow_step h lower6
  have h := allBelow_step h lower7
  have h := allBelow_step h lower8
  have h := allBelow_step h lower9
  have h := allBelow_step h lower10
  have h := allBelow_step h lower11
  have h := allBelow_step h lower12
  have h := allBelow_step h lower13
  have h := allBelow_step h lower14
  have h := allBelow_step h lower15
  have h := allBelow_step h lower16
  have h := allBelow_step h lower17
  have h := allBelow_step h lower18
  have h := allBelow_step h lower19
  have h := allBelow_step h lower20
  have h := allBelow_step h lower21
  have h := allBelow_step h lower22
  have h := allBelow_step h lower23
  have h := allBelow_step h lower24
  have h := allBelow_step h lower25
  have h := allBelow_step h lower26
  have h := allBelow_step h lower27
  have h := allBelow_step h lower28
  have h := allBelow_step h lower29
  exact h

private theorem fullPairs : ∀ i j : Fin 30, i≠j →
    correlation 30 (fullRows i) (fullRows j)=2*sign (fullRows i) j.val :=
  correlations_of_lower rawFull fullSymmetric lowerChecked


namespace SplitSquares
def rawWords (i : ℕ) : ℕ := #[0, 18372, 11570, 8096, 15172, 29772, 23090, 30986, 20638, 19546, 12846, 8924, 1528, 19636, 9186][i]!
def words (i : Fin 15) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[29, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 15 rawWords i=rowTotals i)

private theorem row0 : rowAgrees 0=true := by decide +kernel
private theorem row1 : rowAgrees 1=true := by decide +kernel
private theorem row2 : rowAgrees 2=true := by decide +kernel
private theorem row3 : rowAgrees 3=true := by decide +kernel
private theorem row4 : rowAgrees 4=true := by decide +kernel
private theorem row5 : rowAgrees 5=true := by decide +kernel
private theorem row6 : rowAgrees 6=true := by decide +kernel
private theorem row7 : rowAgrees 7=true := by decide +kernel
private theorem row8 : rowAgrees 8=true := by decide +kernel
private theorem row9 : rowAgrees 9=true := by decide +kernel
private theorem row10 : rowAgrees 10=true := by decide +kernel
private theorem row11 : rowAgrees 11=true := by decide +kernel
private theorem row12 : rowAgrees 12=true := by decide +kernel
private theorem row13 : rowAgrees 13=true := by decide +kernel
private theorem row14 : rowAgrees 14=true := by decide +kernel
private theorem rowChecked : allBelow 15 rowAgrees=true := by
  have h : allBelow 0 rowAgrees=true := rfl
  have h := allBelow_step h row0
  have h := allBelow_step h row1
  have h := allBelow_step h row2
  have h := allBelow_step h row3
  have h := allBelow_step h row4
  have h := allBelow_step h row5
  have h := allBelow_step h row6
  have h := allBelow_step h row7
  have h := allBelow_step h row8
  have h := allBelow_step h row9
  have h := allBelow_step h row10
  have h := allBelow_step h row11
  have h := allBelow_step h row12
  have h := allBelow_step h row13
  have h := allBelow_step h row14
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 15, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 15, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(126:ℤ) := by
  change cubicInteger (fun i : Fin 15 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(126:ℤ) ∧
    87*(15:ℤ)^3+375*15*(4*15-3)+1000*((wordMatrix words-1)^3).trace-
      1110*29*(15-1)=(289590:ℤ) ∧ 0≤(289590:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 15 ⊕ Fin 15 → Fin 30
  | .inl i => Fin.ofNat 30 (#[0, 1, 4, 5, 6, 7, 9, 13, 16, 20, 22, 23, 24, 25, 28][i.val]!)
  | .inr i => Fin.ofNat 30 (#[2, 3, 8, 10, 11, 12, 14, 15, 17, 18, 19, 21, 26, 27, 29][i.val]!)

def pointPosition (i : Fin 30) : Fin 15 ⊕ Fin 15 :=
  let j : ℕ := #[0, 1, 15, 16, 2, 3, 4, 5, 17, 6, 18, 19, 20, 7, 21, 22, 8, 23, 24, 25, 9, 26, 10, 11, 12, 13, 27, 28, 14, 29][i.val]!
  if j<15 then .inl (Fin.ofNat 15 j) else .inr (Fin.ofNat 15 (j-15))

def indexing : (Fin 15 ⊕ Fin 15) ≃ Fin 30 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 15,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*29)*(29-1)^14) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 14 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 14 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 14=(2*29)*(29-1)^14 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquares


namespace SplitNonsquares
def rawWords (i : ℕ) : ℕ := #[32766, 6865, 6049, 27697, 21579, 14477, 24979, 8807, 26181, 18823, 12573, 21035, 3127, 1513, 2905][i]!
def words (i : Fin 15) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[57, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 15 rawWords i=rowTotals i)

private theorem row0 : rowAgrees 0=true := by decide +kernel
private theorem row1 : rowAgrees 1=true := by decide +kernel
private theorem row2 : rowAgrees 2=true := by decide +kernel
private theorem row3 : rowAgrees 3=true := by decide +kernel
private theorem row4 : rowAgrees 4=true := by decide +kernel
private theorem row5 : rowAgrees 5=true := by decide +kernel
private theorem row6 : rowAgrees 6=true := by decide +kernel
private theorem row7 : rowAgrees 7=true := by decide +kernel
private theorem row8 : rowAgrees 8=true := by decide +kernel
private theorem row9 : rowAgrees 9=true := by decide +kernel
private theorem row10 : rowAgrees 10=true := by decide +kernel
private theorem row11 : rowAgrees 11=true := by decide +kernel
private theorem row12 : rowAgrees 12=true := by decide +kernel
private theorem row13 : rowAgrees 13=true := by decide +kernel
private theorem row14 : rowAgrees 14=true := by decide +kernel
private theorem rowChecked : allBelow 15 rowAgrees=true := by
  have h : allBelow 0 rowAgrees=true := rfl
  have h := allBelow_step h row0
  have h := allBelow_step h row1
  have h := allBelow_step h row2
  have h := allBelow_step h row3
  have h := allBelow_step h row4
  have h := allBelow_step h row5
  have h := allBelow_step h row6
  have h := allBelow_step h row7
  have h := allBelow_step h row8
  have h := allBelow_step h row9
  have h := allBelow_step h row10
  have h := allBelow_step h row11
  have h := allBelow_step h row12
  have h := allBelow_step h row13
  have h := allBelow_step h row14
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 15, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 15, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-126:ℤ) := by
  change cubicInteger (fun i : Fin 15 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-126:ℤ) ∧
    87*(15:ℤ)^3+375*15*(4*15-3)+1000*((wordMatrix words-1)^3).trace-
      1110*29*(15-1)=(37590:ℤ) ∧ 0≤(37590:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 15 ⊕ Fin 15 → Fin 30
  | .inl i => Fin.ofNat 30 (#[0, 2, 3, 8, 10, 11, 12, 14, 15, 17, 18, 19, 21, 26, 27][i.val]!)
  | .inr i => Fin.ofNat 30 (#[1, 4, 5, 6, 7, 9, 13, 16, 20, 22, 23, 24, 25, 28, 29][i.val]!)

def pointPosition (i : Fin 30) : Fin 15 ⊕ Fin 15 :=
  let j : ℕ := #[0, 15, 1, 2, 16, 17, 18, 19, 3, 20, 4, 5, 6, 21, 7, 8, 22, 9, 10, 11, 23, 12, 24, 25, 26, 27, 13, 14, 28, 29][i.val]!
  if j<15 then .inl (Fin.ofNat 15 j) else .inr (Fin.ofNat 15 (j-15))

def indexing : (Fin 15 ⊕ Fin 15) ≃ Fin 30 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 15,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*29)*(29-1)^14) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 14 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 14 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 14=(2*29)*(29-1)^14 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquares


namespace NonsplitNegative
def rawWords (i : ℕ) : ℕ := #[18402, 3493, 13962, 14132, 19912, 31371, 13329, 22583, 27675, 2093, 20831, 5042, 11500, 20844, 9649][i]!
def words (i : Fin 15) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 15 rawWords i=rowTotals i)

private theorem row0 : rowAgrees 0=true := by decide +kernel
private theorem row1 : rowAgrees 1=true := by decide +kernel
private theorem row2 : rowAgrees 2=true := by decide +kernel
private theorem row3 : rowAgrees 3=true := by decide +kernel
private theorem row4 : rowAgrees 4=true := by decide +kernel
private theorem row5 : rowAgrees 5=true := by decide +kernel
private theorem row6 : rowAgrees 6=true := by decide +kernel
private theorem row7 : rowAgrees 7=true := by decide +kernel
private theorem row8 : rowAgrees 8=true := by decide +kernel
private theorem row9 : rowAgrees 9=true := by decide +kernel
private theorem row10 : rowAgrees 10=true := by decide +kernel
private theorem row11 : rowAgrees 11=true := by decide +kernel
private theorem row12 : rowAgrees 12=true := by decide +kernel
private theorem row13 : rowAgrees 13=true := by decide +kernel
private theorem row14 : rowAgrees 14=true := by decide +kernel
private theorem rowChecked : allBelow 15 rowAgrees=true := by
  have h : allBelow 0 rowAgrees=true := rfl
  have h := allBelow_step h row0
  have h := allBelow_step h row1
  have h := allBelow_step h row2
  have h := allBelow_step h row3
  have h := allBelow_step h row4
  have h := allBelow_step h row5
  have h := allBelow_step h row6
  have h := allBelow_step h row7
  have h := allBelow_step h row8
  have h := allBelow_step h row9
  have h := allBelow_step h row10
  have h := allBelow_step h row11
  have h := allBelow_step h row12
  have h := allBelow_step h row13
  have h := allBelow_step h row14
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 15, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 15, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(150:ℤ) := by
  change cubicInteger (fun i : Fin 15 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(150:ℤ) ∧
    87*(15:ℤ)^3+375*15*(4*15-3)+1000*((wordMatrix words-1)^3).trace-
      1110*29*(15-1)=(313590:ℤ) ∧ 0≤(313590:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 15 ⊕ Fin 15 → Fin 30
  | .inl i => Fin.ofNat 30 (#[0, 2, 4, 7, 9, 10, 11, 12, 17, 18, 19, 20, 22, 25, 27][i.val]!)
  | .inr i => Fin.ofNat 30 (#[1, 3, 5, 6, 8, 13, 14, 15, 16, 21, 23, 24, 26, 28, 29][i.val]!)

def pointPosition (i : Fin 30) : Fin 15 ⊕ Fin 15 :=
  let j : ℕ := #[0, 15, 1, 16, 2, 17, 18, 3, 19, 4, 5, 6, 7, 20, 21, 22, 23, 8, 9, 10, 11, 24, 12, 25, 26, 13, 27, 14, 28, 29][i.val]!
  if j<15 then .inl (Fin.ofNat 15 j) else .inr (Fin.ofNat 15 (j-15))

def indexing : (Fin 15 ⊕ Fin 15) ≃ Fin 30 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 15,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*29)*(29-1)^14) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 14 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 14 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 14=(2*29)*(29-1)^14 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegative


namespace SplitSquaresOpposite
def rawWords (i : ℕ) : ℕ := #[3432, 3024, 13848, 10789, 7238, 12489, 4403, 13090, 9411, 6286, 10517, 1563, 756, 1452, 0][i]!
def words (i : Fin 15) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 57]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 15 rawWords i=rowTotals i)

private theorem row0 : rowAgrees 0=true := by decide +kernel
private theorem row1 : rowAgrees 1=true := by decide +kernel
private theorem row2 : rowAgrees 2=true := by decide +kernel
private theorem row3 : rowAgrees 3=true := by decide +kernel
private theorem row4 : rowAgrees 4=true := by decide +kernel
private theorem row5 : rowAgrees 5=true := by decide +kernel
private theorem row6 : rowAgrees 6=true := by decide +kernel
private theorem row7 : rowAgrees 7=true := by decide +kernel
private theorem row8 : rowAgrees 8=true := by decide +kernel
private theorem row9 : rowAgrees 9=true := by decide +kernel
private theorem row10 : rowAgrees 10=true := by decide +kernel
private theorem row11 : rowAgrees 11=true := by decide +kernel
private theorem row12 : rowAgrees 12=true := by decide +kernel
private theorem row13 : rowAgrees 13=true := by decide +kernel
private theorem row14 : rowAgrees 14=true := by decide +kernel
private theorem rowChecked : allBelow 15 rowAgrees=true := by
  have h : allBelow 0 rowAgrees=true := rfl
  have h := allBelow_step h row0
  have h := allBelow_step h row1
  have h := allBelow_step h row2
  have h := allBelow_step h row3
  have h := allBelow_step h row4
  have h := allBelow_step h row5
  have h := allBelow_step h row6
  have h := allBelow_step h row7
  have h := allBelow_step h row8
  have h := allBelow_step h row9
  have h := allBelow_step h row10
  have h := allBelow_step h row11
  have h := allBelow_step h row12
  have h := allBelow_step h row13
  have h := allBelow_step h row14
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 15, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 15, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-126:ℤ) := by
  change cubicInteger (fun i : Fin 15 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-126:ℤ) ∧
    87*(15:ℤ)^3+375*15*(4*15-3)+1000*((wordMatrix words-1)^3).trace-
      1110*29*(15-1)=(37590:ℤ) ∧ 0≤(37590:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 15 ⊕ Fin 15 → Fin 30
  | .inl i => Fin.ofNat 30 (#[2, 3, 8, 10, 11, 12, 14, 15, 17, 18, 19, 21, 26, 27, 29][i.val]!)
  | .inr i => Fin.ofNat 30 (#[0, 1, 4, 5, 6, 7, 9, 13, 16, 20, 22, 23, 24, 25, 28][i.val]!)

def pointPosition (i : Fin 30) : Fin 15 ⊕ Fin 15 :=
  let j : ℕ := #[15, 16, 0, 1, 17, 18, 19, 20, 2, 21, 3, 4, 5, 22, 6, 7, 23, 8, 9, 10, 24, 11, 25, 26, 27, 28, 12, 13, 29, 14][i.val]!
  if j<15 then .inl (Fin.ofNat 15 j) else .inr (Fin.ofNat 15 (j-15))

def indexing : (Fin 15 ⊕ Fin 15) ≃ Fin 30 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 15,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*29)*(29-1)^14) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 14 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 14 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 14=(2*29)*(29-1)^14 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquaresOpposite


namespace SplitNonsquaresOpposite
def rawWords (i : ℕ) : ℕ := #[9186, 5785, 4048, 7586, 14886, 11545, 15493, 10319, 9773, 6423, 4462, 764, 9818, 4593, 0][i]!
def words (i : Fin 15) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 29]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 15 rawWords i=rowTotals i)

private theorem row0 : rowAgrees 0=true := by decide +kernel
private theorem row1 : rowAgrees 1=true := by decide +kernel
private theorem row2 : rowAgrees 2=true := by decide +kernel
private theorem row3 : rowAgrees 3=true := by decide +kernel
private theorem row4 : rowAgrees 4=true := by decide +kernel
private theorem row5 : rowAgrees 5=true := by decide +kernel
private theorem row6 : rowAgrees 6=true := by decide +kernel
private theorem row7 : rowAgrees 7=true := by decide +kernel
private theorem row8 : rowAgrees 8=true := by decide +kernel
private theorem row9 : rowAgrees 9=true := by decide +kernel
private theorem row10 : rowAgrees 10=true := by decide +kernel
private theorem row11 : rowAgrees 11=true := by decide +kernel
private theorem row12 : rowAgrees 12=true := by decide +kernel
private theorem row13 : rowAgrees 13=true := by decide +kernel
private theorem row14 : rowAgrees 14=true := by decide +kernel
private theorem rowChecked : allBelow 15 rowAgrees=true := by
  have h : allBelow 0 rowAgrees=true := rfl
  have h := allBelow_step h row0
  have h := allBelow_step h row1
  have h := allBelow_step h row2
  have h := allBelow_step h row3
  have h := allBelow_step h row4
  have h := allBelow_step h row5
  have h := allBelow_step h row6
  have h := allBelow_step h row7
  have h := allBelow_step h row8
  have h := allBelow_step h row9
  have h := allBelow_step h row10
  have h := allBelow_step h row11
  have h := allBelow_step h row12
  have h := allBelow_step h row13
  have h := allBelow_step h row14
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 15, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 15, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(126:ℤ) := by
  change cubicInteger (fun i : Fin 15 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(126:ℤ) ∧
    87*(15:ℤ)^3+375*15*(4*15-3)+1000*((wordMatrix words-1)^3).trace-
      1110*29*(15-1)=(289590:ℤ) ∧ 0≤(289590:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 15 ⊕ Fin 15 → Fin 30
  | .inl i => Fin.ofNat 30 (#[1, 4, 5, 6, 7, 9, 13, 16, 20, 22, 23, 24, 25, 28, 29][i.val]!)
  | .inr i => Fin.ofNat 30 (#[0, 2, 3, 8, 10, 11, 12, 14, 15, 17, 18, 19, 21, 26, 27][i.val]!)

def pointPosition (i : Fin 30) : Fin 15 ⊕ Fin 15 :=
  let j : ℕ := #[15, 0, 16, 17, 1, 2, 3, 4, 18, 5, 19, 20, 21, 6, 22, 23, 7, 24, 25, 26, 8, 27, 9, 10, 11, 12, 28, 29, 13, 14][i.val]!
  if j<15 then .inl (Fin.ofNat 15 j) else .inr (Fin.ofNat 15 (j-15))

def indexing : (Fin 15 ⊕ Fin 15) ≃ Fin 30 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 15,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*29)*(29-1)^14) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 14 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 14 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 14=(2*29)*(29-1)^14 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquaresOpposite


namespace NonsplitNegativeOpposite
def rawWords (i : ℕ) : ℕ := #[8610, 2797, 7602, 3922, 5388, 12167, 14602, 5159, 14461, 3114, 4796, 4974, 11732, 4449, 0][i]!
def words (i : Fin 15) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 15 rawWords i=rowTotals i)

private theorem row0 : rowAgrees 0=true := by decide +kernel
private theorem row1 : rowAgrees 1=true := by decide +kernel
private theorem row2 : rowAgrees 2=true := by decide +kernel
private theorem row3 : rowAgrees 3=true := by decide +kernel
private theorem row4 : rowAgrees 4=true := by decide +kernel
private theorem row5 : rowAgrees 5=true := by decide +kernel
private theorem row6 : rowAgrees 6=true := by decide +kernel
private theorem row7 : rowAgrees 7=true := by decide +kernel
private theorem row8 : rowAgrees 8=true := by decide +kernel
private theorem row9 : rowAgrees 9=true := by decide +kernel
private theorem row10 : rowAgrees 10=true := by decide +kernel
private theorem row11 : rowAgrees 11=true := by decide +kernel
private theorem row12 : rowAgrees 12=true := by decide +kernel
private theorem row13 : rowAgrees 13=true := by decide +kernel
private theorem row14 : rowAgrees 14=true := by decide +kernel
private theorem rowChecked : allBelow 15 rowAgrees=true := by
  have h : allBelow 0 rowAgrees=true := rfl
  have h := allBelow_step h row0
  have h := allBelow_step h row1
  have h := allBelow_step h row2
  have h := allBelow_step h row3
  have h := allBelow_step h row4
  have h := allBelow_step h row5
  have h := allBelow_step h row6
  have h := allBelow_step h row7
  have h := allBelow_step h row8
  have h := allBelow_step h row9
  have h := allBelow_step h row10
  have h := allBelow_step h row11
  have h := allBelow_step h row12
  have h := allBelow_step h row13
  have h := allBelow_step h row14
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 15, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 15, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-150:ℤ) := by
  change cubicInteger (fun i : Fin 15 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-150:ℤ) ∧
    87*(15:ℤ)^3+375*15*(4*15-3)+1000*((wordMatrix words-1)^3).trace-
      1110*29*(15-1)=(13590:ℤ) ∧ 0≤(13590:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 15 ⊕ Fin 15 → Fin 30
  | .inl i => Fin.ofNat 30 (#[1, 3, 5, 6, 8, 13, 14, 15, 16, 21, 23, 24, 26, 28, 29][i.val]!)
  | .inr i => Fin.ofNat 30 (#[0, 2, 4, 7, 9, 10, 11, 12, 17, 18, 19, 20, 22, 25, 27][i.val]!)

def pointPosition (i : Fin 30) : Fin 15 ⊕ Fin 15 :=
  let j : ℕ := #[15, 0, 16, 1, 17, 2, 3, 18, 4, 19, 20, 21, 22, 5, 6, 7, 8, 23, 24, 25, 26, 9, 27, 10, 11, 28, 12, 29, 13, 14][i.val]!
  if j<15 then .inl (Fin.ofNat 15 j) else .inr (Fin.ofNat 15 (j-15))

def indexing : (Fin 15 ⊕ Fin 15) ≃ Fin 30 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 15,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*29)*(29-1)^14) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 14 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 14 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 14=(2*29)*(29-1)^14 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegativeOpposite

end PaleyBits29
