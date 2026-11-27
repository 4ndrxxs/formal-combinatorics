import Quantum.Hadamard.ConferenceBitCompletion
open Hadamard.BitTrace Hadamard.DeterminantRatio Matrix
set_option maxHeartbeats 12000000
set_option maxRecDepth 60000
namespace PaleyBits37

def rawFull (i : ℕ) : ℕ := #[41370444132, 82740888264, 28042823057, 56085646114, 112171292228, 86903630985, 36368308499, 72736616998, 8034280525, 16068561050, 32137122100, 64274244200, 128548488400, 119658023329, 101877093187, 66315232903, 132630465806, 127821978141, 118205002811, 98971052151, 60503150831, 121006301662, 104573649853, 71708346235, 5977738999, 11955477998, 23910955996, 47821911992, 95643823984, 53848694497, 107697388994, 77955824517, 18472695563, 36945391126, 73890782252, 10342611033, 20685222066, 0][i]!
def fullRows (i : Fin 38) : ℕ := rawFull i.val

private theorem fullSymmetric : (wordMatrix fullRows).IsSymm := by
  have h : ∀ i j : Fin 38, sign (fullRows i) j.val=sign (fullRows j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem fullDiagonal : ∀ i : Fin 38, sign (fullRows i) i.val=1 := by decide +kernel
private theorem lower0 : (lowerRow 38 rawFull) 0=true := by decide +kernel
private theorem lower1 : (lowerRow 38 rawFull) 1=true := by decide +kernel
private theorem lower2 : (lowerRow 38 rawFull) 2=true := by decide +kernel
private theorem lower3 : (lowerRow 38 rawFull) 3=true := by decide +kernel
private theorem lower4 : (lowerRow 38 rawFull) 4=true := by decide +kernel
private theorem lower5 : (lowerRow 38 rawFull) 5=true := by decide +kernel
private theorem lower6 : (lowerRow 38 rawFull) 6=true := by decide +kernel
private theorem lower7 : (lowerRow 38 rawFull) 7=true := by decide +kernel
private theorem lower8 : (lowerRow 38 rawFull) 8=true := by decide +kernel
private theorem lower9 : (lowerRow 38 rawFull) 9=true := by decide +kernel
private theorem lower10 : (lowerRow 38 rawFull) 10=true := by decide +kernel
private theorem lower11 : (lowerRow 38 rawFull) 11=true := by decide +kernel
private theorem lower12 : (lowerRow 38 rawFull) 12=true := by decide +kernel
private theorem lower13 : (lowerRow 38 rawFull) 13=true := by decide +kernel
private theorem lower14 : (lowerRow 38 rawFull) 14=true := by decide +kernel
private theorem lower15 : (lowerRow 38 rawFull) 15=true := by decide +kernel
private theorem lower16 : (lowerRow 38 rawFull) 16=true := by decide +kernel
private theorem lower17 : (lowerRow 38 rawFull) 17=true := by decide +kernel
private theorem lower18 : (lowerRow 38 rawFull) 18=true := by decide +kernel
private theorem lower19 : (lowerRow 38 rawFull) 19=true := by decide +kernel
private theorem lower20 : (lowerRow 38 rawFull) 20=true := by decide +kernel
private theorem lower21 : (lowerRow 38 rawFull) 21=true := by decide +kernel
private theorem lower22 : (lowerRow 38 rawFull) 22=true := by decide +kernel
private theorem lower23 : (lowerRow 38 rawFull) 23=true := by decide +kernel
private theorem lower24 : (lowerRow 38 rawFull) 24=true := by decide +kernel
private theorem lower25 : (lowerRow 38 rawFull) 25=true := by decide +kernel
private theorem lower26 : (lowerRow 38 rawFull) 26=true := by decide +kernel
private theorem lower27 : (lowerRow 38 rawFull) 27=true := by decide +kernel
private theorem lower28 : (lowerRow 38 rawFull) 28=true := by decide +kernel
private theorem lower29 : (lowerRow 38 rawFull) 29=true := by decide +kernel
private theorem lower30 : (lowerRow 38 rawFull) 30=true := by decide +kernel
private theorem lower31 : (lowerRow 38 rawFull) 31=true := by decide +kernel
private theorem lower32 : (lowerRow 38 rawFull) 32=true := by decide +kernel
private theorem lower33 : (lowerRow 38 rawFull) 33=true := by decide +kernel
private theorem lower34 : (lowerRow 38 rawFull) 34=true := by decide +kernel
private theorem lower35 : (lowerRow 38 rawFull) 35=true := by decide +kernel
private theorem lower36 : (lowerRow 38 rawFull) 36=true := by decide +kernel
private theorem lower37 : (lowerRow 38 rawFull) 37=true := by decide +kernel
private theorem lowerChecked : allBelow 38 (lowerRow 38 rawFull)=true := by
  have h : allBelow 0 (lowerRow 38 rawFull)=true := rfl
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
  have h := allBelow_step h lower30
  have h := allBelow_step h lower31
  have h := allBelow_step h lower32
  have h := allBelow_step h lower33
  have h := allBelow_step h lower34
  have h := allBelow_step h lower35
  have h := allBelow_step h lower36
  have h := allBelow_step h lower37
  exact h

private theorem fullPairs : ∀ i j : Fin 38, i≠j →
    correlation 38 (fullRows i) (fullRows j)=2*sign (fullRows i) j.val :=
  correlations_of_lower rawFull fullSymmetric lowerChecked


namespace SplitSquares
def rawWords (i : ℕ) : ℕ := #[0, 364084, 147106, 357728, 310562, 94366, 256776, 252452, 440408, 492742, 406046, 106966, 148924, 68988, 495848, 281554, 27370, 284612, 182042][i]!
def words (i : Fin 19) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 19 rawWords i=rowTotals i)

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
private theorem row15 : rowAgrees 15=true := by decide +kernel
private theorem row16 : rowAgrees 16=true := by decide +kernel
private theorem row17 : rowAgrees 17=true := by decide +kernel
private theorem row18 : rowAgrees 18=true := by decide +kernel
private theorem rowChecked : allBelow 19 rowAgrees=true := by
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
  have h := allBelow_step h row15
  have h := allBelow_step h row16
  have h := allBelow_step h row17
  have h := allBelow_step h row18
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 19, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 19, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-342:ℤ) := by
  change cubicInteger (fun i : Fin 19 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-342:ℤ) ∧
    87*(19:ℤ)^3+375*19*(4*19-3)+1000*((wordMatrix words-1)^3).trace-
      1110*37*(19-1)=(35598:ℤ) ∧ 0≤(35598:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 19 ⊕ Fin 19 → Fin 38
  | .inl i => Fin.ofNat 38 (#[0, 1, 3, 4, 7, 9, 10, 11, 12, 16, 21, 25, 26, 27, 28, 30, 33, 34, 36][i.val]!)
  | .inr i => Fin.ofNat 38 (#[2, 5, 6, 8, 13, 14, 15, 17, 18, 19, 20, 22, 23, 24, 29, 31, 32, 35, 37][i.val]!)

def pointPosition (i : Fin 38) : Fin 19 ⊕ Fin 19 :=
  let j : ℕ := #[0, 1, 19, 2, 3, 20, 21, 4, 22, 5, 6, 7, 8, 23, 24, 25, 9, 26, 27, 28, 29, 10, 30, 31, 32, 11, 12, 13, 14, 33, 15, 34, 35, 16, 17, 36, 18, 37][i.val]!
  if j<19 then .inl (Fin.ofNat 19 j) else .inr (Fin.ofNat 19 (j-19))

def indexing : (Fin 19 ⊕ Fin 19) ≃ Fin 38 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 19,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*37)*(37-1)^18) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 18 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 18 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 18=(2*37)*(37-1)^18 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquares


namespace SplitNonsquares
def rawWords (i : ℕ) : ℕ := #[524286, 89489, 65057, 322641, 209003, 460437, 236569, 436515, 472195, 485413, 147823, 266959, 280919, 99229, 169487, 352461, 41843, 18417, 39849][i]!
def words (i : Fin 19) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 19 rawWords i=rowTotals i)

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
private theorem row15 : rowAgrees 15=true := by decide +kernel
private theorem row16 : rowAgrees 16=true := by decide +kernel
private theorem row17 : rowAgrees 17=true := by decide +kernel
private theorem row18 : rowAgrees 18=true := by decide +kernel
private theorem rowChecked : allBelow 19 rowAgrees=true := by
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
  have h := allBelow_step h row15
  have h := allBelow_step h row16
  have h := allBelow_step h row17
  have h := allBelow_step h row18
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 19, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 19, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(342:ℤ) := by
  change cubicInteger (fun i : Fin 19 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(342:ℤ) ∧
    87*(19:ℤ)^3+375*19*(4*19-3)+1000*((wordMatrix words-1)^3).trace-
      1110*37*(19-1)=(719598:ℤ) ∧ 0≤(719598:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 19 ⊕ Fin 19 → Fin 38
  | .inl i => Fin.ofNat 38 (#[0, 2, 5, 6, 8, 13, 14, 15, 17, 18, 19, 20, 22, 23, 24, 29, 31, 32, 35][i.val]!)
  | .inr i => Fin.ofNat 38 (#[1, 3, 4, 7, 9, 10, 11, 12, 16, 21, 25, 26, 27, 28, 30, 33, 34, 36, 37][i.val]!)

def pointPosition (i : Fin 38) : Fin 19 ⊕ Fin 19 :=
  let j : ℕ := #[0, 19, 1, 20, 21, 2, 3, 22, 4, 23, 24, 25, 26, 5, 6, 7, 27, 8, 9, 10, 11, 28, 12, 13, 14, 29, 30, 31, 32, 15, 33, 16, 17, 34, 35, 18, 36, 37][i.val]!
  if j<19 then .inl (Fin.ofNat 19 j) else .inr (Fin.ofNat 19 (j-19))

def indexing : (Fin 19 ⊕ Fin 19) ≃ Fin 38 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 19,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*37)*(37-1)^18) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 18 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 18 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 18=(2*37)*(37-1)^18 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquares


namespace NonsplitNegative
def rawWords (i : ℕ) : ℕ := #[329994, 146981, 453810, 55649, 256068, 252558, 441112, 356388, 517193, 396386, 287494, 74367, 147690, 101846, 464316, 139644, 27057, 316278, 149445][i]!
def words (i : Fin 19) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 19 rawWords i=rowTotals i)

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
private theorem row15 : rowAgrees 15=true := by decide +kernel
private theorem row16 : rowAgrees 16=true := by decide +kernel
private theorem row17 : rowAgrees 17=true := by decide +kernel
private theorem row18 : rowAgrees 18=true := by decide +kernel
private theorem rowChecked : allBelow 19 rowAgrees=true := by
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
  have h := allBelow_step h row15
  have h := allBelow_step h row16
  have h := allBelow_step h row17
  have h := allBelow_step h row18
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 19, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 19, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-114:ℤ) := by
  change cubicInteger (fun i : Fin 19 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-114:ℤ) ∧
    87*(19:ℤ)^3+375*19*(4*19-3)+1000*((wordMatrix words-1)^3).trace-
      1110*37*(19-1)=(263598:ℤ) ∧ 0≤(263598:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 19 ⊕ Fin 19 → Fin 38
  | .inl i => Fin.ofNat 38 (#[0, 2, 4, 5, 9, 10, 11, 12, 13, 16, 21, 24, 25, 26, 27, 28, 32, 33, 35][i.val]!)
  | .inr i => Fin.ofNat 38 (#[1, 3, 6, 7, 8, 14, 15, 17, 18, 19, 20, 22, 23, 29, 30, 31, 34, 36, 37][i.val]!)

def pointPosition (i : Fin 38) : Fin 19 ⊕ Fin 19 :=
  let j : ℕ := #[0, 19, 1, 20, 2, 3, 21, 22, 23, 4, 5, 6, 7, 8, 24, 25, 9, 26, 27, 28, 29, 10, 30, 31, 11, 12, 13, 14, 15, 32, 33, 34, 16, 17, 35, 18, 36, 37][i.val]!
  if j<19 then .inl (Fin.ofNat 19 j) else .inr (Fin.ofNat 19 (j-19))

def indexing : (Fin 19 ⊕ Fin 19) ≃ Fin 38 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 19,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*37)*(37-1)^18) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 18 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 18 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 18=(2*37)*(37-1)^18 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegative


namespace SplitSquaresOpposite
def rawWords (i : ℕ) : ℕ := #[44744, 32528, 161320, 104501, 230218, 118284, 218257, 236097, 242706, 73911, 133479, 140459, 49614, 84743, 176230, 20921, 9208, 19924, 0][i]!
def words (i : Fin 19) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 19 rawWords i=rowTotals i)

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
private theorem row15 : rowAgrees 15=true := by decide +kernel
private theorem row16 : rowAgrees 16=true := by decide +kernel
private theorem row17 : rowAgrees 17=true := by decide +kernel
private theorem row18 : rowAgrees 18=true := by decide +kernel
private theorem rowChecked : allBelow 19 rowAgrees=true := by
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
  have h := allBelow_step h row15
  have h := allBelow_step h row16
  have h := allBelow_step h row17
  have h := allBelow_step h row18
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 19, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 19, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(342:ℤ) := by
  change cubicInteger (fun i : Fin 19 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(342:ℤ) ∧
    87*(19:ℤ)^3+375*19*(4*19-3)+1000*((wordMatrix words-1)^3).trace-
      1110*37*(19-1)=(719598:ℤ) ∧ 0≤(719598:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 19 ⊕ Fin 19 → Fin 38
  | .inl i => Fin.ofNat 38 (#[2, 5, 6, 8, 13, 14, 15, 17, 18, 19, 20, 22, 23, 24, 29, 31, 32, 35, 37][i.val]!)
  | .inr i => Fin.ofNat 38 (#[0, 1, 3, 4, 7, 9, 10, 11, 12, 16, 21, 25, 26, 27, 28, 30, 33, 34, 36][i.val]!)

def pointPosition (i : Fin 38) : Fin 19 ⊕ Fin 19 :=
  let j : ℕ := #[19, 20, 0, 21, 22, 1, 2, 23, 3, 24, 25, 26, 27, 4, 5, 6, 28, 7, 8, 9, 10, 29, 11, 12, 13, 30, 31, 32, 33, 14, 34, 15, 16, 35, 36, 17, 37, 18][i.val]!
  if j<19 then .inl (Fin.ofNat 19 j) else .inr (Fin.ofNat 19 (j-19))

def indexing : (Fin 19 ⊕ Fin 19) ≃ Fin 38 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 19,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*37)*(37-1)^18) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 18 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 18 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 18=(2*37)*(37-1)^18 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquaresOpposite


namespace SplitNonsquaresOpposite
def rawWords (i : ℕ) : ℕ := #[182042, 73553, 178864, 155281, 47183, 128388, 126226, 220204, 246371, 203023, 53483, 74462, 34494, 247924, 140777, 13685, 142306, 91021, 0][i]!
def words (i : Fin 19) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 19 rawWords i=rowTotals i)

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
private theorem row15 : rowAgrees 15=true := by decide +kernel
private theorem row16 : rowAgrees 16=true := by decide +kernel
private theorem row17 : rowAgrees 17=true := by decide +kernel
private theorem row18 : rowAgrees 18=true := by decide +kernel
private theorem rowChecked : allBelow 19 rowAgrees=true := by
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
  have h := allBelow_step h row15
  have h := allBelow_step h row16
  have h := allBelow_step h row17
  have h := allBelow_step h row18
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 19, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 19, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-342:ℤ) := by
  change cubicInteger (fun i : Fin 19 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-342:ℤ) ∧
    87*(19:ℤ)^3+375*19*(4*19-3)+1000*((wordMatrix words-1)^3).trace-
      1110*37*(19-1)=(35598:ℤ) ∧ 0≤(35598:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 19 ⊕ Fin 19 → Fin 38
  | .inl i => Fin.ofNat 38 (#[1, 3, 4, 7, 9, 10, 11, 12, 16, 21, 25, 26, 27, 28, 30, 33, 34, 36, 37][i.val]!)
  | .inr i => Fin.ofNat 38 (#[0, 2, 5, 6, 8, 13, 14, 15, 17, 18, 19, 20, 22, 23, 24, 29, 31, 32, 35][i.val]!)

def pointPosition (i : Fin 38) : Fin 19 ⊕ Fin 19 :=
  let j : ℕ := #[19, 0, 20, 1, 2, 21, 22, 3, 23, 4, 5, 6, 7, 24, 25, 26, 8, 27, 28, 29, 30, 9, 31, 32, 33, 10, 11, 12, 13, 34, 14, 35, 36, 15, 16, 37, 17, 18][i.val]!
  if j<19 then .inl (Fin.ofNat 19 j) else .inr (Fin.ofNat 19 (j-19))

def indexing : (Fin 19 ⊕ Fin 19) ≃ Fin 38 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 19,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*37)*(37-1)^18) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 18 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 18 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 18=(2*37)*(37-1)^18 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquaresOpposite


namespace NonsplitNegativeOpposite
def rawWords (i : ℕ) : ℕ := #[153454, 73105, 30257, 191553, 55334, 241173, 95369, 252482, 168963, 196773, 67951, 148666, 172503, 102508, 133341, 143800, 141026, 121769, 0][i]!
def words (i : Fin 19) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 19 rawWords i=rowTotals i)

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
private theorem row15 : rowAgrees 15=true := by decide +kernel
private theorem row16 : rowAgrees 16=true := by decide +kernel
private theorem row17 : rowAgrees 17=true := by decide +kernel
private theorem row18 : rowAgrees 18=true := by decide +kernel
private theorem rowChecked : allBelow 19 rowAgrees=true := by
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
  have h := allBelow_step h row15
  have h := allBelow_step h row16
  have h := allBelow_step h row17
  have h := allBelow_step h row18
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 19, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 19, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(114:ℤ) := by
  change cubicInteger (fun i : Fin 19 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(114:ℤ) ∧
    87*(19:ℤ)^3+375*19*(4*19-3)+1000*((wordMatrix words-1)^3).trace-
      1110*37*(19-1)=(491598:ℤ) ∧ 0≤(491598:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 19 ⊕ Fin 19 → Fin 38
  | .inl i => Fin.ofNat 38 (#[1, 3, 6, 7, 8, 14, 15, 17, 18, 19, 20, 22, 23, 29, 30, 31, 34, 36, 37][i.val]!)
  | .inr i => Fin.ofNat 38 (#[0, 2, 4, 5, 9, 10, 11, 12, 13, 16, 21, 24, 25, 26, 27, 28, 32, 33, 35][i.val]!)

def pointPosition (i : Fin 38) : Fin 19 ⊕ Fin 19 :=
  let j : ℕ := #[19, 0, 20, 1, 21, 22, 2, 3, 4, 23, 24, 25, 26, 27, 5, 6, 28, 7, 8, 9, 10, 29, 11, 12, 30, 31, 32, 33, 34, 13, 14, 15, 35, 36, 16, 37, 17, 18][i.val]!
  if j<19 then .inl (Fin.ofNat 19 j) else .inr (Fin.ofNat 19 (j-19))

def indexing : (Fin 19 ⊕ Fin 19) ≃ Fin 38 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 19,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*37)*(37-1)^18) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 18 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 18 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 18=(2*37)*(37-1)^18 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegativeOpposite

end PaleyBits37
