import Quantum.Hadamard.ConferenceBitCompletion
open Hadamard.BitTrace Hadamard.DeterminantRatio Matrix
set_option maxHeartbeats 12000000
set_option maxRecDepth 60000
namespace PaleyBits41

def rawFull (i : ℕ) : ℕ := #[328519579848, 657039159696, 1314078319392, 429133383233, 858266766466, 1716533532932, 1234043810313, 269064365075, 538128730150, 1076257460300, 2152514920600, 2106006585649, 2012989915747, 1826956575943, 1454889896335, 710756537119, 1421513074238, 644002892925, 1288005785850, 376988316149, 753976632298, 1507953264596, 816883273641, 1633766547282, 1068509839013, 2137019678026, 2075016100501, 1951008945451, 1702994635351, 1206966015151, 214908774751, 429817549502, 859635099004, 1719270198008, 1239517140465, 280011025379, 560022050758, 1120044101516, 41064947481, 82129894962, 164259789924, 0][i]!
def fullRows (i : Fin 42) : ℕ := rawFull i.val

private theorem fullSymmetric : (wordMatrix fullRows).IsSymm := by
  have h : ∀ i j : Fin 42, sign (fullRows i) j.val=sign (fullRows j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem fullDiagonal : ∀ i : Fin 42, sign (fullRows i) i.val=1 := by decide +kernel
private theorem lower0 : (lowerRow 42 rawFull) 0=true := by decide +kernel
private theorem lower1 : (lowerRow 42 rawFull) 1=true := by decide +kernel
private theorem lower2 : (lowerRow 42 rawFull) 2=true := by decide +kernel
private theorem lower3 : (lowerRow 42 rawFull) 3=true := by decide +kernel
private theorem lower4 : (lowerRow 42 rawFull) 4=true := by decide +kernel
private theorem lower5 : (lowerRow 42 rawFull) 5=true := by decide +kernel
private theorem lower6 : (lowerRow 42 rawFull) 6=true := by decide +kernel
private theorem lower7 : (lowerRow 42 rawFull) 7=true := by decide +kernel
private theorem lower8 : (lowerRow 42 rawFull) 8=true := by decide +kernel
private theorem lower9 : (lowerRow 42 rawFull) 9=true := by decide +kernel
private theorem lower10 : (lowerRow 42 rawFull) 10=true := by decide +kernel
private theorem lower11 : (lowerRow 42 rawFull) 11=true := by decide +kernel
private theorem lower12 : (lowerRow 42 rawFull) 12=true := by decide +kernel
private theorem lower13 : (lowerRow 42 rawFull) 13=true := by decide +kernel
private theorem lower14 : (lowerRow 42 rawFull) 14=true := by decide +kernel
private theorem lower15 : (lowerRow 42 rawFull) 15=true := by decide +kernel
private theorem lower16 : (lowerRow 42 rawFull) 16=true := by decide +kernel
private theorem lower17 : (lowerRow 42 rawFull) 17=true := by decide +kernel
private theorem lower18 : (lowerRow 42 rawFull) 18=true := by decide +kernel
private theorem lower19 : (lowerRow 42 rawFull) 19=true := by decide +kernel
private theorem lower20 : (lowerRow 42 rawFull) 20=true := by decide +kernel
private theorem lower21 : (lowerRow 42 rawFull) 21=true := by decide +kernel
private theorem lower22 : (lowerRow 42 rawFull) 22=true := by decide +kernel
private theorem lower23 : (lowerRow 42 rawFull) 23=true := by decide +kernel
private theorem lower24 : (lowerRow 42 rawFull) 24=true := by decide +kernel
private theorem lower25 : (lowerRow 42 rawFull) 25=true := by decide +kernel
private theorem lower26 : (lowerRow 42 rawFull) 26=true := by decide +kernel
private theorem lower27 : (lowerRow 42 rawFull) 27=true := by decide +kernel
private theorem lower28 : (lowerRow 42 rawFull) 28=true := by decide +kernel
private theorem lower29 : (lowerRow 42 rawFull) 29=true := by decide +kernel
private theorem lower30 : (lowerRow 42 rawFull) 30=true := by decide +kernel
private theorem lower31 : (lowerRow 42 rawFull) 31=true := by decide +kernel
private theorem lower32 : (lowerRow 42 rawFull) 32=true := by decide +kernel
private theorem lower33 : (lowerRow 42 rawFull) 33=true := by decide +kernel
private theorem lower34 : (lowerRow 42 rawFull) 34=true := by decide +kernel
private theorem lower35 : (lowerRow 42 rawFull) 35=true := by decide +kernel
private theorem lower36 : (lowerRow 42 rawFull) 36=true := by decide +kernel
private theorem lower37 : (lowerRow 42 rawFull) 37=true := by decide +kernel
private theorem lower38 : (lowerRow 42 rawFull) 38=true := by decide +kernel
private theorem lower39 : (lowerRow 42 rawFull) 39=true := by decide +kernel
private theorem lower40 : (lowerRow 42 rawFull) 40=true := by decide +kernel
private theorem lower41 : (lowerRow 42 rawFull) 41=true := by decide +kernel
private theorem lowerChecked : allBelow 42 (lowerRow 42 rawFull)=true := by
  have h : allBelow 0 (lowerRow 42 rawFull)=true := rfl
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
  have h := allBelow_step h lower38
  have h := allBelow_step h lower39
  have h := allBelow_step h lower40
  have h := allBelow_step h lower41
  exact h

private theorem fullPairs : ∀ i j : Fin 42, i≠j →
    correlation 42 (fullRows i) (fullRows j)=2*sign (fullRows i) j.val :=
  correlations_of_lower rawFull fullSymmetric lowerChecked


namespace SplitSquares
def rawWords (i : ℕ) : ℕ := #[0, 685864, 1493360, 646018, 1689380, 441366, 1006852, 2013448, 1134814, 1435674, 905330, 1278700, 1443306, 2015906, 272222, 536252, 1707864, 604390, 1079012, 238810, 342932][i]!
def words (i : Fin 21) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[41, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 21 rawWords i=rowTotals i)

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
private theorem row19 : rowAgrees 19=true := by decide +kernel
private theorem row20 : rowAgrees 20=true := by decide +kernel
private theorem rowChecked : allBelow 21 rowAgrees=true := by
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
  have h := allBelow_step h row19
  have h := allBelow_step h row20
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 21, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 21, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(60:ℤ) := by
  change cubicInteger (fun i : Fin 21 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(60:ℤ) ∧
    87*(21:ℤ)^3+375*21*(4*21-3)+1000*((wordMatrix words-1)^3).trace-
      1110*41*(21-1)=(593382:ℤ) ∧ 0≤(593382:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 21 ⊕ Fin 21 → Fin 42
  | .inl i => Fin.ofNat 42 (#[0, 1, 2, 4, 5, 8, 9, 10, 16, 18, 20, 21, 23, 25, 31, 32, 33, 36, 37, 39, 40][i.val]!)
  | .inr i => Fin.ofNat 42 (#[3, 6, 7, 11, 12, 13, 14, 15, 17, 19, 22, 24, 26, 27, 28, 29, 30, 34, 35, 38, 41][i.val]!)

def pointPosition (i : Fin 42) : Fin 21 ⊕ Fin 21 :=
  let j : ℕ := #[0, 1, 2, 21, 3, 4, 22, 23, 5, 6, 7, 24, 25, 26, 27, 28, 8, 29, 9, 30, 10, 11, 31, 12, 32, 13, 33, 34, 35, 36, 37, 14, 15, 16, 38, 39, 17, 18, 40, 19, 20, 41][i.val]!
  if j<21 then .inl (Fin.ofNat 21 j) else .inr (Fin.ofNat 21 (j-21))

def indexing : (Fin 21 ⊕ Fin 21) ≃ Fin 42 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 21,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*41)*(41-1)^20) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 20 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 20 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 20=(2*41)*(41-1)^20 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquares


namespace SplitNonsquares
def rawWords (i : ℕ) : ℕ := #[2097150, 1264517, 951907, 867521, 1751681, 1406213, 717837, 1171995, 518179, 495767, 1452141, 886043, 1720953, 1115641, 1446371, 789461, 535467, 22359, 53037, 1153117, 554163][i]!
def words (i : Fin 21) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[81, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 21 rawWords i=rowTotals i)

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
private theorem row19 : rowAgrees 19=true := by decide +kernel
private theorem row20 : rowAgrees 20=true := by decide +kernel
private theorem rowChecked : allBelow 21 rowAgrees=true := by
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
  have h := allBelow_step h row19
  have h := allBelow_step h row20
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 21, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 21, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-60:ℤ) := by
  change cubicInteger (fun i : Fin 21 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-60:ℤ) ∧
    87*(21:ℤ)^3+375*21*(4*21-3)+1000*((wordMatrix words-1)^3).trace-
      1110*41*(21-1)=(473382:ℤ) ∧ 0≤(473382:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 21 ⊕ Fin 21 → Fin 42
  | .inl i => Fin.ofNat 42 (#[0, 3, 6, 7, 11, 12, 13, 14, 15, 17, 19, 22, 24, 26, 27, 28, 29, 30, 34, 35, 38][i.val]!)
  | .inr i => Fin.ofNat 42 (#[1, 2, 4, 5, 8, 9, 10, 16, 18, 20, 21, 23, 25, 31, 32, 33, 36, 37, 39, 40, 41][i.val]!)

def pointPosition (i : Fin 42) : Fin 21 ⊕ Fin 21 :=
  let j : ℕ := #[0, 21, 22, 1, 23, 24, 2, 3, 25, 26, 27, 4, 5, 6, 7, 8, 28, 9, 29, 10, 30, 31, 11, 32, 12, 33, 13, 14, 15, 16, 17, 34, 35, 36, 18, 19, 37, 38, 20, 39, 40, 41][i.val]!
  if j<21 then .inl (Fin.ofNat 21 j) else .inr (Fin.ofNat 21 (j-21))

def indexing : (Fin 21 ⊕ Fin 21) ≃ Fin 42 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 21,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*41)*(41-1)^20) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 20 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 20 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 20=(2*41)*(41-1)^20 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquares


namespace NonsplitNegative
def rawWords (i : ℕ) : ℕ := #[1151586, 1791473, 1223632, 202624, 1931398, 1559555, 628999, 1258014, 673870, 1495181, 761898, 1376628, 803547, 1868948, 1970994, 1582693, 1051899, 1591214, 31280, 193874, 256695][i]!
def words (i : Fin 21) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 21 rawWords i=rowTotals i)

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
private theorem row19 : rowAgrees 19=true := by decide +kernel
private theorem row20 : rowAgrees 20=true := by decide +kernel
private theorem rowChecked : allBelow 21 rowAgrees=true := by
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
  have h := allBelow_step h row19
  have h := allBelow_step h row20
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 21, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 21, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-420:ℤ) := by
  change cubicInteger (fun i : Fin 21 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-420:ℤ) ∧
    87*(21:ℤ)^3+375*21*(4*21-3)+1000*((wordMatrix words-1)^3).trace-
      1110*41*(21-1)=(113382:ℤ) ∧ 0≤(113382:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 21 ⊕ Fin 21 → Fin 42
  | .inl i => Fin.ofNat 42 (#[0, 3, 4, 5, 10, 14, 15, 16, 18, 19, 20, 21, 22, 23, 25, 26, 27, 31, 36, 37, 38][i.val]!)
  | .inr i => Fin.ofNat 42 (#[1, 2, 6, 7, 8, 9, 11, 12, 13, 17, 24, 28, 29, 30, 32, 33, 34, 35, 39, 40, 41][i.val]!)

def pointPosition (i : Fin 42) : Fin 21 ⊕ Fin 21 :=
  let j : ℕ := #[0, 21, 22, 1, 2, 3, 23, 24, 25, 26, 4, 27, 28, 29, 5, 6, 7, 30, 8, 9, 10, 11, 12, 13, 31, 14, 15, 16, 32, 33, 34, 17, 35, 36, 37, 38, 18, 19, 20, 39, 40, 41][i.val]!
  if j<21 then .inl (Fin.ofNat 21 j) else .inr (Fin.ofNat 21 (j-21))

def indexing : (Fin 21 ⊕ Fin 21) ≃ Fin 42 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 21,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*41)*(41-1)^20) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 20 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 20 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 20=(2*41)*(41-1)^20 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegative


namespace SplitSquaresOpposite
def rawWords (i : ℕ) : ℕ := #[632258, 475953, 433760, 875840, 703106, 358918, 585997, 259089, 247883, 726070, 443021, 860476, 557820, 723185, 394730, 267733, 11179, 26518, 576558, 277081, 0][i]!
def words (i : Fin 21) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 81]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 21 rawWords i=rowTotals i)

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
private theorem row19 : rowAgrees 19=true := by decide +kernel
private theorem row20 : rowAgrees 20=true := by decide +kernel
private theorem rowChecked : allBelow 21 rowAgrees=true := by
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
  have h := allBelow_step h row19
  have h := allBelow_step h row20
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 21, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 21, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-60:ℤ) := by
  change cubicInteger (fun i : Fin 21 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-60:ℤ) ∧
    87*(21:ℤ)^3+375*21*(4*21-3)+1000*((wordMatrix words-1)^3).trace-
      1110*41*(21-1)=(473382:ℤ) ∧ 0≤(473382:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 21 ⊕ Fin 21 → Fin 42
  | .inl i => Fin.ofNat 42 (#[3, 6, 7, 11, 12, 13, 14, 15, 17, 19, 22, 24, 26, 27, 28, 29, 30, 34, 35, 38, 41][i.val]!)
  | .inr i => Fin.ofNat 42 (#[0, 1, 2, 4, 5, 8, 9, 10, 16, 18, 20, 21, 23, 25, 31, 32, 33, 36, 37, 39, 40][i.val]!)

def pointPosition (i : Fin 42) : Fin 21 ⊕ Fin 21 :=
  let j : ℕ := #[21, 22, 23, 0, 24, 25, 1, 2, 26, 27, 28, 3, 4, 5, 6, 7, 29, 8, 30, 9, 31, 32, 10, 33, 11, 34, 12, 13, 14, 15, 16, 35, 36, 37, 17, 18, 38, 39, 19, 40, 41, 20][i.val]!
  if j<21 then .inl (Fin.ofNat 21 j) else .inr (Fin.ofNat 21 (j-21))

def indexing : (Fin 21 ⊕ Fin 21) ≃ Fin 42 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 21,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*41)*(41-1)^20) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 20 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 20 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 20=(2*41)*(41-1)^20 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquaresOpposite


namespace SplitNonsquaresOpposite
def rawWords (i : ℕ) : ℕ := #[342932, 746680, 323009, 844690, 220683, 503426, 1006724, 567407, 717837, 452665, 639350, 721653, 1007953, 136111, 268126, 853932, 302195, 539506, 119405, 171466, 0][i]!
def words (i : Fin 21) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 41]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 21 rawWords i=rowTotals i)

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
private theorem row19 : rowAgrees 19=true := by decide +kernel
private theorem row20 : rowAgrees 20=true := by decide +kernel
private theorem rowChecked : allBelow 21 rowAgrees=true := by
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
  have h := allBelow_step h row19
  have h := allBelow_step h row20
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 21, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 21, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(60:ℤ) := by
  change cubicInteger (fun i : Fin 21 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(60:ℤ) ∧
    87*(21:ℤ)^3+375*21*(4*21-3)+1000*((wordMatrix words-1)^3).trace-
      1110*41*(21-1)=(593382:ℤ) ∧ 0≤(593382:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 21 ⊕ Fin 21 → Fin 42
  | .inl i => Fin.ofNat 42 (#[1, 2, 4, 5, 8, 9, 10, 16, 18, 20, 21, 23, 25, 31, 32, 33, 36, 37, 39, 40, 41][i.val]!)
  | .inr i => Fin.ofNat 42 (#[0, 3, 6, 7, 11, 12, 13, 14, 15, 17, 19, 22, 24, 26, 27, 28, 29, 30, 34, 35, 38][i.val]!)

def pointPosition (i : Fin 42) : Fin 21 ⊕ Fin 21 :=
  let j : ℕ := #[21, 0, 1, 22, 2, 3, 23, 24, 4, 5, 6, 25, 26, 27, 28, 29, 7, 30, 8, 31, 9, 10, 32, 11, 33, 12, 34, 35, 36, 37, 38, 13, 14, 15, 39, 40, 16, 17, 41, 18, 19, 20][i.val]!
  if j<21 then .inl (Fin.ofNat 21 j) else .inr (Fin.ofNat 21 (j-21))

def indexing : (Fin 21 ⊕ Fin 21) ≃ Fin 42 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 21,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*41)*(41-1)^20) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 20 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 20 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 20=(2*41)*(41-1)^20 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquaresOpposite


namespace NonsplitNegativeOpposite
def rawWords (i : ℕ) : ℕ := #[407960, 556848, 781216, 234753, 221251, 429190, 962064, 857125, 945167, 359494, 402410, 983911, 672395, 34647, 398102, 794732, 527004, 23933, 53217, 104902, 0][i]!
def words (i : Fin 21) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 21 rawWords i=rowTotals i)

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
private theorem row19 : rowAgrees 19=true := by decide +kernel
private theorem row20 : rowAgrees 20=true := by decide +kernel
private theorem rowChecked : allBelow 21 rowAgrees=true := by
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
  have h := allBelow_step h row19
  have h := allBelow_step h row20
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 21, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 21, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(420:ℤ) := by
  change cubicInteger (fun i : Fin 21 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(420:ℤ) ∧
    87*(21:ℤ)^3+375*21*(4*21-3)+1000*((wordMatrix words-1)^3).trace-
      1110*41*(21-1)=(953382:ℤ) ∧ 0≤(953382:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 21 ⊕ Fin 21 → Fin 42
  | .inl i => Fin.ofNat 42 (#[1, 2, 6, 7, 8, 9, 11, 12, 13, 17, 24, 28, 29, 30, 32, 33, 34, 35, 39, 40, 41][i.val]!)
  | .inr i => Fin.ofNat 42 (#[0, 3, 4, 5, 10, 14, 15, 16, 18, 19, 20, 21, 22, 23, 25, 26, 27, 31, 36, 37, 38][i.val]!)

def pointPosition (i : Fin 42) : Fin 21 ⊕ Fin 21 :=
  let j : ℕ := #[21, 0, 1, 22, 23, 24, 2, 3, 4, 5, 25, 6, 7, 8, 26, 27, 28, 9, 29, 30, 31, 32, 33, 34, 10, 35, 36, 37, 11, 12, 13, 38, 14, 15, 16, 17, 39, 40, 41, 18, 19, 20][i.val]!
  if j<21 then .inl (Fin.ofNat 21 j) else .inr (Fin.ofNat 21 (j-21))

def indexing : (Fin 21 ⊕ Fin 21) ≃ Fin 42 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 21,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*41)*(41-1)^20) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 20 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 20 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 20=(2*41)*(41-1)^20 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegativeOpposite

end PaleyBits41
