import Quantum.Hadamard.ConferenceBitCompletion
open Hadamard.BitTrace Hadamard.DeterminantRatio Matrix
set_option maxHeartbeats 12000000
set_option maxRecDepth 60000
namespace PaleyBits53

def rawFull (i : ℕ) : ℕ := #[3697175711994156, 7394351423988312, 5781503593235633, 2555807931730275, 5111615863460550, 1216032472180109, 2432064944360218, 4864129888720436, 721060522699881, 1442121045399762, 2884242090799524, 5768484181599048, 2529769108457105, 5059538216914210, 1111877179087429, 2223754358174858, 4447508716349716, 8895017432699432, 8782835610657873, 8558471966574755, 8109744678408519, 7212290102076047, 5417380949411103, 1827562644081215, 3655125288162430, 7310250576324860, 5613301897908729, 2219404541076467, 4438809082152934, 8877618164305868, 8748037073870745, 8488874893000499, 7970550531260007, 6933901807779023, 4860604360817055, 714009466893119, 1428018933786238, 2856037867572476, 5712075735144952, 2416952215548913, 4833904431097826, 660609607454661, 1321219214909322, 2642438429818644, 5284876859637288, 1562554464533585, 3125108929067170, 6250217858134340, 3493236461527689, 6986472923055378, 4965746591369765, 924293927998539, 1848587855997078, 0][i]!
def fullRows (i : Fin 54) : ℕ := rawFull i.val

private theorem fullSymmetric : (wordMatrix fullRows).IsSymm := by
  have h : ∀ i j : Fin 54, sign (fullRows i) j.val=sign (fullRows j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem fullDiagonal : ∀ i : Fin 54, sign (fullRows i) i.val=1 := by decide +kernel
private theorem lower0 : (lowerRow 54 rawFull) 0=true := by decide +kernel
private theorem lower1 : (lowerRow 54 rawFull) 1=true := by decide +kernel
private theorem lower2 : (lowerRow 54 rawFull) 2=true := by decide +kernel
private theorem lower3 : (lowerRow 54 rawFull) 3=true := by decide +kernel
private theorem lower4 : (lowerRow 54 rawFull) 4=true := by decide +kernel
private theorem lower5 : (lowerRow 54 rawFull) 5=true := by decide +kernel
private theorem lower6 : (lowerRow 54 rawFull) 6=true := by decide +kernel
private theorem lower7 : (lowerRow 54 rawFull) 7=true := by decide +kernel
private theorem lower8 : (lowerRow 54 rawFull) 8=true := by decide +kernel
private theorem lower9 : (lowerRow 54 rawFull) 9=true := by decide +kernel
private theorem lower10 : (lowerRow 54 rawFull) 10=true := by decide +kernel
private theorem lower11 : (lowerRow 54 rawFull) 11=true := by decide +kernel
private theorem lower12 : (lowerRow 54 rawFull) 12=true := by decide +kernel
private theorem lower13 : (lowerRow 54 rawFull) 13=true := by decide +kernel
private theorem lower14 : (lowerRow 54 rawFull) 14=true := by decide +kernel
private theorem lower15 : (lowerRow 54 rawFull) 15=true := by decide +kernel
private theorem lower16 : (lowerRow 54 rawFull) 16=true := by decide +kernel
private theorem lower17 : (lowerRow 54 rawFull) 17=true := by decide +kernel
private theorem lower18 : (lowerRow 54 rawFull) 18=true := by decide +kernel
private theorem lower19 : (lowerRow 54 rawFull) 19=true := by decide +kernel
private theorem lower20 : (lowerRow 54 rawFull) 20=true := by decide +kernel
private theorem lower21 : (lowerRow 54 rawFull) 21=true := by decide +kernel
private theorem lower22 : (lowerRow 54 rawFull) 22=true := by decide +kernel
private theorem lower23 : (lowerRow 54 rawFull) 23=true := by decide +kernel
private theorem lower24 : (lowerRow 54 rawFull) 24=true := by decide +kernel
private theorem lower25 : (lowerRow 54 rawFull) 25=true := by decide +kernel
private theorem lower26 : (lowerRow 54 rawFull) 26=true := by decide +kernel
private theorem lower27 : (lowerRow 54 rawFull) 27=true := by decide +kernel
private theorem lower28 : (lowerRow 54 rawFull) 28=true := by decide +kernel
private theorem lower29 : (lowerRow 54 rawFull) 29=true := by decide +kernel
private theorem lower30 : (lowerRow 54 rawFull) 30=true := by decide +kernel
private theorem lower31 : (lowerRow 54 rawFull) 31=true := by decide +kernel
private theorem lower32 : (lowerRow 54 rawFull) 32=true := by decide +kernel
private theorem lower33 : (lowerRow 54 rawFull) 33=true := by decide +kernel
private theorem lower34 : (lowerRow 54 rawFull) 34=true := by decide +kernel
private theorem lower35 : (lowerRow 54 rawFull) 35=true := by decide +kernel
private theorem lower36 : (lowerRow 54 rawFull) 36=true := by decide +kernel
private theorem lower37 : (lowerRow 54 rawFull) 37=true := by decide +kernel
private theorem lower38 : (lowerRow 54 rawFull) 38=true := by decide +kernel
private theorem lower39 : (lowerRow 54 rawFull) 39=true := by decide +kernel
private theorem lower40 : (lowerRow 54 rawFull) 40=true := by decide +kernel
private theorem lower41 : (lowerRow 54 rawFull) 41=true := by decide +kernel
private theorem lower42 : (lowerRow 54 rawFull) 42=true := by decide +kernel
private theorem lower43 : (lowerRow 54 rawFull) 43=true := by decide +kernel
private theorem lower44 : (lowerRow 54 rawFull) 44=true := by decide +kernel
private theorem lower45 : (lowerRow 54 rawFull) 45=true := by decide +kernel
private theorem lower46 : (lowerRow 54 rawFull) 46=true := by decide +kernel
private theorem lower47 : (lowerRow 54 rawFull) 47=true := by decide +kernel
private theorem lower48 : (lowerRow 54 rawFull) 48=true := by decide +kernel
private theorem lower49 : (lowerRow 54 rawFull) 49=true := by decide +kernel
private theorem lower50 : (lowerRow 54 rawFull) 50=true := by decide +kernel
private theorem lower51 : (lowerRow 54 rawFull) 51=true := by decide +kernel
private theorem lower52 : (lowerRow 54 rawFull) 52=true := by decide +kernel
private theorem lower53 : (lowerRow 54 rawFull) 53=true := by decide +kernel
private theorem lowerChecked : allBelow 54 (lowerRow 54 rawFull)=true := by
  have h : allBelow 0 (lowerRow 54 rawFull)=true := rfl
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
  have h := allBelow_step h lower42
  have h := allBelow_step h lower43
  have h := allBelow_step h lower44
  have h := allBelow_step h lower45
  have h := allBelow_step h lower46
  have h := allBelow_step h lower47
  have h := allBelow_step h lower48
  have h := allBelow_step h lower49
  have h := allBelow_step h lower50
  have h := allBelow_step h lower51
  have h := allBelow_step h lower52
  have h := allBelow_step h lower53
  exact h

private theorem fullPairs : ∀ i j : Fin 54, i≠j →
    correlation 54 (fullRows i) (fullRows j)=2*sign (fullRows i) j.val :=
  correlations_of_lower rawFull fullSymmetric lowerChecked


namespace SplitSquares
def rawWords (i : ℕ) : ℕ := #[0, 110711596, 103232570, 17821862, 77521508, 7981214, 41669392, 83273000, 99165890, 60262738, 62345604, 124756512, 32867406, 98716060, 60367994, 119675640, 4480878, 35172060, 78192284, 70666618, 21649138, 9223652, 126958048, 40138642, 105971464, 96652870, 55355798][i]!
def words (i : Fin 27) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[53, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 27 rawWords i=rowTotals i)

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
private theorem row21 : rowAgrees 21=true := by decide +kernel
private theorem row22 : rowAgrees 22=true := by decide +kernel
private theorem row23 : rowAgrees 23=true := by decide +kernel
private theorem row24 : rowAgrees 24=true := by decide +kernel
private theorem row25 : rowAgrees 25=true := by decide +kernel
private theorem row26 : rowAgrees 26=true := by decide +kernel
private theorem rowChecked : allBelow 27 rowAgrees=true := by
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
  have h := allBelow_step h row21
  have h := allBelow_step h row22
  have h := allBelow_step h row23
  have h := allBelow_step h row24
  have h := allBelow_step h row25
  have h := allBelow_step h row26
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 27, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 27, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(546:ℤ) := by
  change cubicInteger (fun i : Fin 27 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(546:ℤ) ∧
    87*(27:ℤ)^3+375*27*(4*27-3)+1000*((wordMatrix words-1)^3).trace-
      1110*53*(27-1)=(1791966:ℤ) ∧ 0≤(1791966:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 27 ⊕ Fin 27 → Fin 54
  | .inl i => Fin.ofNat 54 (#[0, 1, 4, 6, 7, 9, 10, 11, 13, 15, 16, 17, 24, 25, 28, 29, 36, 37, 38, 40, 42, 43, 44, 46, 47, 49, 52][i.val]!)
  | .inr i => Fin.ofNat 54 (#[2, 3, 5, 8, 12, 14, 18, 19, 20, 21, 22, 23, 26, 27, 30, 31, 32, 33, 34, 35, 39, 41, 45, 48, 50, 51, 53][i.val]!)

def pointPosition (i : Fin 54) : Fin 27 ⊕ Fin 27 :=
  let j : ℕ := #[0, 1, 27, 28, 2, 29, 3, 4, 30, 5, 6, 7, 31, 8, 32, 9, 10, 11, 33, 34, 35, 36, 37, 38, 12, 13, 39, 40, 14, 15, 41, 42, 43, 44, 45, 46, 16, 17, 18, 47, 19, 48, 20, 21, 22, 49, 23, 24, 50, 25, 51, 52, 26, 53][i.val]!
  if j<27 then .inl (Fin.ofNat 27 j) else .inr (Fin.ofNat 27 (j-27))

def indexing : (Fin 27 ⊕ Fin 27) ≃ Fin 54 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 27,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*53)*(53-1)^26) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 26 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 26 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 26=(2*53)*(53-1)^26 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquares


namespace SplitNonsquares
def rawWords (i : ℕ) : ℕ := #[134217726, 39722569, 85769241, 36925719, 7989773, 79667777, 31336739, 132298241, 115690569, 107616435, 91500935, 29934423, 47261327, 25761021, 66226457, 118900917, 111948089, 102286059, 80840039, 19081847, 447615, 71911353, 2383827, 50690529, 109636805, 25416587, 19367845][i]!
def words (i : Fin 27) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[105, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 27 rawWords i=rowTotals i)

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
private theorem row21 : rowAgrees 21=true := by decide +kernel
private theorem row22 : rowAgrees 22=true := by decide +kernel
private theorem row23 : rowAgrees 23=true := by decide +kernel
private theorem row24 : rowAgrees 24=true := by decide +kernel
private theorem row25 : rowAgrees 25=true := by decide +kernel
private theorem row26 : rowAgrees 26=true := by decide +kernel
private theorem rowChecked : allBelow 27 rowAgrees=true := by
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
  have h := allBelow_step h row21
  have h := allBelow_step h row22
  have h := allBelow_step h row23
  have h := allBelow_step h row24
  have h := allBelow_step h row25
  have h := allBelow_step h row26
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 27, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 27, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-546:ℤ) := by
  change cubicInteger (fun i : Fin 27 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-546:ℤ) ∧
    87*(27:ℤ)^3+375*27*(4*27-3)+1000*((wordMatrix words-1)^3).trace-
      1110*53*(27-1)=(699966:ℤ) ∧ 0≤(699966:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 27 ⊕ Fin 27 → Fin 54
  | .inl i => Fin.ofNat 54 (#[0, 2, 3, 5, 8, 12, 14, 18, 19, 20, 21, 22, 23, 26, 27, 30, 31, 32, 33, 34, 35, 39, 41, 45, 48, 50, 51][i.val]!)
  | .inr i => Fin.ofNat 54 (#[1, 4, 6, 7, 9, 10, 11, 13, 15, 16, 17, 24, 25, 28, 29, 36, 37, 38, 40, 42, 43, 44, 46, 47, 49, 52, 53][i.val]!)

def pointPosition (i : Fin 54) : Fin 27 ⊕ Fin 27 :=
  let j : ℕ := #[0, 27, 1, 2, 28, 3, 29, 30, 4, 31, 32, 33, 5, 34, 6, 35, 36, 37, 7, 8, 9, 10, 11, 12, 38, 39, 13, 14, 40, 41, 15, 16, 17, 18, 19, 20, 42, 43, 44, 21, 45, 22, 46, 47, 48, 23, 49, 50, 24, 51, 25, 26, 52, 53][i.val]!
  if j<27 then .inl (Fin.ofNat 27 j) else .inr (Fin.ofNat 27 (j-27))

def indexing : (Fin 27 ⊕ Fin 27) ≃ Fin 54 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 27,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*53)*(53-1)^26) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 26 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 26 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 26=(2*53)*(53-1)^26 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquares


namespace NonsplitNegative
def rawWords (i : ℕ) : ℕ := #[84671754, 10959181, 36630578, 6072003, 77400356, 24961812, 108384394, 33521736, 64427571, 133995816, 102339337, 79311379, 58085191, 39880751, 121704549, 103753453, 75810259, 17602951, 21730302, 80121533, 18882552, 84982502, 42759144, 38341522, 70669217, 79755076, 53071441][i]!
def words (i : Fin 27) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 27 rawWords i=rowTotals i)

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
private theorem row21 : rowAgrees 21=true := by decide +kernel
private theorem row22 : rowAgrees 22=true := by decide +kernel
private theorem row23 : rowAgrees 23=true := by decide +kernel
private theorem row24 : rowAgrees 24=true := by decide +kernel
private theorem row25 : rowAgrees 25=true := by decide +kernel
private theorem row26 : rowAgrees 26=true := by decide +kernel
private theorem rowChecked : allBelow 27 rowAgrees=true := by
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
  have h := allBelow_step h row21
  have h := allBelow_step h row22
  have h := allBelow_step h row23
  have h := allBelow_step h row24
  have h := allBelow_step h row25
  have h := allBelow_step h row26
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 27, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 27, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-378:ℤ) := by
  change cubicInteger (fun i : Fin 27 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-378:ℤ) ∧
    87*(27:ℤ)^3+375*27*(4*27-3)+1000*((wordMatrix words-1)^3).trace-
      1110*53*(27-1)=(867966:ℤ) ∧ 0≤(867966:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 27 ⊕ Fin 27 → Fin 54
  | .inl i => Fin.ofNat 54 (#[0, 2, 4, 5, 6, 9, 10, 13, 14, 17, 19, 20, 22, 23, 30, 31, 33, 34, 36, 39, 40, 43, 44, 47, 48, 49, 51][i.val]!)
  | .inr i => Fin.ofNat 54 (#[1, 3, 7, 8, 11, 12, 15, 16, 18, 21, 24, 25, 26, 27, 28, 29, 32, 35, 37, 38, 41, 42, 45, 46, 50, 52, 53][i.val]!)

def pointPosition (i : Fin 54) : Fin 27 ⊕ Fin 27 :=
  let j : ℕ := #[0, 27, 1, 28, 2, 3, 4, 29, 30, 5, 6, 31, 32, 7, 8, 33, 34, 9, 35, 10, 11, 36, 12, 13, 37, 38, 39, 40, 41, 42, 14, 15, 43, 16, 17, 44, 18, 45, 46, 19, 20, 47, 48, 21, 22, 49, 50, 23, 24, 25, 51, 26, 52, 53][i.val]!
  if j<27 then .inl (Fin.ofNat 27 j) else .inr (Fin.ofNat 27 (j-27))

def indexing : (Fin 27 ⊕ Fin 27) ≃ Fin 54 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 27,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*53)*(53-1)^26) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 26 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 26 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 26=(2*53)*(53-1)^26 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegative


namespace SplitSquaresOpposite
def rawWords (i : ℕ) : ℕ := #[19861284, 42884620, 18462859, 3994886, 39833888, 15668369, 66149120, 57845284, 53808217, 45750467, 14967211, 23630663, 12880510, 33113228, 59450458, 55974044, 51143029, 40420019, 9540923, 223807, 35955676, 1191913, 25345264, 54818402, 12708293, 9683922, 0][i]!
def words (i : Fin 27) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 105]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 27 rawWords i=rowTotals i)

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
private theorem row21 : rowAgrees 21=true := by decide +kernel
private theorem row22 : rowAgrees 22=true := by decide +kernel
private theorem row23 : rowAgrees 23=true := by decide +kernel
private theorem row24 : rowAgrees 24=true := by decide +kernel
private theorem row25 : rowAgrees 25=true := by decide +kernel
private theorem row26 : rowAgrees 26=true := by decide +kernel
private theorem rowChecked : allBelow 27 rowAgrees=true := by
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
  have h := allBelow_step h row21
  have h := allBelow_step h row22
  have h := allBelow_step h row23
  have h := allBelow_step h row24
  have h := allBelow_step h row25
  have h := allBelow_step h row26
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 27, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 27, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-546:ℤ) := by
  change cubicInteger (fun i : Fin 27 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-546:ℤ) ∧
    87*(27:ℤ)^3+375*27*(4*27-3)+1000*((wordMatrix words-1)^3).trace-
      1110*53*(27-1)=(699966:ℤ) ∧ 0≤(699966:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 27 ⊕ Fin 27 → Fin 54
  | .inl i => Fin.ofNat 54 (#[2, 3, 5, 8, 12, 14, 18, 19, 20, 21, 22, 23, 26, 27, 30, 31, 32, 33, 34, 35, 39, 41, 45, 48, 50, 51, 53][i.val]!)
  | .inr i => Fin.ofNat 54 (#[0, 1, 4, 6, 7, 9, 10, 11, 13, 15, 16, 17, 24, 25, 28, 29, 36, 37, 38, 40, 42, 43, 44, 46, 47, 49, 52][i.val]!)

def pointPosition (i : Fin 54) : Fin 27 ⊕ Fin 27 :=
  let j : ℕ := #[27, 28, 0, 1, 29, 2, 30, 31, 3, 32, 33, 34, 4, 35, 5, 36, 37, 38, 6, 7, 8, 9, 10, 11, 39, 40, 12, 13, 41, 42, 14, 15, 16, 17, 18, 19, 43, 44, 45, 20, 46, 21, 47, 48, 49, 22, 50, 51, 23, 52, 24, 25, 53, 26][i.val]!
  if j<27 then .inl (Fin.ofNat 27 j) else .inr (Fin.ofNat 27 (j-27))

def indexing : (Fin 27 ⊕ Fin 27) ≃ Fin 54 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 27,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*53)*(53-1)^26) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 26 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 26 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 26=(2*53)*(53-1)^26 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquaresOpposite


namespace SplitNonsquaresOpposite
def rawWords (i : ℕ) : ℕ := #[55355798, 51616285, 8910931, 38760754, 3990607, 20834696, 41636500, 49582945, 30131369, 31172802, 62378256, 16433703, 49358030, 30183997, 59837820, 2240439, 17586030, 39096142, 35333309, 10824569, 4611826, 63479024, 20069321, 52985732, 48326435, 27677899, 0][i]!
def words (i : Fin 27) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 53]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 27 rawWords i=rowTotals i)

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
private theorem row21 : rowAgrees 21=true := by decide +kernel
private theorem row22 : rowAgrees 22=true := by decide +kernel
private theorem row23 : rowAgrees 23=true := by decide +kernel
private theorem row24 : rowAgrees 24=true := by decide +kernel
private theorem row25 : rowAgrees 25=true := by decide +kernel
private theorem row26 : rowAgrees 26=true := by decide +kernel
private theorem rowChecked : allBelow 27 rowAgrees=true := by
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
  have h := allBelow_step h row21
  have h := allBelow_step h row22
  have h := allBelow_step h row23
  have h := allBelow_step h row24
  have h := allBelow_step h row25
  have h := allBelow_step h row26
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 27, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 27, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(546:ℤ) := by
  change cubicInteger (fun i : Fin 27 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(546:ℤ) ∧
    87*(27:ℤ)^3+375*27*(4*27-3)+1000*((wordMatrix words-1)^3).trace-
      1110*53*(27-1)=(1791966:ℤ) ∧ 0≤(1791966:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 27 ⊕ Fin 27 → Fin 54
  | .inl i => Fin.ofNat 54 (#[1, 4, 6, 7, 9, 10, 11, 13, 15, 16, 17, 24, 25, 28, 29, 36, 37, 38, 40, 42, 43, 44, 46, 47, 49, 52, 53][i.val]!)
  | .inr i => Fin.ofNat 54 (#[0, 2, 3, 5, 8, 12, 14, 18, 19, 20, 21, 22, 23, 26, 27, 30, 31, 32, 33, 34, 35, 39, 41, 45, 48, 50, 51][i.val]!)

def pointPosition (i : Fin 54) : Fin 27 ⊕ Fin 27 :=
  let j : ℕ := #[27, 0, 28, 29, 1, 30, 2, 3, 31, 4, 5, 6, 32, 7, 33, 8, 9, 10, 34, 35, 36, 37, 38, 39, 11, 12, 40, 41, 13, 14, 42, 43, 44, 45, 46, 47, 15, 16, 17, 48, 18, 49, 19, 20, 21, 50, 22, 23, 51, 24, 52, 53, 25, 26][i.val]!
  if j<27 then .inl (Fin.ofNat 27 j) else .inr (Fin.ofNat 27 (j-27))

def indexing : (Fin 27 ⊕ Fin 27) ≃ Fin 54 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 27,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*53)*(53-1)^26) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 26 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 26 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 26=(2*53)*(53-1)^26 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquaresOpposite


namespace NonsplitNegativeOpposite
def rawWords (i : ℕ) : ℕ := #[44262978, 3055193, 45939296, 3862674, 66947210, 15406148, 33464615, 28198680, 56431296, 36869511, 32092835, 46424086, 46712622, 30641229, 27269261, 51721822, 59155761, 860907, 6523350, 59905534, 8954716, 21251839, 19152240, 1670389, 40494544, 17406741, 0][i]!
def words (i : Fin 27) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 27 rawWords i=rowTotals i)

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
private theorem row21 : rowAgrees 21=true := by decide +kernel
private theorem row22 : rowAgrees 22=true := by decide +kernel
private theorem row23 : rowAgrees 23=true := by decide +kernel
private theorem row24 : rowAgrees 24=true := by decide +kernel
private theorem row25 : rowAgrees 25=true := by decide +kernel
private theorem row26 : rowAgrees 26=true := by decide +kernel
private theorem rowChecked : allBelow 27 rowAgrees=true := by
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
  have h := allBelow_step h row21
  have h := allBelow_step h row22
  have h := allBelow_step h row23
  have h := allBelow_step h row24
  have h := allBelow_step h row25
  have h := allBelow_step h row26
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 27, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 27, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(378:ℤ) := by
  change cubicInteger (fun i : Fin 27 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(378:ℤ) ∧
    87*(27:ℤ)^3+375*27*(4*27-3)+1000*((wordMatrix words-1)^3).trace-
      1110*53*(27-1)=(1623966:ℤ) ∧ 0≤(1623966:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 27 ⊕ Fin 27 → Fin 54
  | .inl i => Fin.ofNat 54 (#[1, 3, 7, 8, 11, 12, 15, 16, 18, 21, 24, 25, 26, 27, 28, 29, 32, 35, 37, 38, 41, 42, 45, 46, 50, 52, 53][i.val]!)
  | .inr i => Fin.ofNat 54 (#[0, 2, 4, 5, 6, 9, 10, 13, 14, 17, 19, 20, 22, 23, 30, 31, 33, 34, 36, 39, 40, 43, 44, 47, 48, 49, 51][i.val]!)

def pointPosition (i : Fin 54) : Fin 27 ⊕ Fin 27 :=
  let j : ℕ := #[27, 0, 28, 1, 29, 30, 31, 2, 3, 32, 33, 4, 5, 34, 35, 6, 7, 36, 8, 37, 38, 9, 39, 40, 10, 11, 12, 13, 14, 15, 41, 42, 16, 43, 44, 17, 45, 18, 19, 46, 47, 20, 21, 48, 49, 22, 23, 50, 51, 52, 24, 53, 25, 26][i.val]!
  if j<27 then .inl (Fin.ofNat 27 j) else .inr (Fin.ofNat 27 (j-27))

def indexing : (Fin 27 ⊕ Fin 27) ≃ Fin 54 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 27,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*53)*(53-1)^26) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 26 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 26 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 26=(2*53)*(53-1)^26 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegativeOpposite

end PaleyBits53
