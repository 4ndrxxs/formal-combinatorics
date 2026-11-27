import Quantum.Hadamard.ConferenceBitCompletion
open Hadamard.BitTrace Hadamard.DeterminantRatio Matrix
set_option maxHeartbeats 12000000
set_option maxRecDepth 60000
namespace PaleyBits49

def rawFull (i : ℕ) : ℕ := #[314106316550528, 69626634871680, 134889580873600, 265381117333248, 530727874944512, 498540154125312, 438528134985856, 236161825554503, 467959962255375, 377367749181470, 191785813377084, 379173582340216, 199794991431793, 399555889479779, 392366139646901, 226180106029034, 452325854416725, 341736115150379, 120522545314902, 241010999310509, 477658045493722, 120320020306649, 240605947229491, 476814116367078, 395076325807565, 227237057932059, 450110426994358, 341634853694828, 201313856875675, 398263760624054, 233611925484396, 467223848871641, 375895790816691, 193239406304102, 382114859497037, 435425776127405, 312265551960922, 65978930673205, 131957592911082, 263915183725013, 527796009808683, 497006021387990, 2453955598051, 543958084935, 1053824850575, 2073289979166, 4146311523004, 3894844954104, 3426001054577, 0][i]!
def fullRows (i : Fin 50) : ℕ := rawFull i.val

private theorem fullSymmetric : (wordMatrix fullRows).IsSymm := by
  have h : ∀ i j : Fin 50, sign (fullRows i) j.val=sign (fullRows j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem fullDiagonal : ∀ i : Fin 50, sign (fullRows i) i.val=1 := by decide +kernel
private theorem lower0 : (lowerRow 50 rawFull) 0=true := by decide +kernel
private theorem lower1 : (lowerRow 50 rawFull) 1=true := by decide +kernel
private theorem lower2 : (lowerRow 50 rawFull) 2=true := by decide +kernel
private theorem lower3 : (lowerRow 50 rawFull) 3=true := by decide +kernel
private theorem lower4 : (lowerRow 50 rawFull) 4=true := by decide +kernel
private theorem lower5 : (lowerRow 50 rawFull) 5=true := by decide +kernel
private theorem lower6 : (lowerRow 50 rawFull) 6=true := by decide +kernel
private theorem lower7 : (lowerRow 50 rawFull) 7=true := by decide +kernel
private theorem lower8 : (lowerRow 50 rawFull) 8=true := by decide +kernel
private theorem lower9 : (lowerRow 50 rawFull) 9=true := by decide +kernel
private theorem lower10 : (lowerRow 50 rawFull) 10=true := by decide +kernel
private theorem lower11 : (lowerRow 50 rawFull) 11=true := by decide +kernel
private theorem lower12 : (lowerRow 50 rawFull) 12=true := by decide +kernel
private theorem lower13 : (lowerRow 50 rawFull) 13=true := by decide +kernel
private theorem lower14 : (lowerRow 50 rawFull) 14=true := by decide +kernel
private theorem lower15 : (lowerRow 50 rawFull) 15=true := by decide +kernel
private theorem lower16 : (lowerRow 50 rawFull) 16=true := by decide +kernel
private theorem lower17 : (lowerRow 50 rawFull) 17=true := by decide +kernel
private theorem lower18 : (lowerRow 50 rawFull) 18=true := by decide +kernel
private theorem lower19 : (lowerRow 50 rawFull) 19=true := by decide +kernel
private theorem lower20 : (lowerRow 50 rawFull) 20=true := by decide +kernel
private theorem lower21 : (lowerRow 50 rawFull) 21=true := by decide +kernel
private theorem lower22 : (lowerRow 50 rawFull) 22=true := by decide +kernel
private theorem lower23 : (lowerRow 50 rawFull) 23=true := by decide +kernel
private theorem lower24 : (lowerRow 50 rawFull) 24=true := by decide +kernel
private theorem lower25 : (lowerRow 50 rawFull) 25=true := by decide +kernel
private theorem lower26 : (lowerRow 50 rawFull) 26=true := by decide +kernel
private theorem lower27 : (lowerRow 50 rawFull) 27=true := by decide +kernel
private theorem lower28 : (lowerRow 50 rawFull) 28=true := by decide +kernel
private theorem lower29 : (lowerRow 50 rawFull) 29=true := by decide +kernel
private theorem lower30 : (lowerRow 50 rawFull) 30=true := by decide +kernel
private theorem lower31 : (lowerRow 50 rawFull) 31=true := by decide +kernel
private theorem lower32 : (lowerRow 50 rawFull) 32=true := by decide +kernel
private theorem lower33 : (lowerRow 50 rawFull) 33=true := by decide +kernel
private theorem lower34 : (lowerRow 50 rawFull) 34=true := by decide +kernel
private theorem lower35 : (lowerRow 50 rawFull) 35=true := by decide +kernel
private theorem lower36 : (lowerRow 50 rawFull) 36=true := by decide +kernel
private theorem lower37 : (lowerRow 50 rawFull) 37=true := by decide +kernel
private theorem lower38 : (lowerRow 50 rawFull) 38=true := by decide +kernel
private theorem lower39 : (lowerRow 50 rawFull) 39=true := by decide +kernel
private theorem lower40 : (lowerRow 50 rawFull) 40=true := by decide +kernel
private theorem lower41 : (lowerRow 50 rawFull) 41=true := by decide +kernel
private theorem lower42 : (lowerRow 50 rawFull) 42=true := by decide +kernel
private theorem lower43 : (lowerRow 50 rawFull) 43=true := by decide +kernel
private theorem lower44 : (lowerRow 50 rawFull) 44=true := by decide +kernel
private theorem lower45 : (lowerRow 50 rawFull) 45=true := by decide +kernel
private theorem lower46 : (lowerRow 50 rawFull) 46=true := by decide +kernel
private theorem lower47 : (lowerRow 50 rawFull) 47=true := by decide +kernel
private theorem lower48 : (lowerRow 50 rawFull) 48=true := by decide +kernel
private theorem lower49 : (lowerRow 50 rawFull) 49=true := by decide +kernel
private theorem lowerChecked : allBelow 50 (lowerRow 50 rawFull)=true := by
  have h : allBelow 0 (lowerRow 50 rawFull)=true := rfl
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
  exact h

private theorem fullPairs : ∀ i j : Fin 50, i≠j →
    correlation 50 (fullRows i) (fullRows j)=2*sign (fullRows i) j.val :=
  correlations_of_lower rawFull fullSymmetric lowerChecked


namespace SplitSquares
def rawWords (i : ℕ) : ℕ := #[0, 8223872, 15198592, 31102848, 32070528, 26732288, 20889088, 11428894, 24169532, 10332280, 25797098, 13263702, 24363098, 21171942, 18618806, 7083884, 15218230, 26753260, 24167142, 249562, 12997482, 25530838, 1423646, 3346108, 2520440][i]!
def words (i : Fin 25) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[49, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 25 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 25 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 25, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 25, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(552:ℤ) := by
  change cubicInteger (fun i : Fin 25 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(552:ℤ) ∧
    87*(25:ℤ)^3+375*25*(4*25-3)+1000*((wordMatrix words-1)^3).trace-
      1110*49*(25-1)=(1515390:ℤ) ∧ 0≤(1515390:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 25 ⊕ Fin 25 → Fin 50
  | .inl i => Fin.ofNat 50 (#[0, 1, 2, 3, 4, 5, 6, 9, 10, 11, 15, 18, 20, 23, 26, 27, 29, 30, 33, 36, 38, 41, 45, 46, 47][i.val]!)
  | .inr i => Fin.ofNat 50 (#[7, 8, 12, 13, 14, 16, 17, 19, 21, 22, 24, 25, 28, 31, 32, 34, 35, 37, 39, 40, 42, 43, 44, 48, 49][i.val]!)

def pointPosition (i : Fin 50) : Fin 25 ⊕ Fin 25 :=
  let j : ℕ := #[0, 1, 2, 3, 4, 5, 6, 25, 26, 7, 8, 9, 27, 28, 29, 10, 30, 31, 11, 32, 12, 33, 34, 13, 35, 36, 14, 15, 37, 16, 17, 38, 39, 18, 40, 41, 19, 42, 20, 43, 44, 21, 45, 46, 47, 22, 23, 24, 48, 49][i.val]!
  if j<25 then .inl (Fin.ofNat 25 j) else .inr (Fin.ofNat 25 (j-25))

def indexing : (Fin 25 ⊕ Fin 25) ≃ Fin 50 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 25,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*49)*(49-1)^24) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 24 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 24 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 24=(2*49)*(49-1)^24 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquares


namespace SplitNonsquares
def rawWords (i : ℕ) : ℕ := #[33554430, 11201313, 22715489, 12390273, 22377761, 19555863, 30715397, 28007433, 13924379, 7807083, 13181181, 19972559, 7258517, 11667315, 21764531, 29104199, 31065753, 23147175, 14734169, 8508591, 16886621, 441003, 481109, 894411, 1296629][i]!
def words (i : Fin 25) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[97, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 25 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 25 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 25, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 25, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-552:ℤ) := by
  change cubicInteger (fun i : Fin 25 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-552:ℤ) ∧
    87*(25:ℤ)^3+375*25*(4*25-3)+1000*((wordMatrix words-1)^3).trace-
      1110*49*(25-1)=(411390:ℤ) ∧ 0≤(411390:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 25 ⊕ Fin 25 → Fin 50
  | .inl i => Fin.ofNat 50 (#[0, 7, 8, 12, 13, 14, 16, 17, 19, 21, 22, 24, 25, 28, 31, 32, 34, 35, 37, 39, 40, 42, 43, 44, 48][i.val]!)
  | .inr i => Fin.ofNat 50 (#[1, 2, 3, 4, 5, 6, 9, 10, 11, 15, 18, 20, 23, 26, 27, 29, 30, 33, 36, 38, 41, 45, 46, 47, 49][i.val]!)

def pointPosition (i : Fin 50) : Fin 25 ⊕ Fin 25 :=
  let j : ℕ := #[0, 25, 26, 27, 28, 29, 30, 1, 2, 31, 32, 33, 3, 4, 5, 34, 6, 7, 35, 8, 36, 9, 10, 37, 11, 12, 38, 39, 13, 40, 41, 14, 15, 42, 16, 17, 43, 18, 44, 19, 20, 45, 21, 22, 23, 46, 47, 48, 24, 49][i.val]!
  if j<25 then .inl (Fin.ofNat 25 j) else .inr (Fin.ofNat 25 (j-25))

def indexing : (Fin 25 ⊕ Fin 25) ≃ Fin 50 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 25,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*49)*(49-1)^24) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 24 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 24 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 24=(2*49)*(49-1)^24 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquares


namespace NonsplitNegative
def rawWords (i : ℕ) : ℕ := #[20625184, 8235552, 15659232, 29605312, 18243456, 22635527, 5688332, 28703772, 6887449, 31385619, 20746489, 14197722, 14517661, 9570991, 23102196, 6840015, 30413226, 22291037, 15865558, 29400871, 474867, 312711, 1039214, 866956, 739001][i]!
def words (i : Fin 25) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 25 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 25 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 25, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 25, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(0:ℤ) := by
  change cubicInteger (fun i : Fin 25 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(0:ℤ) ∧
    87*(25:ℤ)^3+375*25*(4*25-3)+1000*((wordMatrix words-1)^3).trace-
      1110*49*(25-1)=(963390:ℤ) ∧ 0≤(963390:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 25 ⊕ Fin 25 → Fin 50
  | .inl i => Fin.ofNat 50 (#[0, 1, 3, 4, 6, 8, 10, 11, 12, 13, 16, 18, 21, 25, 27, 28, 29, 31, 38, 40, 43, 44, 45, 46, 48][i.val]!)
  | .inr i => Fin.ofNat 50 (#[2, 5, 7, 9, 14, 15, 17, 19, 20, 22, 23, 24, 26, 30, 32, 33, 34, 35, 36, 37, 39, 41, 42, 47, 49][i.val]!)

def pointPosition (i : Fin 50) : Fin 25 ⊕ Fin 25 :=
  let j : ℕ := #[0, 1, 25, 2, 3, 26, 4, 27, 5, 28, 6, 7, 8, 9, 29, 30, 10, 31, 11, 32, 33, 12, 34, 35, 36, 13, 37, 14, 15, 16, 38, 17, 39, 40, 41, 42, 43, 44, 18, 45, 19, 46, 47, 20, 21, 22, 23, 48, 24, 49][i.val]!
  if j<25 then .inl (Fin.ofNat 25 j) else .inr (Fin.ofNat 25 (j-25))

def indexing : (Fin 25 ⊕ Fin 25) ≃ Fin 50 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 25,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*49)*(49-1)^24) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 24 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 24 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 24=(2*49)*(49-1)^24 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegative


namespace SplitSquaresOpposite
def rawWords (i : ℕ) : ℕ := #[5600656, 11357744, 6195136, 11188880, 9777931, 15357698, 14003716, 6962189, 3903541, 6590590, 9986279, 3629258, 5833657, 10882265, 14552099, 15532876, 11573587, 7367084, 4254295, 8443310, 220501, 240554, 447205, 648314, 0][i]!
def words (i : Fin 25) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 97]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 25 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 25 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 25, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 25, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-552:ℤ) := by
  change cubicInteger (fun i : Fin 25 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-552:ℤ) ∧
    87*(25:ℤ)^3+375*25*(4*25-3)+1000*((wordMatrix words-1)^3).trace-
      1110*49*(25-1)=(411390:ℤ) ∧ 0≤(411390:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 25 ⊕ Fin 25 → Fin 50
  | .inl i => Fin.ofNat 50 (#[7, 8, 12, 13, 14, 16, 17, 19, 21, 22, 24, 25, 28, 31, 32, 34, 35, 37, 39, 40, 42, 43, 44, 48, 49][i.val]!)
  | .inr i => Fin.ofNat 50 (#[0, 1, 2, 3, 4, 5, 6, 9, 10, 11, 15, 18, 20, 23, 26, 27, 29, 30, 33, 36, 38, 41, 45, 46, 47][i.val]!)

def pointPosition (i : Fin 50) : Fin 25 ⊕ Fin 25 :=
  let j : ℕ := #[25, 26, 27, 28, 29, 30, 31, 0, 1, 32, 33, 34, 2, 3, 4, 35, 5, 6, 36, 7, 37, 8, 9, 38, 10, 11, 39, 40, 12, 41, 42, 13, 14, 43, 15, 16, 44, 17, 45, 18, 19, 46, 20, 21, 22, 47, 48, 49, 23, 24][i.val]!
  if j<25 then .inl (Fin.ofNat 25 j) else .inr (Fin.ofNat 25 (j-25))

def indexing : (Fin 25 ⊕ Fin 25) ≃ Fin 50 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 25,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*49)*(49-1)^24) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 24 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 24 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 24=(2*49)*(49-1)^24 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquaresOpposite


namespace SplitNonsquaresOpposite
def rawWords (i : ℕ) : ℕ := #[4111936, 7599296, 15551424, 16035264, 13366144, 10444544, 5714447, 12084766, 5166140, 12898549, 6631851, 12181549, 10585971, 9309403, 3541942, 7609115, 13376630, 12083571, 124781, 6498741, 12765419, 711823, 1673054, 1260220, 0][i]!
def words (i : Fin 25) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 49]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 25 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 25 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 25, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 25, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(552:ℤ) := by
  change cubicInteger (fun i : Fin 25 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(552:ℤ) ∧
    87*(25:ℤ)^3+375*25*(4*25-3)+1000*((wordMatrix words-1)^3).trace-
      1110*49*(25-1)=(1515390:ℤ) ∧ 0≤(1515390:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 25 ⊕ Fin 25 → Fin 50
  | .inl i => Fin.ofNat 50 (#[1, 2, 3, 4, 5, 6, 9, 10, 11, 15, 18, 20, 23, 26, 27, 29, 30, 33, 36, 38, 41, 45, 46, 47, 49][i.val]!)
  | .inr i => Fin.ofNat 50 (#[0, 7, 8, 12, 13, 14, 16, 17, 19, 21, 22, 24, 25, 28, 31, 32, 34, 35, 37, 39, 40, 42, 43, 44, 48][i.val]!)

def pointPosition (i : Fin 50) : Fin 25 ⊕ Fin 25 :=
  let j : ℕ := #[25, 0, 1, 2, 3, 4, 5, 26, 27, 6, 7, 8, 28, 29, 30, 9, 31, 32, 10, 33, 11, 34, 35, 12, 36, 37, 13, 14, 38, 15, 16, 39, 40, 17, 41, 42, 18, 43, 19, 44, 45, 20, 46, 47, 48, 21, 22, 23, 49, 24][i.val]!
  if j<25 then .inl (Fin.ofNat 25 j) else .inr (Fin.ofNat 25 (j-25))

def indexing : (Fin 25 ⊕ Fin 25) ≃ Fin 50 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 25,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*49)*(49-1)^24) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 24 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 24 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 24=(2*49)*(49-1)^24 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquaresOpposite


namespace NonsplitNegativeOpposite
def rawWords (i : ℕ) : ℕ := #[3914908, 13301488, 15883697, 7189617, 5681679, 14501390, 7573002, 11311111, 11235332, 11870322, 10100847, 6578373, 8896927, 13504283, 5773606, 15732955, 3281769, 12662103, 4209336, 4220331, 8504949, 12684237, 3074174, 3323814, 0][i]!
def words (i : Fin 25) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 25 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 25 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 25, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 25, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(0:ℤ) := by
  change cubicInteger (fun i : Fin 25 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(0:ℤ) ∧
    87*(25:ℤ)^3+375*25*(4*25-3)+1000*((wordMatrix words-1)^3).trace-
      1110*49*(25-1)=(963390:ℤ) ∧ 0≤(963390:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 25 ⊕ Fin 25 → Fin 50
  | .inl i => Fin.ofNat 50 (#[2, 5, 7, 9, 14, 15, 17, 19, 20, 22, 23, 24, 26, 30, 32, 33, 34, 35, 36, 37, 39, 41, 42, 47, 49][i.val]!)
  | .inr i => Fin.ofNat 50 (#[0, 1, 3, 4, 6, 8, 10, 11, 12, 13, 16, 18, 21, 25, 27, 28, 29, 31, 38, 40, 43, 44, 45, 46, 48][i.val]!)

def pointPosition (i : Fin 50) : Fin 25 ⊕ Fin 25 :=
  let j : ℕ := #[25, 26, 0, 27, 28, 1, 29, 2, 30, 3, 31, 32, 33, 34, 4, 5, 35, 6, 36, 7, 8, 37, 9, 10, 11, 38, 12, 39, 40, 41, 13, 42, 14, 15, 16, 17, 18, 19, 43, 20, 44, 21, 22, 45, 46, 47, 48, 23, 49, 24][i.val]!
  if j<25 then .inl (Fin.ofNat 25 j) else .inr (Fin.ofNat 25 (j-25))

def indexing : (Fin 25 ⊕ Fin 25) ≃ Fin 50 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 25,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*49)*(49-1)^24) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 24 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 24 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 24=(2*49)*(49-1)^24 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegativeOpposite

end PaleyBits49
