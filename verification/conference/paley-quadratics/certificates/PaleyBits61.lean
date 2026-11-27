import Quantum.Hadamard.ConferenceBitCompletion
open Hadamard.BitTrace Hadamard.DeterminantRatio Matrix
set_option maxHeartbeats 12000000
set_option maxRecDepth 60000
namespace PaleyBits61

def rawFull (i : ℕ) : ℕ := #[642916798280633796, 1285833596561267592, 265824183908841233, 531648367817682466, 1063296735635364932, 2126593471270729864, 1947343933327765777, 1588844857441837603, 871846705669981255, 1743693411339962510, 1181543813466231069, 57244617718768187, 114489235437536374, 228978470875072748, 457956941750145496, 915913883500290992, 1831827767000581984, 1357812524787470017, 409782040361246083, 819564080722492166, 1639128161444984332, 972413313676274713, 1944826627352549426, 1583810245491404901, 861777481769115851, 1723554963538231702, 1141266917862769453, 2282533835725538906, 2259224662237383861, 2212606315261073771, 2119369621308453591, 1932896233403213231, 1559949457592732511, 814055905971771071, 1628111811943542142, 950380614673390333, 1900761229346780666, 1495679449479867381, 685515889746040811, 1371031779492081622, 436220549770469293, 872441099540938586, 1744882199081877172, 1183921388950060393, 61999768686426835, 123999537372853670, 247999074745707340, 495998149491414680, 991996298982829360, 1983992597965658720, 1662142186717623489, 1018441364221553027, 2036882728443106054, 1767922447672518157, 1230001886131342363, 154160763048990775, 308321526097981550, 616643052195963100, 1233286104391926200, 160729199570158449, 321458399140316898, 0][i]!
def fullRows (i : Fin 62) : ℕ := rawFull i.val

private theorem fullSymmetric : (wordMatrix fullRows).IsSymm := by
  have h : ∀ i j : Fin 62, sign (fullRows i) j.val=sign (fullRows j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem fullDiagonal : ∀ i : Fin 62, sign (fullRows i) i.val=1 := by decide +kernel
private theorem lower0 : (lowerRow 62 rawFull) 0=true := by decide +kernel
private theorem lower1 : (lowerRow 62 rawFull) 1=true := by decide +kernel
private theorem lower2 : (lowerRow 62 rawFull) 2=true := by decide +kernel
private theorem lower3 : (lowerRow 62 rawFull) 3=true := by decide +kernel
private theorem lower4 : (lowerRow 62 rawFull) 4=true := by decide +kernel
private theorem lower5 : (lowerRow 62 rawFull) 5=true := by decide +kernel
private theorem lower6 : (lowerRow 62 rawFull) 6=true := by decide +kernel
private theorem lower7 : (lowerRow 62 rawFull) 7=true := by decide +kernel
private theorem lower8 : (lowerRow 62 rawFull) 8=true := by decide +kernel
private theorem lower9 : (lowerRow 62 rawFull) 9=true := by decide +kernel
private theorem lower10 : (lowerRow 62 rawFull) 10=true := by decide +kernel
private theorem lower11 : (lowerRow 62 rawFull) 11=true := by decide +kernel
private theorem lower12 : (lowerRow 62 rawFull) 12=true := by decide +kernel
private theorem lower13 : (lowerRow 62 rawFull) 13=true := by decide +kernel
private theorem lower14 : (lowerRow 62 rawFull) 14=true := by decide +kernel
private theorem lower15 : (lowerRow 62 rawFull) 15=true := by decide +kernel
private theorem lower16 : (lowerRow 62 rawFull) 16=true := by decide +kernel
private theorem lower17 : (lowerRow 62 rawFull) 17=true := by decide +kernel
private theorem lower18 : (lowerRow 62 rawFull) 18=true := by decide +kernel
private theorem lower19 : (lowerRow 62 rawFull) 19=true := by decide +kernel
private theorem lower20 : (lowerRow 62 rawFull) 20=true := by decide +kernel
private theorem lower21 : (lowerRow 62 rawFull) 21=true := by decide +kernel
private theorem lower22 : (lowerRow 62 rawFull) 22=true := by decide +kernel
private theorem lower23 : (lowerRow 62 rawFull) 23=true := by decide +kernel
private theorem lower24 : (lowerRow 62 rawFull) 24=true := by decide +kernel
private theorem lower25 : (lowerRow 62 rawFull) 25=true := by decide +kernel
private theorem lower26 : (lowerRow 62 rawFull) 26=true := by decide +kernel
private theorem lower27 : (lowerRow 62 rawFull) 27=true := by decide +kernel
private theorem lower28 : (lowerRow 62 rawFull) 28=true := by decide +kernel
private theorem lower29 : (lowerRow 62 rawFull) 29=true := by decide +kernel
private theorem lower30 : (lowerRow 62 rawFull) 30=true := by decide +kernel
private theorem lower31 : (lowerRow 62 rawFull) 31=true := by decide +kernel
private theorem lower32 : (lowerRow 62 rawFull) 32=true := by decide +kernel
private theorem lower33 : (lowerRow 62 rawFull) 33=true := by decide +kernel
private theorem lower34 : (lowerRow 62 rawFull) 34=true := by decide +kernel
private theorem lower35 : (lowerRow 62 rawFull) 35=true := by decide +kernel
private theorem lower36 : (lowerRow 62 rawFull) 36=true := by decide +kernel
private theorem lower37 : (lowerRow 62 rawFull) 37=true := by decide +kernel
private theorem lower38 : (lowerRow 62 rawFull) 38=true := by decide +kernel
private theorem lower39 : (lowerRow 62 rawFull) 39=true := by decide +kernel
private theorem lower40 : (lowerRow 62 rawFull) 40=true := by decide +kernel
private theorem lower41 : (lowerRow 62 rawFull) 41=true := by decide +kernel
private theorem lower42 : (lowerRow 62 rawFull) 42=true := by decide +kernel
private theorem lower43 : (lowerRow 62 rawFull) 43=true := by decide +kernel
private theorem lower44 : (lowerRow 62 rawFull) 44=true := by decide +kernel
private theorem lower45 : (lowerRow 62 rawFull) 45=true := by decide +kernel
private theorem lower46 : (lowerRow 62 rawFull) 46=true := by decide +kernel
private theorem lower47 : (lowerRow 62 rawFull) 47=true := by decide +kernel
private theorem lower48 : (lowerRow 62 rawFull) 48=true := by decide +kernel
private theorem lower49 : (lowerRow 62 rawFull) 49=true := by decide +kernel
private theorem lower50 : (lowerRow 62 rawFull) 50=true := by decide +kernel
private theorem lower51 : (lowerRow 62 rawFull) 51=true := by decide +kernel
private theorem lower52 : (lowerRow 62 rawFull) 52=true := by decide +kernel
private theorem lower53 : (lowerRow 62 rawFull) 53=true := by decide +kernel
private theorem lower54 : (lowerRow 62 rawFull) 54=true := by decide +kernel
private theorem lower55 : (lowerRow 62 rawFull) 55=true := by decide +kernel
private theorem lower56 : (lowerRow 62 rawFull) 56=true := by decide +kernel
private theorem lower57 : (lowerRow 62 rawFull) 57=true := by decide +kernel
private theorem lower58 : (lowerRow 62 rawFull) 58=true := by decide +kernel
private theorem lower59 : (lowerRow 62 rawFull) 59=true := by decide +kernel
private theorem lower60 : (lowerRow 62 rawFull) 60=true := by decide +kernel
private theorem lower61 : (lowerRow 62 rawFull) 61=true := by decide +kernel
private theorem lowerChecked : allBelow 62 (lowerRow 62 rawFull)=true := by
  have h : allBelow 0 (lowerRow 62 rawFull)=true := rfl
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
  have h := allBelow_step h lower54
  have h := allBelow_step h lower55
  have h := allBelow_step h lower56
  have h := allBelow_step h lower57
  have h := allBelow_step h lower58
  have h := allBelow_step h lower59
  have h := allBelow_step h lower60
  have h := allBelow_step h lower61
  exact h

private theorem fullPairs : ∀ i j : Fin 62, i≠j →
    correlation 62 (fullRows i) (fullRows j)=2*sign (fullRows i) j.val :=
  correlations_of_lower rawFull fullSymmetric lowerChecked


namespace SplitSquares
def rawWords (i : ℕ) : ℕ := #[0, 1278208100, 952865202, 832561984, 1798514372, 1188863494, 247085338, 427760148, 921728076, 636379320, 1274388784, 531808482, 2001248740, 1432622938, 2069007114, 2032229422, 1949992094, 1355893470, 1525163690, 663032558, 1191398904, 210087890, 486963108, 841879404, 676920984, 1486642544, 1618557794, 593808598, 46659980, 1300878108, 639104050][i]!
def words (i : Fin 31) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[61, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 31 rawWords i=rowTotals i)

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
private theorem row27 : rowAgrees 27=true := by decide +kernel
private theorem row28 : rowAgrees 28=true := by decide +kernel
private theorem row29 : rowAgrees 29=true := by decide +kernel
private theorem row30 : rowAgrees 30=true := by decide +kernel
private theorem rowChecked : allBelow 31 rowAgrees=true := by
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
  have h := allBelow_step h row27
  have h := allBelow_step h row28
  have h := allBelow_step h row29
  have h := allBelow_step h row30
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 31, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 31, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-210:ℤ) := by
  change cubicInteger (fun i : Fin 31 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-210:ℤ) ∧
    87*(31:ℤ)^3+375*31*(4*31-3)+1000*((wordMatrix words-1)^3).trace-
      1110*61*(31-1)=(1757142:ℤ) ∧ 0≤(1757142:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 31 ⊕ Fin 31 → Fin 62
  | .inl i => Fin.ofNat 62 (#[0, 1, 3, 4, 5, 9, 12, 13, 14, 15, 16, 19, 20, 22, 25, 27, 34, 36, 39, 41, 42, 45, 46, 47, 48, 49, 52, 56, 57, 58, 60][i.val]!)
  | .inr i => Fin.ofNat 62 (#[2, 6, 7, 8, 10, 11, 17, 18, 21, 23, 24, 26, 28, 29, 30, 31, 32, 33, 35, 37, 38, 40, 43, 44, 50, 51, 53, 54, 55, 59, 61][i.val]!)

def pointPosition (i : Fin 62) : Fin 31 ⊕ Fin 31 :=
  let j : ℕ := #[0, 1, 31, 2, 3, 4, 32, 33, 34, 5, 35, 36, 6, 7, 8, 9, 10, 37, 38, 11, 12, 39, 13, 40, 41, 14, 42, 15, 43, 44, 45, 46, 47, 48, 16, 49, 17, 50, 51, 18, 52, 19, 20, 53, 54, 21, 22, 23, 24, 25, 55, 56, 26, 57, 58, 59, 27, 28, 29, 60, 30, 61][i.val]!
  if j<31 then .inl (Fin.ofNat 31 j) else .inr (Fin.ofNat 31 (j-31))

def indexing : (Fin 31 ⊕ Fin 31) ≃ Fin 62 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 31,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*61)*(61-1)^30) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 30 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 30 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 30=(2*61)*(61-1)^30 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquares


namespace SplitNonsquares
def rawWords (i : ℕ) : ℕ := #[2147483646, 677360689, 1136315537, 125675905, 1156796711, 451224467, 903504769, 854076525, 789084281, 1596154977, 1027981959, 2047578509, 1939220755, 1411945451, 1784219477, 1550986255, 1882476091, 719362647, 1472795691, 1217685967, 831115359, 1631822525, 103204091, 505286901, 909383501, 29776813, 1237624665, 1686818595, 26590945, 154361283, 204339733][i]!
def words (i : Fin 31) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[121, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 31 rawWords i=rowTotals i)

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
private theorem row27 : rowAgrees 27=true := by decide +kernel
private theorem row28 : rowAgrees 28=true := by decide +kernel
private theorem row29 : rowAgrees 29=true := by decide +kernel
private theorem row30 : rowAgrees 30=true := by decide +kernel
private theorem rowChecked : allBelow 31 rowAgrees=true := by
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
  have h := allBelow_step h row27
  have h := allBelow_step h row28
  have h := allBelow_step h row29
  have h := allBelow_step h row30
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 31, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 31, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(210:ℤ) := by
  change cubicInteger (fun i : Fin 31 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(210:ℤ) ∧
    87*(31:ℤ)^3+375*31*(4*31-3)+1000*((wordMatrix words-1)^3).trace-
      1110*61*(31-1)=(2177142:ℤ) ∧ 0≤(2177142:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 31 ⊕ Fin 31 → Fin 62
  | .inl i => Fin.ofNat 62 (#[0, 2, 6, 7, 8, 10, 11, 17, 18, 21, 23, 24, 26, 28, 29, 30, 31, 32, 33, 35, 37, 38, 40, 43, 44, 50, 51, 53, 54, 55, 59][i.val]!)
  | .inr i => Fin.ofNat 62 (#[1, 3, 4, 5, 9, 12, 13, 14, 15, 16, 19, 20, 22, 25, 27, 34, 36, 39, 41, 42, 45, 46, 47, 48, 49, 52, 56, 57, 58, 60, 61][i.val]!)

def pointPosition (i : Fin 62) : Fin 31 ⊕ Fin 31 :=
  let j : ℕ := #[0, 31, 1, 32, 33, 34, 2, 3, 4, 35, 5, 6, 36, 37, 38, 39, 40, 7, 8, 41, 42, 9, 43, 10, 11, 44, 12, 45, 13, 14, 15, 16, 17, 18, 46, 19, 47, 20, 21, 48, 22, 49, 50, 23, 24, 51, 52, 53, 54, 55, 25, 26, 56, 27, 28, 29, 57, 58, 59, 30, 60, 61][i.val]!
  if j<31 then .inl (Fin.ofNat 31 j) else .inr (Fin.ofNat 31 (j-31))

def indexing : (Fin 31 ⊕ Fin 31) ≃ Fin 62 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 31,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*61)*(61-1)^30) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 30 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 30 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 30=(2*61)*(61-1)^30 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquares


namespace NonsplitNegative
def rawWords (i : ℕ) : ℕ := #[1147389474, 429381681, 858460280, 1890804100, 1264491398, 46094087, 804335876, 1810768408, 1473651832, 195578033, 928796961, 1588625938, 761914486, 1302778312, 2105849387, 1980266515, 1209929839, 1416438207, 327902642, 1848088244, 1212222842, 76167917, 219289041, 505703402, 407140310, 546082804, 1626012993, 1641642706, 562482446, 503895244, 203155865][i]!
def words (i : Fin 31) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 31 rawWords i=rowTotals i)

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
private theorem row27 : rowAgrees 27=true := by decide +kernel
private theorem row28 : rowAgrees 28=true := by decide +kernel
private theorem row29 : rowAgrees 29=true := by decide +kernel
private theorem row30 : rowAgrees 30=true := by decide +kernel
private theorem rowChecked : allBelow 31 rowAgrees=true := by
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
  have h := allBelow_step h row27
  have h := allBelow_step h row28
  have h := allBelow_step h row29
  have h := allBelow_step h row30
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 31, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 31, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-930:ℤ) := by
  change cubicInteger (fun i : Fin 31 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-930:ℤ) ∧
    87*(31:ℤ)^3+375*31*(4*31-3)+1000*((wordMatrix words-1)^3).trace-
      1110*61*(31-1)=(1037142:ℤ) ∧ 0≤(1037142:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 31 ⊕ Fin 31 → Fin 62
  | .inl i => Fin.ofNat 62 (#[0, 2, 3, 5, 9, 10, 14, 15, 16, 17, 18, 19, 20, 22, 28, 30, 31, 33, 39, 41, 42, 43, 44, 45, 46, 47, 51, 52, 56, 58, 59][i.val]!)
  | .inr i => Fin.ofNat 62 (#[1, 4, 6, 7, 8, 11, 12, 13, 21, 23, 24, 25, 26, 27, 29, 32, 34, 35, 36, 37, 38, 40, 48, 49, 50, 53, 54, 55, 57, 60, 61][i.val]!)

def pointPosition (i : Fin 62) : Fin 31 ⊕ Fin 31 :=
  let j : ℕ := #[0, 31, 1, 2, 32, 3, 33, 34, 35, 4, 5, 36, 37, 38, 6, 7, 8, 9, 10, 11, 12, 39, 13, 40, 41, 42, 43, 44, 14, 45, 15, 16, 46, 17, 47, 48, 49, 50, 51, 18, 52, 19, 20, 21, 22, 23, 24, 25, 53, 54, 55, 26, 27, 56, 57, 58, 28, 59, 29, 30, 60, 61][i.val]!
  if j<31 then .inl (Fin.ofNat 31 j) else .inr (Fin.ofNat 31 (j-31))

def indexing : (Fin 31 ⊕ Fin 31) ≃ Fin 62 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 31,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*61)*(61-1)^30) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 30 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 30 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 30=(2*61)*(61-1)^30 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegative


namespace SplitSquaresOpposite
def rawWords (i : ℕ) : ℕ := #[338680344, 568157768, 62837952, 578398355, 225612233, 451752384, 427038262, 394542140, 798077488, 513990979, 1023789254, 969610377, 705972725, 892109738, 775493127, 941238045, 359681323, 736397845, 608842983, 415557679, 815911262, 51602045, 252643450, 454691750, 14888406, 618812332, 843409297, 13295472, 77180641, 102169866, 0][i]!
def words (i : Fin 31) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 121]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 31 rawWords i=rowTotals i)

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
private theorem row27 : rowAgrees 27=true := by decide +kernel
private theorem row28 : rowAgrees 28=true := by decide +kernel
private theorem row29 : rowAgrees 29=true := by decide +kernel
private theorem row30 : rowAgrees 30=true := by decide +kernel
private theorem rowChecked : allBelow 31 rowAgrees=true := by
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
  have h := allBelow_step h row27
  have h := allBelow_step h row28
  have h := allBelow_step h row29
  have h := allBelow_step h row30
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 31, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 31, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(210:ℤ) := by
  change cubicInteger (fun i : Fin 31 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(210:ℤ) ∧
    87*(31:ℤ)^3+375*31*(4*31-3)+1000*((wordMatrix words-1)^3).trace-
      1110*61*(31-1)=(2177142:ℤ) ∧ 0≤(2177142:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 31 ⊕ Fin 31 → Fin 62
  | .inl i => Fin.ofNat 62 (#[2, 6, 7, 8, 10, 11, 17, 18, 21, 23, 24, 26, 28, 29, 30, 31, 32, 33, 35, 37, 38, 40, 43, 44, 50, 51, 53, 54, 55, 59, 61][i.val]!)
  | .inr i => Fin.ofNat 62 (#[0, 1, 3, 4, 5, 9, 12, 13, 14, 15, 16, 19, 20, 22, 25, 27, 34, 36, 39, 41, 42, 45, 46, 47, 48, 49, 52, 56, 57, 58, 60][i.val]!)

def pointPosition (i : Fin 62) : Fin 31 ⊕ Fin 31 :=
  let j : ℕ := #[31, 32, 0, 33, 34, 35, 1, 2, 3, 36, 4, 5, 37, 38, 39, 40, 41, 6, 7, 42, 43, 8, 44, 9, 10, 45, 11, 46, 12, 13, 14, 15, 16, 17, 47, 18, 48, 19, 20, 49, 21, 50, 51, 22, 23, 52, 53, 54, 55, 56, 24, 25, 57, 26, 27, 28, 58, 59, 60, 29, 61, 30][i.val]!
  if j<31 then .inl (Fin.ofNat 31 j) else .inr (Fin.ofNat 31 (j-31))

def indexing : (Fin 31 ⊕ Fin 31) ≃ Fin 62 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 31,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*61)*(61-1)^30) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 30 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 30 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 30=(2*61)*(61-1)^30 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquaresOpposite


namespace SplitNonsquaresOpposite
def rawWords (i : ℕ) : ℕ := #[639104050, 476432601, 416280992, 899257186, 594431747, 123542669, 213880074, 460864038, 318189660, 637194392, 265904241, 1000624370, 716311469, 1034503557, 1016114711, 974996047, 677946735, 762581845, 331516279, 595699452, 105043945, 243481554, 420939702, 338460492, 743321272, 809278897, 296904299, 23329990, 650439054, 319552025, 0][i]!
def words (i : Fin 31) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 61]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 31 rawWords i=rowTotals i)

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
private theorem row27 : rowAgrees 27=true := by decide +kernel
private theorem row28 : rowAgrees 28=true := by decide +kernel
private theorem row29 : rowAgrees 29=true := by decide +kernel
private theorem row30 : rowAgrees 30=true := by decide +kernel
private theorem rowChecked : allBelow 31 rowAgrees=true := by
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
  have h := allBelow_step h row27
  have h := allBelow_step h row28
  have h := allBelow_step h row29
  have h := allBelow_step h row30
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 31, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 31, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-210:ℤ) := by
  change cubicInteger (fun i : Fin 31 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-210:ℤ) ∧
    87*(31:ℤ)^3+375*31*(4*31-3)+1000*((wordMatrix words-1)^3).trace-
      1110*61*(31-1)=(1757142:ℤ) ∧ 0≤(1757142:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 31 ⊕ Fin 31 → Fin 62
  | .inl i => Fin.ofNat 62 (#[1, 3, 4, 5, 9, 12, 13, 14, 15, 16, 19, 20, 22, 25, 27, 34, 36, 39, 41, 42, 45, 46, 47, 48, 49, 52, 56, 57, 58, 60, 61][i.val]!)
  | .inr i => Fin.ofNat 62 (#[0, 2, 6, 7, 8, 10, 11, 17, 18, 21, 23, 24, 26, 28, 29, 30, 31, 32, 33, 35, 37, 38, 40, 43, 44, 50, 51, 53, 54, 55, 59][i.val]!)

def pointPosition (i : Fin 62) : Fin 31 ⊕ Fin 31 :=
  let j : ℕ := #[31, 0, 32, 1, 2, 3, 33, 34, 35, 4, 36, 37, 5, 6, 7, 8, 9, 38, 39, 10, 11, 40, 12, 41, 42, 13, 43, 14, 44, 45, 46, 47, 48, 49, 15, 50, 16, 51, 52, 17, 53, 18, 19, 54, 55, 20, 21, 22, 23, 24, 56, 57, 25, 58, 59, 60, 26, 27, 28, 61, 29, 30][i.val]!
  if j<31 then .inl (Fin.ofNat 31 j) else .inr (Fin.ofNat 31 (j-31))

def indexing : (Fin 31 ⊕ Fin 31) ≃ Fin 62 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 31,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*61)*(61-1)^30) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 30 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 30 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 30=(2*61)*(61-1)^30 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquaresOpposite


namespace NonsplitNegativeOpposite
def rawWords (i : ℕ) : ℕ := #[739634296, 474982756, 832562898, 826150017, 8247301, 216777091, 162939399, 323815212, 126935714, 782322116, 524521613, 1053205019, 495813648, 995838215, 992879477, 733027639, 941930167, 34106478, 907106527, 742551742, 149201245, 290570872, 221785266, 940612452, 811660748, 671543168, 541859619, 316276323, 161840270, 126741005, 0][i]!
def words (i : Fin 31) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 31 rawWords i=rowTotals i)

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
private theorem row27 : rowAgrees 27=true := by decide +kernel
private theorem row28 : rowAgrees 28=true := by decide +kernel
private theorem row29 : rowAgrees 29=true := by decide +kernel
private theorem row30 : rowAgrees 30=true := by decide +kernel
private theorem rowChecked : allBelow 31 rowAgrees=true := by
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
  have h := allBelow_step h row27
  have h := allBelow_step h row28
  have h := allBelow_step h row29
  have h := allBelow_step h row30
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 31, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 31, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(930:ℤ) := by
  change cubicInteger (fun i : Fin 31 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(930:ℤ) ∧
    87*(31:ℤ)^3+375*31*(4*31-3)+1000*((wordMatrix words-1)^3).trace-
      1110*61*(31-1)=(2897142:ℤ) ∧ 0≤(2897142:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 31 ⊕ Fin 31 → Fin 62
  | .inl i => Fin.ofNat 62 (#[1, 4, 6, 7, 8, 11, 12, 13, 21, 23, 24, 25, 26, 27, 29, 32, 34, 35, 36, 37, 38, 40, 48, 49, 50, 53, 54, 55, 57, 60, 61][i.val]!)
  | .inr i => Fin.ofNat 62 (#[0, 2, 3, 5, 9, 10, 14, 15, 16, 17, 18, 19, 20, 22, 28, 30, 31, 33, 39, 41, 42, 43, 44, 45, 46, 47, 51, 52, 56, 58, 59][i.val]!)

def pointPosition (i : Fin 62) : Fin 31 ⊕ Fin 31 :=
  let j : ℕ := #[31, 0, 32, 33, 1, 34, 2, 3, 4, 35, 36, 5, 6, 7, 37, 38, 39, 40, 41, 42, 43, 8, 44, 9, 10, 11, 12, 13, 45, 14, 46, 47, 15, 48, 16, 17, 18, 19, 20, 49, 21, 50, 51, 52, 53, 54, 55, 56, 22, 23, 24, 57, 58, 25, 26, 27, 59, 28, 60, 61, 29, 30][i.val]!
  if j<31 then .inl (Fin.ofNat 31 j) else .inr (Fin.ofNat 31 (j-31))

def indexing : (Fin 31 ⊕ Fin 31) ≃ Fin 62 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 31,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*61)*(61-1)^30) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 30 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 30 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 30=(2*61)*(61-1)^30 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegativeOpposite

end PaleyBits61
