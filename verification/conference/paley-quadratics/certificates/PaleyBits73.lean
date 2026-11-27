import Quantum.Hadamard.ConferenceBitCompletion
open Hadamard.BitTrace Hadamard.DeterminantRatio Matrix
set_option maxHeartbeats 12000000
set_option maxRecDepth 60000
namespace PaleyBits73

def rawFull (i : ℕ) : ℕ := #[384875580742593342624, 769751161485186685248, 1539502322970373370496, 3079004645940746740992, 6158009291881493481984, 2871285618023696536577, 5742571236047393073154, 2040409506355495718917, 4080819012710991437834, 8161638025421982875668, 6878543085104675323945, 4312353204470060220499, 8624706408940120440998, 7804679852140950454605, 6164626738542610481819, 2884520511345930536247, 5769041022691861072494, 2093349079644431717597, 4186698159288863435194, 8373396318577726870388, 7302059671416163313385, 5159386377093036199379, 874039788446781971367, 1748079576893563942734, 3496159153787127885468, 6992318307574255770936, 4539903649409221114481, 9079807298818442228962, 8714881631897594030533, 7985030298055897633675, 6525327630372504839959, 3605922295005719252527, 7211844590011438505054, 4978956214283586582717, 513179462827882738043, 1026358925655765476086, 2052717851311530952172, 4105435702623061904344, 8210871405246123808688, 6977009844752957189985, 4509286723766623952579, 9018573447533247905158, 8592413929327205382925, 7740094892915120338459, 6035456820090950249527, 2626180674442610071663, 5252361348885220143326, 1059989732031149859261, 2119979464062299718522, 4239958928124599437044, 8479917856249198874088, 7515102746759107320785, 5585472527778924214179, 1726212089818558000967, 3452424179637116001934, 6904848359274232003868, 4364963752809173580345, 8729927505618347160690, 8015122045497403893989, 6585511125255517360587, 3726289284771744293783, 7452578569543488587566, 5460424173347686747741, 1476115380956083068091, 2952230761912166136182, 5904461523824332272364, 2364190081909374117337, 4728380163818748234674, 12027361898206041957, 24054723796412083914, 48109447592824167828, 96218895185648335656, 192437790371296671312, 0][i]!
def fullRows (i : Fin 74) : ℕ := rawFull i.val

private theorem fullSymmetric : (wordMatrix fullRows).IsSymm := by
  have h : ∀ i j : Fin 74, sign (fullRows i) j.val=sign (fullRows j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem fullDiagonal : ∀ i : Fin 74, sign (fullRows i) i.val=1 := by decide +kernel
private theorem lower0 : (lowerRow 74 rawFull) 0=true := by decide +kernel
private theorem lower1 : (lowerRow 74 rawFull) 1=true := by decide +kernel
private theorem lower2 : (lowerRow 74 rawFull) 2=true := by decide +kernel
private theorem lower3 : (lowerRow 74 rawFull) 3=true := by decide +kernel
private theorem lower4 : (lowerRow 74 rawFull) 4=true := by decide +kernel
private theorem lower5 : (lowerRow 74 rawFull) 5=true := by decide +kernel
private theorem lower6 : (lowerRow 74 rawFull) 6=true := by decide +kernel
private theorem lower7 : (lowerRow 74 rawFull) 7=true := by decide +kernel
private theorem lower8 : (lowerRow 74 rawFull) 8=true := by decide +kernel
private theorem lower9 : (lowerRow 74 rawFull) 9=true := by decide +kernel
private theorem lower10 : (lowerRow 74 rawFull) 10=true := by decide +kernel
private theorem lower11 : (lowerRow 74 rawFull) 11=true := by decide +kernel
private theorem lower12 : (lowerRow 74 rawFull) 12=true := by decide +kernel
private theorem lower13 : (lowerRow 74 rawFull) 13=true := by decide +kernel
private theorem lower14 : (lowerRow 74 rawFull) 14=true := by decide +kernel
private theorem lower15 : (lowerRow 74 rawFull) 15=true := by decide +kernel
private theorem lower16 : (lowerRow 74 rawFull) 16=true := by decide +kernel
private theorem lower17 : (lowerRow 74 rawFull) 17=true := by decide +kernel
private theorem lower18 : (lowerRow 74 rawFull) 18=true := by decide +kernel
private theorem lower19 : (lowerRow 74 rawFull) 19=true := by decide +kernel
private theorem lower20 : (lowerRow 74 rawFull) 20=true := by decide +kernel
private theorem lower21 : (lowerRow 74 rawFull) 21=true := by decide +kernel
private theorem lower22 : (lowerRow 74 rawFull) 22=true := by decide +kernel
private theorem lower23 : (lowerRow 74 rawFull) 23=true := by decide +kernel
private theorem lower24 : (lowerRow 74 rawFull) 24=true := by decide +kernel
private theorem lower25 : (lowerRow 74 rawFull) 25=true := by decide +kernel
private theorem lower26 : (lowerRow 74 rawFull) 26=true := by decide +kernel
private theorem lower27 : (lowerRow 74 rawFull) 27=true := by decide +kernel
private theorem lower28 : (lowerRow 74 rawFull) 28=true := by decide +kernel
private theorem lower29 : (lowerRow 74 rawFull) 29=true := by decide +kernel
private theorem lower30 : (lowerRow 74 rawFull) 30=true := by decide +kernel
private theorem lower31 : (lowerRow 74 rawFull) 31=true := by decide +kernel
private theorem lower32 : (lowerRow 74 rawFull) 32=true := by decide +kernel
private theorem lower33 : (lowerRow 74 rawFull) 33=true := by decide +kernel
private theorem lower34 : (lowerRow 74 rawFull) 34=true := by decide +kernel
private theorem lower35 : (lowerRow 74 rawFull) 35=true := by decide +kernel
private theorem lower36 : (lowerRow 74 rawFull) 36=true := by decide +kernel
private theorem lower37 : (lowerRow 74 rawFull) 37=true := by decide +kernel
private theorem lower38 : (lowerRow 74 rawFull) 38=true := by decide +kernel
private theorem lower39 : (lowerRow 74 rawFull) 39=true := by decide +kernel
private theorem lower40 : (lowerRow 74 rawFull) 40=true := by decide +kernel
private theorem lower41 : (lowerRow 74 rawFull) 41=true := by decide +kernel
private theorem lower42 : (lowerRow 74 rawFull) 42=true := by decide +kernel
private theorem lower43 : (lowerRow 74 rawFull) 43=true := by decide +kernel
private theorem lower44 : (lowerRow 74 rawFull) 44=true := by decide +kernel
private theorem lower45 : (lowerRow 74 rawFull) 45=true := by decide +kernel
private theorem lower46 : (lowerRow 74 rawFull) 46=true := by decide +kernel
private theorem lower47 : (lowerRow 74 rawFull) 47=true := by decide +kernel
private theorem lower48 : (lowerRow 74 rawFull) 48=true := by decide +kernel
private theorem lower49 : (lowerRow 74 rawFull) 49=true := by decide +kernel
private theorem lower50 : (lowerRow 74 rawFull) 50=true := by decide +kernel
private theorem lower51 : (lowerRow 74 rawFull) 51=true := by decide +kernel
private theorem lower52 : (lowerRow 74 rawFull) 52=true := by decide +kernel
private theorem lower53 : (lowerRow 74 rawFull) 53=true := by decide +kernel
private theorem lower54 : (lowerRow 74 rawFull) 54=true := by decide +kernel
private theorem lower55 : (lowerRow 74 rawFull) 55=true := by decide +kernel
private theorem lower56 : (lowerRow 74 rawFull) 56=true := by decide +kernel
private theorem lower57 : (lowerRow 74 rawFull) 57=true := by decide +kernel
private theorem lower58 : (lowerRow 74 rawFull) 58=true := by decide +kernel
private theorem lower59 : (lowerRow 74 rawFull) 59=true := by decide +kernel
private theorem lower60 : (lowerRow 74 rawFull) 60=true := by decide +kernel
private theorem lower61 : (lowerRow 74 rawFull) 61=true := by decide +kernel
private theorem lower62 : (lowerRow 74 rawFull) 62=true := by decide +kernel
private theorem lower63 : (lowerRow 74 rawFull) 63=true := by decide +kernel
private theorem lower64 : (lowerRow 74 rawFull) 64=true := by decide +kernel
private theorem lower65 : (lowerRow 74 rawFull) 65=true := by decide +kernel
private theorem lower66 : (lowerRow 74 rawFull) 66=true := by decide +kernel
private theorem lower67 : (lowerRow 74 rawFull) 67=true := by decide +kernel
private theorem lower68 : (lowerRow 74 rawFull) 68=true := by decide +kernel
private theorem lower69 : (lowerRow 74 rawFull) 69=true := by decide +kernel
private theorem lower70 : (lowerRow 74 rawFull) 70=true := by decide +kernel
private theorem lower71 : (lowerRow 74 rawFull) 71=true := by decide +kernel
private theorem lower72 : (lowerRow 74 rawFull) 72=true := by decide +kernel
private theorem lower73 : (lowerRow 74 rawFull) 73=true := by decide +kernel
private theorem lowerChecked : allBelow 74 (lowerRow 74 rawFull)=true := by
  have h : allBelow 0 (lowerRow 74 rawFull)=true := rfl
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
  have h := allBelow_step h lower62
  have h := allBelow_step h lower63
  have h := allBelow_step h lower64
  have h := allBelow_step h lower65
  have h := allBelow_step h lower66
  have h := allBelow_step h lower67
  have h := allBelow_step h lower68
  have h := allBelow_step h lower69
  have h := allBelow_step h lower70
  have h := allBelow_step h lower71
  have h := allBelow_step h lower72
  have h := allBelow_step h lower73
  exact h

private theorem fullPairs : ∀ i j : Fin 74, i≠j →
    correlation 74 (fullRows i) (fullRows j)=2*sign (fullRows i) j.val :=
  correlations_of_lower rawFull fullSymmetric lowerChecked


namespace SplitSquares
def rawWords (i : ℕ) : ℕ := #[0, 14845974368, 21162834816, 45882373696, 91701865600, 80863009282, 57625304074, 118742465044, 123957532678, 82331865262, 63112958042, 121930850804, 23976478702, 48829696156, 102212502872, 134112412450, 105852226878, 12813624502, 33611078252, 58359657208, 117197305808, 133895072070, 73822332734, 28592213242, 61271940788, 128715729512, 51022229902, 96682042204, 125666506034, 103194791630, 43337017718, 86143620524, 69096764114, 1303832234, 2611797332, 2000268744, 7422987184][i]!
def words (i : Fin 37) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[73, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 37 rawWords i=rowTotals i)

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
private theorem row31 : rowAgrees 31=true := by decide +kernel
private theorem row32 : rowAgrees 32=true := by decide +kernel
private theorem row33 : rowAgrees 33=true := by decide +kernel
private theorem row34 : rowAgrees 34=true := by decide +kernel
private theorem row35 : rowAgrees 35=true := by decide +kernel
private theorem row36 : rowAgrees 36=true := by decide +kernel
private theorem rowChecked : allBelow 37 rowAgrees=true := by
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
  have h := allBelow_step h row31
  have h := allBelow_step h row32
  have h := allBelow_step h row33
  have h := allBelow_step h row34
  have h := allBelow_step h row35
  have h := allBelow_step h row36
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 37, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 37, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-1044:ℤ) := by
  change cubicInteger (fun i : Fin 37 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-1044:ℤ) ∧
    87*(37:ℤ)^3+375*37*(4*37-3)+1000*((wordMatrix words-1)^3).trace-
      1110*73*(37-1)=(2457606:ℤ) ∧ 0≤(2457606:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 37 ⊕ Fin 37 → Fin 74
  | .inl i => Fin.ofNat 74 (#[0, 1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 19, 23, 24, 25, 27, 32, 35, 36, 37, 38, 41, 46, 48, 49, 50, 54, 55, 57, 61, 64, 65, 67, 69, 70, 71, 72][i.val]!)
  | .inr i => Fin.ofNat 74 (#[5, 7, 10, 11, 13, 14, 15, 17, 20, 21, 22, 26, 28, 29, 30, 31, 33, 34, 39, 40, 42, 43, 44, 45, 47, 51, 52, 53, 56, 58, 59, 60, 62, 63, 66, 68, 73][i.val]!)

def pointPosition (i : Fin 74) : Fin 37 ⊕ Fin 37 :=
  let j : ℕ := #[0, 1, 2, 3, 4, 37, 5, 38, 6, 7, 39, 40, 8, 41, 42, 43, 9, 44, 10, 11, 45, 46, 47, 12, 13, 14, 48, 15, 49, 50, 51, 52, 16, 53, 54, 17, 18, 19, 20, 55, 56, 21, 57, 58, 59, 60, 22, 61, 23, 24, 25, 62, 63, 64, 26, 27, 65, 28, 66, 67, 68, 29, 69, 70, 30, 31, 71, 32, 72, 33, 34, 35, 36, 73][i.val]!
  if j<37 then .inl (Fin.ofNat 37 j) else .inr (Fin.ofNat 37 (j-37))

def indexing : (Fin 37 ⊕ Fin 37) ≃ Fin 74 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 37,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*73)*(73-1)^36) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 36 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 36 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 36=(2*73)*(73-1)^36 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquares


namespace SplitNonsquares
def rawWords (i : ℕ) : ℕ := #[137438953470, 87703886473, 59291889473, 129265928067, 27745008641, 40717169153, 38452683781, 119214766603, 84411262989, 32551436463, 124795564125, 43971658135, 110232274099, 81091233269, 102089099461, 25498223529, 15529416539, 62592662071, 99447490403, 76110133563, 116350177885, 97609936497, 23354080745, 37649107195, 51138372051, 82815915367, 113289580309, 62330084399, 125635857017, 51630618995, 86297862391, 34522002373, 324917157, 255290265, 70739478047, 3180469485, 18626672011][i]!
def words (i : Fin 37) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[145, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 37 rawWords i=rowTotals i)

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
private theorem row31 : rowAgrees 31=true := by decide +kernel
private theorem row32 : rowAgrees 32=true := by decide +kernel
private theorem row33 : rowAgrees 33=true := by decide +kernel
private theorem row34 : rowAgrees 34=true := by decide +kernel
private theorem row35 : rowAgrees 35=true := by decide +kernel
private theorem row36 : rowAgrees 36=true := by decide +kernel
private theorem rowChecked : allBelow 37 rowAgrees=true := by
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
  have h := allBelow_step h row31
  have h := allBelow_step h row32
  have h := allBelow_step h row33
  have h := allBelow_step h row34
  have h := allBelow_step h row35
  have h := allBelow_step h row36
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 37, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 37, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(1044:ℤ) := by
  change cubicInteger (fun i : Fin 37 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(1044:ℤ) ∧
    87*(37:ℤ)^3+375*37*(4*37-3)+1000*((wordMatrix words-1)^3).trace-
      1110*73*(37-1)=(4545606:ℤ) ∧ 0≤(4545606:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 37 ⊕ Fin 37 → Fin 74
  | .inl i => Fin.ofNat 74 (#[0, 5, 7, 10, 11, 13, 14, 15, 17, 20, 21, 22, 26, 28, 29, 30, 31, 33, 34, 39, 40, 42, 43, 44, 45, 47, 51, 52, 53, 56, 58, 59, 60, 62, 63, 66, 68][i.val]!)
  | .inr i => Fin.ofNat 74 (#[1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 19, 23, 24, 25, 27, 32, 35, 36, 37, 38, 41, 46, 48, 49, 50, 54, 55, 57, 61, 64, 65, 67, 69, 70, 71, 72, 73][i.val]!)

def pointPosition (i : Fin 74) : Fin 37 ⊕ Fin 37 :=
  let j : ℕ := #[0, 37, 38, 39, 40, 1, 41, 2, 42, 43, 3, 4, 44, 5, 6, 7, 45, 8, 46, 47, 9, 10, 11, 48, 49, 50, 12, 51, 13, 14, 15, 16, 52, 17, 18, 53, 54, 55, 56, 19, 20, 57, 21, 22, 23, 24, 58, 25, 59, 60, 61, 26, 27, 28, 62, 63, 29, 64, 30, 31, 32, 65, 33, 34, 66, 67, 35, 68, 36, 69, 70, 71, 72, 73][i.val]!
  if j<37 then .inl (Fin.ofNat 37 j) else .inr (Fin.ofNat 37 (j-37))

def indexing : (Fin 37 ⊕ Fin 37) ≃ Fin 74 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 37,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*73)*(73-1)^36) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 36 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 36 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 36=(2*73)*(73-1)^36 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquares


namespace NonsplitNegative
def rawWords (i : ℕ) : ℕ := #[46606313172, 29050745472, 58646832449, 117544725632, 101320578817, 61158868992, 115674225669, 89337737227, 41077663764, 31036198931, 25206161501, 67824714088, 131208233682, 116252574095, 106685403953, 6321354437, 30025461143, 59115593519, 118755431966, 129285331318, 125602787565, 113498222553, 38034261921, 13725063879, 121876193847, 80813640798, 24162686204, 62284996329, 77357246265, 43045454436, 85956218059, 34599296471, 76984092, 984431227, 1293622966, 2843638125, 1396469976][i]!
def words (i : Fin 37) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85, 85]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 37 rawWords i=rowTotals i)

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
private theorem row31 : rowAgrees 31=true := by decide +kernel
private theorem row32 : rowAgrees 32=true := by decide +kernel
private theorem row33 : rowAgrees 33=true := by decide +kernel
private theorem row34 : rowAgrees 34=true := by decide +kernel
private theorem row35 : rowAgrees 35=true := by decide +kernel
private theorem row36 : rowAgrees 36=true := by decide +kernel
private theorem rowChecked : allBelow 37 rowAgrees=true := by
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
  have h := allBelow_step h row31
  have h := allBelow_step h row32
  have h := allBelow_step h row33
  have h := allBelow_step h row34
  have h := allBelow_step h row35
  have h := allBelow_step h row36
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 37, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 37, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-888:ℤ) := by
  change cubicInteger (fun i : Fin 37 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-888:ℤ) ∧
    87*(37:ℤ)^3+375*37*(4*37-3)+1000*((wordMatrix words-1)^3).trace-
      1110*73*(37-1)=(2613606:ℤ) ∧ 0≤(2613606:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 37 ⊕ Fin 37 → Fin 74
  | .inl i => Fin.ofNat 74 (#[0, 4, 5, 6, 7, 8, 10, 11, 12, 14, 20, 23, 24, 26, 29, 31, 33, 34, 35, 38, 39, 40, 42, 44, 47, 49, 50, 53, 59, 61, 62, 63, 65, 66, 67, 68, 69][i.val]!)
  | .inr i => Fin.ofNat 74 (#[1, 2, 3, 9, 13, 15, 16, 17, 18, 19, 21, 22, 25, 27, 28, 30, 32, 36, 37, 41, 43, 45, 46, 48, 51, 52, 54, 55, 56, 57, 58, 60, 64, 70, 71, 72, 73][i.val]!)

def pointPosition (i : Fin 74) : Fin 37 ⊕ Fin 37 :=
  let j : ℕ := #[0, 37, 38, 39, 1, 2, 3, 4, 5, 40, 6, 7, 8, 41, 9, 42, 43, 44, 45, 46, 10, 47, 48, 11, 12, 49, 13, 50, 51, 14, 52, 15, 53, 16, 17, 18, 54, 55, 19, 20, 21, 56, 22, 57, 23, 58, 59, 24, 60, 25, 26, 61, 62, 27, 63, 64, 65, 66, 67, 28, 68, 29, 30, 31, 69, 32, 33, 34, 35, 36, 70, 71, 72, 73][i.val]!
  if j<37 then .inl (Fin.ofNat 37 j) else .inr (Fin.ofNat 37 (j-37))

def indexing : (Fin 37 ⊕ Fin 37) ≃ Fin 74 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 37,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*73)*(73-1)^36) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 36 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 36 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 36=(2*73)*(73-1)^36 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegative


namespace SplitSquaresOpposite
def rawWords (i : ℕ) : ℕ := #[43851943236, 29645944736, 64632964033, 13872504320, 20358584576, 19226341890, 59607383301, 42205631494, 16275718231, 62397782062, 21985829067, 55116137049, 40545616634, 51044549730, 12749111764, 7764708269, 31296331035, 49723745201, 38055066781, 58175088942, 48804968248, 11677040372, 18824553597, 25569186025, 41407957683, 56644790154, 31165042199, 62817928508, 25815309497, 43148931195, 17261001186, 162458578, 127645132, 35369739023, 1590234742, 9313336005, 0][i]!
def words (i : Fin 37) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 137, 145]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 37 rawWords i=rowTotals i)

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
private theorem row31 : rowAgrees 31=true := by decide +kernel
private theorem row32 : rowAgrees 32=true := by decide +kernel
private theorem row33 : rowAgrees 33=true := by decide +kernel
private theorem row34 : rowAgrees 34=true := by decide +kernel
private theorem row35 : rowAgrees 35=true := by decide +kernel
private theorem row36 : rowAgrees 36=true := by decide +kernel
private theorem rowChecked : allBelow 37 rowAgrees=true := by
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
  have h := allBelow_step h row31
  have h := allBelow_step h row32
  have h := allBelow_step h row33
  have h := allBelow_step h row34
  have h := allBelow_step h row35
  have h := allBelow_step h row36
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 37, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 37, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(1044:ℤ) := by
  change cubicInteger (fun i : Fin 37 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(1044:ℤ) ∧
    87*(37:ℤ)^3+375*37*(4*37-3)+1000*((wordMatrix words-1)^3).trace-
      1110*73*(37-1)=(4545606:ℤ) ∧ 0≤(4545606:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 37 ⊕ Fin 37 → Fin 74
  | .inl i => Fin.ofNat 74 (#[5, 7, 10, 11, 13, 14, 15, 17, 20, 21, 22, 26, 28, 29, 30, 31, 33, 34, 39, 40, 42, 43, 44, 45, 47, 51, 52, 53, 56, 58, 59, 60, 62, 63, 66, 68, 73][i.val]!)
  | .inr i => Fin.ofNat 74 (#[0, 1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 19, 23, 24, 25, 27, 32, 35, 36, 37, 38, 41, 46, 48, 49, 50, 54, 55, 57, 61, 64, 65, 67, 69, 70, 71, 72][i.val]!)

def pointPosition (i : Fin 74) : Fin 37 ⊕ Fin 37 :=
  let j : ℕ := #[37, 38, 39, 40, 41, 0, 42, 1, 43, 44, 2, 3, 45, 4, 5, 6, 46, 7, 47, 48, 8, 9, 10, 49, 50, 51, 11, 52, 12, 13, 14, 15, 53, 16, 17, 54, 55, 56, 57, 18, 19, 58, 20, 21, 22, 23, 59, 24, 60, 61, 62, 25, 26, 27, 63, 64, 28, 65, 29, 30, 31, 66, 32, 33, 67, 68, 34, 69, 35, 70, 71, 72, 73, 36][i.val]!
  if j<37 then .inl (Fin.ofNat 37 j) else .inr (Fin.ofNat 37 (j-37))

def indexing : (Fin 37 ⊕ Fin 37) ≃ Fin 74 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 37,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*73)*(73-1)^36) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 36 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 36 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 36=(2*73)*(73-1)^36 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquaresOpposite


namespace SplitNonsquaresOpposite
def rawWords (i : ℕ) : ℕ := #[7422987184, 10581417408, 22941186848, 45850932800, 40431504641, 28812652037, 59371232522, 61978766339, 41165932631, 31556479021, 60965425402, 11988239351, 24414848078, 51106251436, 67056206225, 52926113439, 6406812251, 16805539126, 29179828604, 58598652904, 66947536035, 36911166367, 14296106621, 30635970394, 64357864756, 25511114951, 48341021102, 62833253017, 51597395815, 21668508859, 43071810262, 34548382057, 651916117, 1305898666, 1000134372, 3711493592, 0][i]!
def words (i : Fin 37) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 73]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 37 rawWords i=rowTotals i)

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
private theorem row31 : rowAgrees 31=true := by decide +kernel
private theorem row32 : rowAgrees 32=true := by decide +kernel
private theorem row33 : rowAgrees 33=true := by decide +kernel
private theorem row34 : rowAgrees 34=true := by decide +kernel
private theorem row35 : rowAgrees 35=true := by decide +kernel
private theorem row36 : rowAgrees 36=true := by decide +kernel
private theorem rowChecked : allBelow 37 rowAgrees=true := by
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
  have h := allBelow_step h row31
  have h := allBelow_step h row32
  have h := allBelow_step h row33
  have h := allBelow_step h row34
  have h := allBelow_step h row35
  have h := allBelow_step h row36
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 37, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 37, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-1044:ℤ) := by
  change cubicInteger (fun i : Fin 37 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-1044:ℤ) ∧
    87*(37:ℤ)^3+375*37*(4*37-3)+1000*((wordMatrix words-1)^3).trace-
      1110*73*(37-1)=(2457606:ℤ) ∧ 0≤(2457606:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 37 ⊕ Fin 37 → Fin 74
  | .inl i => Fin.ofNat 74 (#[1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 19, 23, 24, 25, 27, 32, 35, 36, 37, 38, 41, 46, 48, 49, 50, 54, 55, 57, 61, 64, 65, 67, 69, 70, 71, 72, 73][i.val]!)
  | .inr i => Fin.ofNat 74 (#[0, 5, 7, 10, 11, 13, 14, 15, 17, 20, 21, 22, 26, 28, 29, 30, 31, 33, 34, 39, 40, 42, 43, 44, 45, 47, 51, 52, 53, 56, 58, 59, 60, 62, 63, 66, 68][i.val]!)

def pointPosition (i : Fin 74) : Fin 37 ⊕ Fin 37 :=
  let j : ℕ := #[37, 0, 1, 2, 3, 38, 4, 39, 5, 6, 40, 41, 7, 42, 43, 44, 8, 45, 9, 10, 46, 47, 48, 11, 12, 13, 49, 14, 50, 51, 52, 53, 15, 54, 55, 16, 17, 18, 19, 56, 57, 20, 58, 59, 60, 61, 21, 62, 22, 23, 24, 63, 64, 65, 25, 26, 66, 27, 67, 68, 69, 28, 70, 71, 29, 30, 72, 31, 73, 32, 33, 34, 35, 36][i.val]!
  if j<37 then .inl (Fin.ofNat 37 j) else .inr (Fin.ofNat 37 (j-37))

def indexing : (Fin 37 ⊕ Fin 37) ≃ Fin 74 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 37,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*73)*(73-1)^36) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 36 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 36 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 36=(2*73)*(73-1)^36 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquaresOpposite


namespace NonsplitNegativeOpposite
def rawWords (i : ℕ) : ℕ := #[7096348000, 16314518264, 17665823184, 54082701890, 60034703622, 21156059139, 37990343695, 15870584838, 29590900757, 65543045130, 41055633473, 4757856427, 48811442468, 64299534545, 62087759282, 50788569851, 54869114791, 14786502246, 27506354412, 61736150579, 59936853181, 20837421799, 37330031095, 9799756717, 57181904264, 34899595033, 21476758575, 45108182134, 25794640092, 64463724977, 51568964466, 25911469563, 17801846419, 3096376194, 8409408316, 1801057880, 0][i]!
def words (i : Fin 37) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 37 rawWords i=rowTotals i)

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
private theorem row31 : rowAgrees 31=true := by decide +kernel
private theorem row32 : rowAgrees 32=true := by decide +kernel
private theorem row33 : rowAgrees 33=true := by decide +kernel
private theorem row34 : rowAgrees 34=true := by decide +kernel
private theorem row35 : rowAgrees 35=true := by decide +kernel
private theorem row36 : rowAgrees 36=true := by decide +kernel
private theorem rowChecked : allBelow 37 rowAgrees=true := by
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
  have h := allBelow_step h row31
  have h := allBelow_step h row32
  have h := allBelow_step h row33
  have h := allBelow_step h row34
  have h := allBelow_step h row35
  have h := allBelow_step h row36
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 37, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 37, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(888:ℤ) := by
  change cubicInteger (fun i : Fin 37 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(888:ℤ) ∧
    87*(37:ℤ)^3+375*37*(4*37-3)+1000*((wordMatrix words-1)^3).trace-
      1110*73*(37-1)=(4389606:ℤ) ∧ 0≤(4389606:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 37 ⊕ Fin 37 → Fin 74
  | .inl i => Fin.ofNat 74 (#[1, 2, 3, 9, 13, 15, 16, 17, 18, 19, 21, 22, 25, 27, 28, 30, 32, 36, 37, 41, 43, 45, 46, 48, 51, 52, 54, 55, 56, 57, 58, 60, 64, 70, 71, 72, 73][i.val]!)
  | .inr i => Fin.ofNat 74 (#[0, 4, 5, 6, 7, 8, 10, 11, 12, 14, 20, 23, 24, 26, 29, 31, 33, 34, 35, 38, 39, 40, 42, 44, 47, 49, 50, 53, 59, 61, 62, 63, 65, 66, 67, 68, 69][i.val]!)

def pointPosition (i : Fin 74) : Fin 37 ⊕ Fin 37 :=
  let j : ℕ := #[37, 0, 1, 2, 38, 39, 40, 41, 42, 3, 43, 44, 45, 4, 46, 5, 6, 7, 8, 9, 47, 10, 11, 48, 49, 12, 50, 13, 14, 51, 15, 52, 16, 53, 54, 55, 17, 18, 56, 57, 58, 19, 59, 20, 60, 21, 22, 61, 23, 62, 63, 24, 25, 64, 26, 27, 28, 29, 30, 65, 31, 66, 67, 68, 32, 69, 70, 71, 72, 73, 33, 34, 35, 36][i.val]!
  if j<37 then .inl (Fin.ofNat 37 j) else .inr (Fin.ofNat 37 (j-37))

def indexing : (Fin 37 ⊕ Fin 37) ≃ Fin 74 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 37,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*73)*(73-1)^36) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 36 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 36 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 36=(2*73)*(73-1)^36 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegativeOpposite

end PaleyBits73
