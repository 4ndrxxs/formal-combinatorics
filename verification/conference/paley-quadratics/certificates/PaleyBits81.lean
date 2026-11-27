import Quantum.Hadamard.ConferenceBitCompletion
open Hadamard.BitTrace Hadamard.DeterminantRatio Matrix
set_option maxHeartbeats 12000000
set_option maxRecDepth 60000
namespace PaleyBits81

def rawFull (i : ℕ) : ℕ := #[419902435807577361750248, 835600149124075108737944, 1402089988126613958903152, 913033702342222951008579, 1825486190135895562719942, 1531146338578799006983557, 55436977671580244656669, 106224364809736833504307, 178801870434535595124782, 2219098792036444088160338, 2285388747896906551079076, 2185990636506505846382857, 827884129896555722475153, 1358194607486598470012194, 562991251675289358109260, 1787360573159583816891018, 1194131928113353501206292, 2086041498593754891705441, 2206165264167405153723660, 2296702129443978539518033, 2179749396076001446990498, 752639551442556604457572, 1472221384587437038781577, 527173213407419305335058, 1180699899899522579764513, 2096938179517945266186314, 1780681387500579765928596, 1490576421599920607439827, 596938859772115863980006, 896367620100451962428877, 2248491726709210069950111, 2348232934746445782335287, 2316385073943133539069551, 1091251287840771166631162, 1884467773034416916003260, 1620258654253458874921849, 1551865699297822848296536, 983388975889625360878768, 1966260308007285843270440, 330389764754481690263233, 623001622219319475597186, 1241862094508730431102788, 196932387855237028377611, 124697956918430335727638, 249323153677371497181733, 1499901454152443311731157, 582016983631004840845795, 899000356016059542032846, 2327795889029435445052079, 2238265729172316543190303, 2356262694231531868555383, 1697460905910923906520954, 981210457584462461938940, 1925167713510476151540665, 389710097770159128088893, 775222552425905178386555, 1252927943975462405357758, 685671302673133783256044, 1370753462453083081869273, 361434075645140634570226, 654352651985256514868071, 1304056598328506507343055, 459435437894319275272599, 1267735533435867405384507, 386277792292306627393150, 768422361236949516254397, 475218415710869923551708, 648795670111344779047921, 1297517681317517712942570, 1365033890642264569859815, 349930492577198130175887, 699336277517278544867159, 1096350184828792433178440, 1928239634302903021010128, 1740277993858753046870944, 1526663569959691933169733, 937705820440377518711427, 1837706477984031064184070, 138226668302374675533353, 243387689997420438953498, 218126204697668191432244, 0][i]!
def fullRows (i : Fin 82) : ℕ := rawFull i.val

private theorem fullSymmetric : (wordMatrix fullRows).IsSymm := by
  have h : ∀ i j : Fin 82, sign (fullRows i) j.val=sign (fullRows j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem fullDiagonal : ∀ i : Fin 82, sign (fullRows i) i.val=1 := by decide +kernel
private theorem lower0 : (lowerRow 82 rawFull) 0=true := by decide +kernel
private theorem lower1 : (lowerRow 82 rawFull) 1=true := by decide +kernel
private theorem lower2 : (lowerRow 82 rawFull) 2=true := by decide +kernel
private theorem lower3 : (lowerRow 82 rawFull) 3=true := by decide +kernel
private theorem lower4 : (lowerRow 82 rawFull) 4=true := by decide +kernel
private theorem lower5 : (lowerRow 82 rawFull) 5=true := by decide +kernel
private theorem lower6 : (lowerRow 82 rawFull) 6=true := by decide +kernel
private theorem lower7 : (lowerRow 82 rawFull) 7=true := by decide +kernel
private theorem lower8 : (lowerRow 82 rawFull) 8=true := by decide +kernel
private theorem lower9 : (lowerRow 82 rawFull) 9=true := by decide +kernel
private theorem lower10 : (lowerRow 82 rawFull) 10=true := by decide +kernel
private theorem lower11 : (lowerRow 82 rawFull) 11=true := by decide +kernel
private theorem lower12 : (lowerRow 82 rawFull) 12=true := by decide +kernel
private theorem lower13 : (lowerRow 82 rawFull) 13=true := by decide +kernel
private theorem lower14 : (lowerRow 82 rawFull) 14=true := by decide +kernel
private theorem lower15 : (lowerRow 82 rawFull) 15=true := by decide +kernel
private theorem lower16 : (lowerRow 82 rawFull) 16=true := by decide +kernel
private theorem lower17 : (lowerRow 82 rawFull) 17=true := by decide +kernel
private theorem lower18 : (lowerRow 82 rawFull) 18=true := by decide +kernel
private theorem lower19 : (lowerRow 82 rawFull) 19=true := by decide +kernel
private theorem lower20 : (lowerRow 82 rawFull) 20=true := by decide +kernel
private theorem lower21 : (lowerRow 82 rawFull) 21=true := by decide +kernel
private theorem lower22 : (lowerRow 82 rawFull) 22=true := by decide +kernel
private theorem lower23 : (lowerRow 82 rawFull) 23=true := by decide +kernel
private theorem lower24 : (lowerRow 82 rawFull) 24=true := by decide +kernel
private theorem lower25 : (lowerRow 82 rawFull) 25=true := by decide +kernel
private theorem lower26 : (lowerRow 82 rawFull) 26=true := by decide +kernel
private theorem lower27 : (lowerRow 82 rawFull) 27=true := by decide +kernel
private theorem lower28 : (lowerRow 82 rawFull) 28=true := by decide +kernel
private theorem lower29 : (lowerRow 82 rawFull) 29=true := by decide +kernel
private theorem lower30 : (lowerRow 82 rawFull) 30=true := by decide +kernel
private theorem lower31 : (lowerRow 82 rawFull) 31=true := by decide +kernel
private theorem lower32 : (lowerRow 82 rawFull) 32=true := by decide +kernel
private theorem lower33 : (lowerRow 82 rawFull) 33=true := by decide +kernel
private theorem lower34 : (lowerRow 82 rawFull) 34=true := by decide +kernel
private theorem lower35 : (lowerRow 82 rawFull) 35=true := by decide +kernel
private theorem lower36 : (lowerRow 82 rawFull) 36=true := by decide +kernel
private theorem lower37 : (lowerRow 82 rawFull) 37=true := by decide +kernel
private theorem lower38 : (lowerRow 82 rawFull) 38=true := by decide +kernel
private theorem lower39 : (lowerRow 82 rawFull) 39=true := by decide +kernel
private theorem lower40 : (lowerRow 82 rawFull) 40=true := by decide +kernel
private theorem lower41 : (lowerRow 82 rawFull) 41=true := by decide +kernel
private theorem lower42 : (lowerRow 82 rawFull) 42=true := by decide +kernel
private theorem lower43 : (lowerRow 82 rawFull) 43=true := by decide +kernel
private theorem lower44 : (lowerRow 82 rawFull) 44=true := by decide +kernel
private theorem lower45 : (lowerRow 82 rawFull) 45=true := by decide +kernel
private theorem lower46 : (lowerRow 82 rawFull) 46=true := by decide +kernel
private theorem lower47 : (lowerRow 82 rawFull) 47=true := by decide +kernel
private theorem lower48 : (lowerRow 82 rawFull) 48=true := by decide +kernel
private theorem lower49 : (lowerRow 82 rawFull) 49=true := by decide +kernel
private theorem lower50 : (lowerRow 82 rawFull) 50=true := by decide +kernel
private theorem lower51 : (lowerRow 82 rawFull) 51=true := by decide +kernel
private theorem lower52 : (lowerRow 82 rawFull) 52=true := by decide +kernel
private theorem lower53 : (lowerRow 82 rawFull) 53=true := by decide +kernel
private theorem lower54 : (lowerRow 82 rawFull) 54=true := by decide +kernel
private theorem lower55 : (lowerRow 82 rawFull) 55=true := by decide +kernel
private theorem lower56 : (lowerRow 82 rawFull) 56=true := by decide +kernel
private theorem lower57 : (lowerRow 82 rawFull) 57=true := by decide +kernel
private theorem lower58 : (lowerRow 82 rawFull) 58=true := by decide +kernel
private theorem lower59 : (lowerRow 82 rawFull) 59=true := by decide +kernel
private theorem lower60 : (lowerRow 82 rawFull) 60=true := by decide +kernel
private theorem lower61 : (lowerRow 82 rawFull) 61=true := by decide +kernel
private theorem lower62 : (lowerRow 82 rawFull) 62=true := by decide +kernel
private theorem lower63 : (lowerRow 82 rawFull) 63=true := by decide +kernel
private theorem lower64 : (lowerRow 82 rawFull) 64=true := by decide +kernel
private theorem lower65 : (lowerRow 82 rawFull) 65=true := by decide +kernel
private theorem lower66 : (lowerRow 82 rawFull) 66=true := by decide +kernel
private theorem lower67 : (lowerRow 82 rawFull) 67=true := by decide +kernel
private theorem lower68 : (lowerRow 82 rawFull) 68=true := by decide +kernel
private theorem lower69 : (lowerRow 82 rawFull) 69=true := by decide +kernel
private theorem lower70 : (lowerRow 82 rawFull) 70=true := by decide +kernel
private theorem lower71 : (lowerRow 82 rawFull) 71=true := by decide +kernel
private theorem lower72 : (lowerRow 82 rawFull) 72=true := by decide +kernel
private theorem lower73 : (lowerRow 82 rawFull) 73=true := by decide +kernel
private theorem lower74 : (lowerRow 82 rawFull) 74=true := by decide +kernel
private theorem lower75 : (lowerRow 82 rawFull) 75=true := by decide +kernel
private theorem lower76 : (lowerRow 82 rawFull) 76=true := by decide +kernel
private theorem lower77 : (lowerRow 82 rawFull) 77=true := by decide +kernel
private theorem lower78 : (lowerRow 82 rawFull) 78=true := by decide +kernel
private theorem lower79 : (lowerRow 82 rawFull) 79=true := by decide +kernel
private theorem lower80 : (lowerRow 82 rawFull) 80=true := by decide +kernel
private theorem lower81 : (lowerRow 82 rawFull) 81=true := by decide +kernel
private theorem lowerChecked : allBelow 82 (lowerRow 82 rawFull)=true := by
  have h : allBelow 0 (lowerRow 82 rawFull)=true := rfl
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
  have h := allBelow_step h lower74
  have h := allBelow_step h lower75
  have h := allBelow_step h lower76
  have h := allBelow_step h lower77
  have h := allBelow_step h lower78
  have h := allBelow_step h lower79
  have h := allBelow_step h lower80
  have h := allBelow_step h lower81
  exact h

private theorem fullPairs : ∀ i j : Fin 82, i≠j →
    correlation 82 (fullRows i) (fullRows j)=2*sign (fullRows i) j.val :=
  correlations_of_lower rawFull fullSymmetric lowerChecked


namespace SplitSquares
def rawWords (i : ℕ) : ℕ := #[0, 849036628664, 1389271657816, 1733996397606, 475898989702, 1826599679754, 2051278244996, 1361816890962, 546126627876, 1474272643234, 988420907516, 1761569202900, 1848846663714, 794548309156, 518535748122, 2070148171906, 1429501670188, 484603119478, 1093892320202, 1904350467996, 1128620596968, 583755485000, 1958261929520, 663880940018, 1330405202804, 83377583502, 1058845473046, 1639706583162, 804245729484, 1157534383374, 601756512820, 142505140314, 46093861870, 416997449500, 1170067494866, 830951225840, 1666976738248, 1385614472624, 1829862098774, 379381922922, 498909944556][i]!
def words (i : Fin 41) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[81, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 41 rawWords i=rowTotals i)

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
private theorem row37 : rowAgrees 37=true := by decide +kernel
private theorem row38 : rowAgrees 38=true := by decide +kernel
private theorem row39 : rowAgrees 39=true := by decide +kernel
private theorem row40 : rowAgrees 40=true := by decide +kernel
private theorem rowChecked : allBelow 41 rowAgrees=true := by
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
  have h := allBelow_step h row37
  have h := allBelow_step h row38
  have h := allBelow_step h row39
  have h := allBelow_step h row40
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 41, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 41, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(1560:ℤ) := by
  change cubicInteger (fun i : Fin 41 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(1560:ℤ) ∧
    87*(41:ℤ)^3+375*41*(4*41-3)+1000*((wordMatrix words-1)^3).trace-
      1110*81*(41-1)=(6435102:ℤ) ∧ 0≤(6435102:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 41 ⊕ Fin 41 → Fin 82
  | .inl i => Fin.ofNat 82 (#[0, 1, 2, 4, 8, 9, 10, 13, 14, 15, 16, 18, 20, 21, 23, 25, 26, 28, 33, 34, 36, 37, 38, 40, 41, 43, 47, 51, 52, 56, 57, 59, 64, 66, 68, 72, 73, 74, 77, 79, 80][i.val]!)
  | .inr i => Fin.ofNat 82 (#[3, 5, 6, 7, 11, 12, 17, 19, 22, 24, 27, 29, 30, 31, 32, 35, 39, 42, 44, 45, 46, 48, 49, 50, 53, 54, 55, 58, 60, 61, 62, 63, 65, 67, 69, 70, 71, 75, 76, 78, 81][i.val]!)

def pointPosition (i : Fin 82) : Fin 41 ⊕ Fin 41 :=
  let j : ℕ := #[0, 1, 2, 41, 3, 42, 43, 44, 4, 5, 6, 45, 46, 7, 8, 9, 10, 47, 11, 48, 12, 13, 49, 14, 50, 15, 16, 51, 17, 52, 53, 54, 55, 18, 19, 56, 20, 21, 22, 57, 23, 24, 58, 25, 59, 60, 61, 26, 62, 63, 64, 27, 28, 65, 66, 67, 29, 30, 68, 31, 69, 70, 71, 72, 32, 73, 33, 74, 34, 75, 76, 77, 35, 36, 37, 78, 79, 38, 80, 39, 40, 81][i.val]!
  if j<41 then .inl (Fin.ofNat 41 j) else .inr (Fin.ofNat 41 (j-41))

def indexing : (Fin 41 ⊕ Fin 41) ≃ Fin 82 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 41,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*81)*(81-1)^40) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 40 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 40 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 40=(2*81)*(81-1)^40 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquares


namespace SplitNonsquares
def rawWords (i : ℕ) : ℕ := #[2199023255550, 1182706020905, 1164731597969, 465889892739, 682135534149, 1629990615427, 375341937809, 1018000136813, 1189403312681, 758579465619, 1931581106757, 998926624441, 1032307458299, 1975157853299, 1726428090853, 1524583963695, 1678746104015, 1352663845241, 461424961347, 789141686981, 986253178713, 1986200096029, 1641318224663, 2187416054659, 1892102391213, 751911065143, 1796920396743, 59350292239, 74795703835, 416955688269, 584596320603, 1194153733937, 378940450023, 191234023543, 388878631389, 31338145981, 1398310327155, 559014648489, 1190258851049, 1238153920145, 895599502631][i]!
def words (i : Fin 41) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[161, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 41 rawWords i=rowTotals i)

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
private theorem row37 : rowAgrees 37=true := by decide +kernel
private theorem row38 : rowAgrees 38=true := by decide +kernel
private theorem row39 : rowAgrees 39=true := by decide +kernel
private theorem row40 : rowAgrees 40=true := by decide +kernel
private theorem rowChecked : allBelow 41 rowAgrees=true := by
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
  have h := allBelow_step h row37
  have h := allBelow_step h row38
  have h := allBelow_step h row39
  have h := allBelow_step h row40
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 41, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 41, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-1560:ℤ) := by
  change cubicInteger (fun i : Fin 41 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-1560:ℤ) ∧
    87*(41:ℤ)^3+375*41*(4*41-3)+1000*((wordMatrix words-1)^3).trace-
      1110*81*(41-1)=(3315102:ℤ) ∧ 0≤(3315102:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 41 ⊕ Fin 41 → Fin 82
  | .inl i => Fin.ofNat 82 (#[0, 3, 5, 6, 7, 11, 12, 17, 19, 22, 24, 27, 29, 30, 31, 32, 35, 39, 42, 44, 45, 46, 48, 49, 50, 53, 54, 55, 58, 60, 61, 62, 63, 65, 67, 69, 70, 71, 75, 76, 78][i.val]!)
  | .inr i => Fin.ofNat 82 (#[1, 2, 4, 8, 9, 10, 13, 14, 15, 16, 18, 20, 21, 23, 25, 26, 28, 33, 34, 36, 37, 38, 40, 41, 43, 47, 51, 52, 56, 57, 59, 64, 66, 68, 72, 73, 74, 77, 79, 80, 81][i.val]!)

def pointPosition (i : Fin 82) : Fin 41 ⊕ Fin 41 :=
  let j : ℕ := #[0, 41, 42, 1, 43, 2, 3, 4, 44, 45, 46, 5, 6, 47, 48, 49, 50, 7, 51, 8, 52, 53, 9, 54, 10, 55, 56, 11, 57, 12, 13, 14, 15, 58, 59, 16, 60, 61, 62, 17, 63, 64, 18, 65, 19, 20, 21, 66, 22, 23, 24, 67, 68, 25, 26, 27, 69, 70, 28, 71, 29, 30, 31, 32, 72, 33, 73, 34, 74, 35, 36, 37, 75, 76, 77, 38, 39, 78, 40, 79, 80, 81][i.val]!
  if j<41 then .inl (Fin.ofNat 41 j) else .inr (Fin.ofNat 41 (j-41))

def indexing : (Fin 41 ⊕ Fin 41) ≃ Fin 82 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 41,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*81)*(81-1)^40) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 40 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 40 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 40=(2*81)*(81-1)^40 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquares


namespace NonsplitNegative
def rawWords (i : ℕ) : ℕ := #[1592709197968, 1073438927200, 787236158984, 1904604166180, 1334166384865, 462885479002, 2048775715890, 1754055394833, 1289814795266, 347618088100, 1971163247556, 1993781329998, 1067232962141, 1801556645247, 22756272628, 1418908547361, 1367303537593, 377102570294, 1046334219877, 1020113491173, 1989949916579, 957270552326, 1618249794959, 2186375957463, 1767922967178, 1338232278844, 553292069859, 108188390150, 639112690697, 1242472398490, 297232758703, 120652170803, 1599533375598, 721608483901, 1794536849748, 491941107178, 1140781947615, 339886289215, 1276695715427, 26134461646, 365673164249][i]!
def words (i : Fin 41) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 41 rawWords i=rowTotals i)

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
private theorem row37 : rowAgrees 37=true := by decide +kernel
private theorem row38 : rowAgrees 38=true := by decide +kernel
private theorem row39 : rowAgrees 39=true := by decide +kernel
private theorem row40 : rowAgrees 40=true := by decide +kernel
private theorem rowChecked : allBelow 41 rowAgrees=true := by
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
  have h := allBelow_step h row37
  have h := allBelow_step h row38
  have h := allBelow_step h row39
  have h := allBelow_step h row40
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 41, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 41, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(0:ℤ) := by
  change cubicInteger (fun i : Fin 41 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(0:ℤ) ∧
    87*(41:ℤ)^3+375*41*(4*41-3)+1000*((wordMatrix words-1)^3).trace-
      1110*81*(41-1)=(4875102:ℤ) ∧ 0≤(4875102:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 41 ⊕ Fin 41 → Fin 82
  | .inl i => Fin.ofNat 82 (#[0, 1, 2, 10, 11, 13, 15, 19, 20, 21, 26, 28, 29, 32, 34, 35, 39, 43, 44, 45, 46, 47, 49, 50, 51, 52, 55, 56, 58, 59, 61, 63, 64, 65, 66, 68, 70, 71, 76, 77, 78][i.val]!)
  | .inr i => Fin.ofNat 82 (#[3, 4, 5, 6, 7, 8, 9, 12, 14, 16, 17, 18, 22, 23, 24, 25, 27, 30, 31, 33, 36, 37, 38, 40, 41, 42, 48, 53, 54, 57, 60, 62, 67, 69, 72, 73, 74, 75, 79, 80, 81][i.val]!)

def pointPosition (i : Fin 82) : Fin 41 ⊕ Fin 41 :=
  let j : ℕ := #[0, 1, 2, 41, 42, 43, 44, 45, 46, 47, 3, 4, 48, 5, 49, 6, 50, 51, 52, 7, 8, 9, 53, 54, 55, 56, 10, 57, 11, 12, 58, 59, 13, 60, 14, 15, 61, 62, 63, 16, 64, 65, 66, 17, 18, 19, 20, 21, 67, 22, 23, 24, 25, 68, 69, 26, 27, 70, 28, 29, 71, 30, 72, 31, 32, 33, 34, 73, 35, 74, 36, 37, 75, 76, 77, 78, 38, 39, 40, 79, 80, 81][i.val]!
  if j<41 then .inl (Fin.ofNat 41 j) else .inr (Fin.ofNat 41 (j-41))

def indexing : (Fin 41 ⊕ Fin 41) ≃ Fin 82 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 41,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*81)*(81-1)^40) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 40 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 40 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 40=(2*81)*(81-1)^40 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegative


namespace SplitSquaresOpposite
def rawWords (i : ℕ) : ℕ := #[591353010452, 582365798984, 232944946369, 341067767074, 814995307713, 187670968904, 509000068406, 594701656340, 379289732809, 965790553378, 499463312220, 516153729149, 987578926649, 863214045426, 762291981847, 839373052007, 676331922620, 230712480673, 394570843490, 493126589356, 993100048014, 820659112331, 1093708027329, 946051195606, 375955532571, 898460198371, 29675146119, 37397851917, 208477844134, 292298160301, 597076866968, 189470225011, 95617011771, 194439315694, 15669072990, 699155163577, 279507324244, 595129425524, 619076960072, 447799751315, 0][i]!
def words (i : Fin 41) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 161]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 41 rawWords i=rowTotals i)

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
private theorem row37 : rowAgrees 37=true := by decide +kernel
private theorem row38 : rowAgrees 38=true := by decide +kernel
private theorem row39 : rowAgrees 39=true := by decide +kernel
private theorem row40 : rowAgrees 40=true := by decide +kernel
private theorem rowChecked : allBelow 41 rowAgrees=true := by
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
  have h := allBelow_step h row37
  have h := allBelow_step h row38
  have h := allBelow_step h row39
  have h := allBelow_step h row40
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 41, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 41, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-1560:ℤ) := by
  change cubicInteger (fun i : Fin 41 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-1560:ℤ) ∧
    87*(41:ℤ)^3+375*41*(4*41-3)+1000*((wordMatrix words-1)^3).trace-
      1110*81*(41-1)=(3315102:ℤ) ∧ 0≤(3315102:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 41 ⊕ Fin 41 → Fin 82
  | .inl i => Fin.ofNat 82 (#[3, 5, 6, 7, 11, 12, 17, 19, 22, 24, 27, 29, 30, 31, 32, 35, 39, 42, 44, 45, 46, 48, 49, 50, 53, 54, 55, 58, 60, 61, 62, 63, 65, 67, 69, 70, 71, 75, 76, 78, 81][i.val]!)
  | .inr i => Fin.ofNat 82 (#[0, 1, 2, 4, 8, 9, 10, 13, 14, 15, 16, 18, 20, 21, 23, 25, 26, 28, 33, 34, 36, 37, 38, 40, 41, 43, 47, 51, 52, 56, 57, 59, 64, 66, 68, 72, 73, 74, 77, 79, 80][i.val]!)

def pointPosition (i : Fin 82) : Fin 41 ⊕ Fin 41 :=
  let j : ℕ := #[41, 42, 43, 0, 44, 1, 2, 3, 45, 46, 47, 4, 5, 48, 49, 50, 51, 6, 52, 7, 53, 54, 8, 55, 9, 56, 57, 10, 58, 11, 12, 13, 14, 59, 60, 15, 61, 62, 63, 16, 64, 65, 17, 66, 18, 19, 20, 67, 21, 22, 23, 68, 69, 24, 25, 26, 70, 71, 27, 72, 28, 29, 30, 31, 73, 32, 74, 33, 75, 34, 35, 36, 76, 77, 78, 37, 38, 79, 39, 80, 81, 40][i.val]!
  if j<41 then .inl (Fin.ofNat 41 j) else .inr (Fin.ofNat 41 (j-41))

def indexing : (Fin 41 ⊕ Fin 41) ≃ Fin 82 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 41,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*81)*(81-1)^40) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 40 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 40 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 40=(2*81)*(81-1)^40 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquaresOpposite


namespace SplitNonsquaresOpposite
def rawWords (i : ℕ) : ℕ := #[424518314332, 694635828908, 866998198803, 237949494851, 913299839877, 1025639122498, 680908445481, 273063313938, 737136321617, 494210453758, 880784601450, 924423331857, 397274154578, 259267874061, 1035074085953, 714750835094, 242301559739, 546946160101, 952175233998, 564310298484, 291877742500, 979130964760, 331940470009, 665202601402, 41688791751, 529422736523, 819853291581, 402122864742, 578767191687, 300878256410, 71252570157, 23046930935, 208498724750, 585033747433, 415475612920, 833488369124, 692807236312, 914931049387, 189690961461, 249454972278, 0][i]!
def words (i : Fin 41) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 81]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 41 rawWords i=rowTotals i)

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
private theorem row37 : rowAgrees 37=true := by decide +kernel
private theorem row38 : rowAgrees 38=true := by decide +kernel
private theorem row39 : rowAgrees 39=true := by decide +kernel
private theorem row40 : rowAgrees 40=true := by decide +kernel
private theorem rowChecked : allBelow 41 rowAgrees=true := by
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
  have h := allBelow_step h row37
  have h := allBelow_step h row38
  have h := allBelow_step h row39
  have h := allBelow_step h row40
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 41, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 41, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(1560:ℤ) := by
  change cubicInteger (fun i : Fin 41 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(1560:ℤ) ∧
    87*(41:ℤ)^3+375*41*(4*41-3)+1000*((wordMatrix words-1)^3).trace-
      1110*81*(41-1)=(6435102:ℤ) ∧ 0≤(6435102:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 41 ⊕ Fin 41 → Fin 82
  | .inl i => Fin.ofNat 82 (#[1, 2, 4, 8, 9, 10, 13, 14, 15, 16, 18, 20, 21, 23, 25, 26, 28, 33, 34, 36, 37, 38, 40, 41, 43, 47, 51, 52, 56, 57, 59, 64, 66, 68, 72, 73, 74, 77, 79, 80, 81][i.val]!)
  | .inr i => Fin.ofNat 82 (#[0, 3, 5, 6, 7, 11, 12, 17, 19, 22, 24, 27, 29, 30, 31, 32, 35, 39, 42, 44, 45, 46, 48, 49, 50, 53, 54, 55, 58, 60, 61, 62, 63, 65, 67, 69, 70, 71, 75, 76, 78][i.val]!)

def pointPosition (i : Fin 82) : Fin 41 ⊕ Fin 41 :=
  let j : ℕ := #[41, 0, 1, 42, 2, 43, 44, 45, 3, 4, 5, 46, 47, 6, 7, 8, 9, 48, 10, 49, 11, 12, 50, 13, 51, 14, 15, 52, 16, 53, 54, 55, 56, 17, 18, 57, 19, 20, 21, 58, 22, 23, 59, 24, 60, 61, 62, 25, 63, 64, 65, 26, 27, 66, 67, 68, 28, 29, 69, 30, 70, 71, 72, 73, 31, 74, 32, 75, 33, 76, 77, 78, 34, 35, 36, 79, 80, 37, 81, 38, 39, 40][i.val]!
  if j<41 then .inl (Fin.ofNat 41 j) else .inr (Fin.ofNat 41 (j-41))

def indexing : (Fin 41 ⊕ Fin 41) ≃ Fin 82 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 41,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*81)*(81-1)^40) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 40 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 40 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 40=(2*81)*(81-1)^40 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquaresOpposite


namespace NonsplitNegativeOpposite
def rawWords (i : ℕ) : ℕ := #[293103900968, 865842701016, 633447662640, 203492525379, 118861009030, 94384777733, 925260776330, 538268558418, 132265940553, 485439521122, 992422498700, 892778242081, 673228899601, 267816831138, 450626788004, 1036772588553, 750281971322, 1043195349971, 845975946470, 398712049055, 694695026251, 289381871382, 829792962277, 342899039600, 669618174440, 164698944385, 1045163448917, 957896489335, 36085513383, 304162001021, 447610808812, 22038927666, 440468016894, 572029873500, 428063145449, 963574856090, 549974619124, 606766098056, 57662164675, 249331948614, 0][i]!
def words (i : Fin 41) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 41 rawWords i=rowTotals i)

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
private theorem row37 : rowAgrees 37=true := by decide +kernel
private theorem row38 : rowAgrees 38=true := by decide +kernel
private theorem row39 : rowAgrees 39=true := by decide +kernel
private theorem row40 : rowAgrees 40=true := by decide +kernel
private theorem rowChecked : allBelow 41 rowAgrees=true := by
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
  have h := allBelow_step h row37
  have h := allBelow_step h row38
  have h := allBelow_step h row39
  have h := allBelow_step h row40
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 41, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 41, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(0:ℤ) := by
  change cubicInteger (fun i : Fin 41 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(0:ℤ) ∧
    87*(41:ℤ)^3+375*41*(4*41-3)+1000*((wordMatrix words-1)^3).trace-
      1110*81*(41-1)=(4875102:ℤ) ∧ 0≤(4875102:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 41 ⊕ Fin 41 → Fin 82
  | .inl i => Fin.ofNat 82 (#[3, 4, 5, 6, 7, 8, 9, 12, 14, 16, 17, 18, 22, 23, 24, 25, 27, 30, 31, 33, 36, 37, 38, 40, 41, 42, 48, 53, 54, 57, 60, 62, 67, 69, 72, 73, 74, 75, 79, 80, 81][i.val]!)
  | .inr i => Fin.ofNat 82 (#[0, 1, 2, 10, 11, 13, 15, 19, 20, 21, 26, 28, 29, 32, 34, 35, 39, 43, 44, 45, 46, 47, 49, 50, 51, 52, 55, 56, 58, 59, 61, 63, 64, 65, 66, 68, 70, 71, 76, 77, 78][i.val]!)

def pointPosition (i : Fin 82) : Fin 41 ⊕ Fin 41 :=
  let j : ℕ := #[41, 42, 43, 0, 1, 2, 3, 4, 5, 6, 44, 45, 7, 46, 8, 47, 9, 10, 11, 48, 49, 50, 12, 13, 14, 15, 51, 16, 52, 53, 17, 18, 54, 19, 55, 56, 20, 21, 22, 57, 23, 24, 25, 58, 59, 60, 61, 62, 26, 63, 64, 65, 66, 27, 28, 67, 68, 29, 69, 70, 30, 71, 31, 72, 73, 74, 75, 32, 76, 33, 77, 78, 34, 35, 36, 37, 79, 80, 81, 38, 39, 40][i.val]!
  if j<41 then .inl (Fin.ofNat 41 j) else .inr (Fin.ofNat 41 (j-41))

def indexing : (Fin 41 ⊕ Fin 41) ≃ Fin 82 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 41,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*81)*(81-1)^40) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 40 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 40 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 40=(2*81)*(81-1)^40 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegativeOpposite

end PaleyBits81
