import Quantum.Hadamard.ConferenceBitCompletion
open Hadamard.BitTrace Hadamard.DeterminantRatio Matrix
set_option maxHeartbeats 12000000
set_option maxRecDepth 60000
namespace PaleyBits97

def rawFull (i : ℕ) : ℕ := #[6380052750319376475725948064, 12760105500638752951451896128, 25520211001277505902903792256, 51040422002555011805807584512, 102080844005110023611615169024, 45705362981691372036142437377, 91410725963382744072284874754, 24365126898236812957481848837, 48730253796473625914963697674, 97460507592947251829927395348, 36464690157365828472766890025, 72929380314731656945533780050, 145858760629463313891067560100, 133261196230397952595047219529, 108066067432267230003006538387, 57675809836005784818925176103, 115351619672011569637850352206, 72246914315494464088612803741, 144493828630988928177225607482, 130531332233449181167363314293, 102606339438369687147638727915, 46756353848210699108189555159, 93512707696421398216379110318, 28569090364314121245670319965, 57138180728628242491340639930, 114276361457256484982681279860, 70096397885984294778274659049, 140192795771968589556549318098, 121929266515408503926010735525, 85402208002288332664933570379, 12348090976047990142779240087, 24696181952095980285558480174, 49392363904191960571116960348, 98784727808383921142233920696, 39113130588239167097379940721, 78226261176478334194759881442, 156452522352956668389519762884, 154448719677384661591951625097, 150441114326240647996815349523, 142425903623952620806542798375, 126395482219376566425997696079, 94334639410224457664907491487, 30212953791920240142727082303, 60425907583840480285454164606, 120851815167680960570908329212, 83247305306833245954728757753, 8038285585137816722369614835, 16076571170275633444739229670, 32153142340551266889478459340, 64306284681102533778956918680, 128612569362205067557913837360, 98768813695881459928739774049, 39081302363234244670391647427, 78162604726468489340783294854, 156325209452936978681566589708, 154194093877345282176045278745, 149931862726161889165002656819, 141407400423795103142917412967, 124358475819061531098746925263, 90260626609594387010405949855, 22064928190660098833723999039, 44129856381320197667447998078, 88259712762640395334895996156, 18063100496752115482704091641, 36126200993504230965408183282, 72252401987008461930816366564, 144504803974016923861632733128, 130553282919505172536177565585, 102650240810481669885267230499, 46844156592434664583446560327, 93688313184869329166893120654, 28920301341209983146698340637, 57840602682419966293396681274, 115681205364839932586793362548, 72906085701151189986498824425, 145812171402302379972997648850, 133168017776076084758907397029, 107879710523623494330726893387, 57303096018718313474365886103, 114606192037436626948731772206, 70756059046344578710375643741, 141512118092689157420751287482, 124567911156849639654414674293, 90679497285170604121741447915, 22902669541812533056394995159, 45805339083625066112789990318, 91610678167250132225579980636, 24765031305971589264072060601, 49530062611943178528144121202, 99060125223886357056288242404, 39663925419244038925488584137, 79327850838488077850977168274, 199376648447480514866435877, 398753296894961029732871754, 797506593789922059465743508, 1595013187579844118931487016, 3190026375159688237862974032, 0][i]!
def fullRows (i : Fin 98) : ℕ := rawFull i.val

private theorem fullSymmetric : (wordMatrix fullRows).IsSymm := by
  have h : ∀ i j : Fin 98, sign (fullRows i) j.val=sign (fullRows j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem fullDiagonal : ∀ i : Fin 98, sign (fullRows i) i.val=1 := by decide +kernel
private theorem lower0 : (lowerRow 98 rawFull) 0=true := by decide +kernel
private theorem lower1 : (lowerRow 98 rawFull) 1=true := by decide +kernel
private theorem lower2 : (lowerRow 98 rawFull) 2=true := by decide +kernel
private theorem lower3 : (lowerRow 98 rawFull) 3=true := by decide +kernel
private theorem lower4 : (lowerRow 98 rawFull) 4=true := by decide +kernel
private theorem lower5 : (lowerRow 98 rawFull) 5=true := by decide +kernel
private theorem lower6 : (lowerRow 98 rawFull) 6=true := by decide +kernel
private theorem lower7 : (lowerRow 98 rawFull) 7=true := by decide +kernel
private theorem lower8 : (lowerRow 98 rawFull) 8=true := by decide +kernel
private theorem lower9 : (lowerRow 98 rawFull) 9=true := by decide +kernel
private theorem lower10 : (lowerRow 98 rawFull) 10=true := by decide +kernel
private theorem lower11 : (lowerRow 98 rawFull) 11=true := by decide +kernel
private theorem lower12 : (lowerRow 98 rawFull) 12=true := by decide +kernel
private theorem lower13 : (lowerRow 98 rawFull) 13=true := by decide +kernel
private theorem lower14 : (lowerRow 98 rawFull) 14=true := by decide +kernel
private theorem lower15 : (lowerRow 98 rawFull) 15=true := by decide +kernel
private theorem lower16 : (lowerRow 98 rawFull) 16=true := by decide +kernel
private theorem lower17 : (lowerRow 98 rawFull) 17=true := by decide +kernel
private theorem lower18 : (lowerRow 98 rawFull) 18=true := by decide +kernel
private theorem lower19 : (lowerRow 98 rawFull) 19=true := by decide +kernel
private theorem lower20 : (lowerRow 98 rawFull) 20=true := by decide +kernel
private theorem lower21 : (lowerRow 98 rawFull) 21=true := by decide +kernel
private theorem lower22 : (lowerRow 98 rawFull) 22=true := by decide +kernel
private theorem lower23 : (lowerRow 98 rawFull) 23=true := by decide +kernel
private theorem lower24 : (lowerRow 98 rawFull) 24=true := by decide +kernel
private theorem lower25 : (lowerRow 98 rawFull) 25=true := by decide +kernel
private theorem lower26 : (lowerRow 98 rawFull) 26=true := by decide +kernel
private theorem lower27 : (lowerRow 98 rawFull) 27=true := by decide +kernel
private theorem lower28 : (lowerRow 98 rawFull) 28=true := by decide +kernel
private theorem lower29 : (lowerRow 98 rawFull) 29=true := by decide +kernel
private theorem lower30 : (lowerRow 98 rawFull) 30=true := by decide +kernel
private theorem lower31 : (lowerRow 98 rawFull) 31=true := by decide +kernel
private theorem lower32 : (lowerRow 98 rawFull) 32=true := by decide +kernel
private theorem lower33 : (lowerRow 98 rawFull) 33=true := by decide +kernel
private theorem lower34 : (lowerRow 98 rawFull) 34=true := by decide +kernel
private theorem lower35 : (lowerRow 98 rawFull) 35=true := by decide +kernel
private theorem lower36 : (lowerRow 98 rawFull) 36=true := by decide +kernel
private theorem lower37 : (lowerRow 98 rawFull) 37=true := by decide +kernel
private theorem lower38 : (lowerRow 98 rawFull) 38=true := by decide +kernel
private theorem lower39 : (lowerRow 98 rawFull) 39=true := by decide +kernel
private theorem lower40 : (lowerRow 98 rawFull) 40=true := by decide +kernel
private theorem lower41 : (lowerRow 98 rawFull) 41=true := by decide +kernel
private theorem lower42 : (lowerRow 98 rawFull) 42=true := by decide +kernel
private theorem lower43 : (lowerRow 98 rawFull) 43=true := by decide +kernel
private theorem lower44 : (lowerRow 98 rawFull) 44=true := by decide +kernel
private theorem lower45 : (lowerRow 98 rawFull) 45=true := by decide +kernel
private theorem lower46 : (lowerRow 98 rawFull) 46=true := by decide +kernel
private theorem lower47 : (lowerRow 98 rawFull) 47=true := by decide +kernel
private theorem lower48 : (lowerRow 98 rawFull) 48=true := by decide +kernel
private theorem lower49 : (lowerRow 98 rawFull) 49=true := by decide +kernel
private theorem lower50 : (lowerRow 98 rawFull) 50=true := by decide +kernel
private theorem lower51 : (lowerRow 98 rawFull) 51=true := by decide +kernel
private theorem lower52 : (lowerRow 98 rawFull) 52=true := by decide +kernel
private theorem lower53 : (lowerRow 98 rawFull) 53=true := by decide +kernel
private theorem lower54 : (lowerRow 98 rawFull) 54=true := by decide +kernel
private theorem lower55 : (lowerRow 98 rawFull) 55=true := by decide +kernel
private theorem lower56 : (lowerRow 98 rawFull) 56=true := by decide +kernel
private theorem lower57 : (lowerRow 98 rawFull) 57=true := by decide +kernel
private theorem lower58 : (lowerRow 98 rawFull) 58=true := by decide +kernel
private theorem lower59 : (lowerRow 98 rawFull) 59=true := by decide +kernel
private theorem lower60 : (lowerRow 98 rawFull) 60=true := by decide +kernel
private theorem lower61 : (lowerRow 98 rawFull) 61=true := by decide +kernel
private theorem lower62 : (lowerRow 98 rawFull) 62=true := by decide +kernel
private theorem lower63 : (lowerRow 98 rawFull) 63=true := by decide +kernel
private theorem lower64 : (lowerRow 98 rawFull) 64=true := by decide +kernel
private theorem lower65 : (lowerRow 98 rawFull) 65=true := by decide +kernel
private theorem lower66 : (lowerRow 98 rawFull) 66=true := by decide +kernel
private theorem lower67 : (lowerRow 98 rawFull) 67=true := by decide +kernel
private theorem lower68 : (lowerRow 98 rawFull) 68=true := by decide +kernel
private theorem lower69 : (lowerRow 98 rawFull) 69=true := by decide +kernel
private theorem lower70 : (lowerRow 98 rawFull) 70=true := by decide +kernel
private theorem lower71 : (lowerRow 98 rawFull) 71=true := by decide +kernel
private theorem lower72 : (lowerRow 98 rawFull) 72=true := by decide +kernel
private theorem lower73 : (lowerRow 98 rawFull) 73=true := by decide +kernel
private theorem lower74 : (lowerRow 98 rawFull) 74=true := by decide +kernel
private theorem lower75 : (lowerRow 98 rawFull) 75=true := by decide +kernel
private theorem lower76 : (lowerRow 98 rawFull) 76=true := by decide +kernel
private theorem lower77 : (lowerRow 98 rawFull) 77=true := by decide +kernel
private theorem lower78 : (lowerRow 98 rawFull) 78=true := by decide +kernel
private theorem lower79 : (lowerRow 98 rawFull) 79=true := by decide +kernel
private theorem lower80 : (lowerRow 98 rawFull) 80=true := by decide +kernel
private theorem lower81 : (lowerRow 98 rawFull) 81=true := by decide +kernel
private theorem lower82 : (lowerRow 98 rawFull) 82=true := by decide +kernel
private theorem lower83 : (lowerRow 98 rawFull) 83=true := by decide +kernel
private theorem lower84 : (lowerRow 98 rawFull) 84=true := by decide +kernel
private theorem lower85 : (lowerRow 98 rawFull) 85=true := by decide +kernel
private theorem lower86 : (lowerRow 98 rawFull) 86=true := by decide +kernel
private theorem lower87 : (lowerRow 98 rawFull) 87=true := by decide +kernel
private theorem lower88 : (lowerRow 98 rawFull) 88=true := by decide +kernel
private theorem lower89 : (lowerRow 98 rawFull) 89=true := by decide +kernel
private theorem lower90 : (lowerRow 98 rawFull) 90=true := by decide +kernel
private theorem lower91 : (lowerRow 98 rawFull) 91=true := by decide +kernel
private theorem lower92 : (lowerRow 98 rawFull) 92=true := by decide +kernel
private theorem lower93 : (lowerRow 98 rawFull) 93=true := by decide +kernel
private theorem lower94 : (lowerRow 98 rawFull) 94=true := by decide +kernel
private theorem lower95 : (lowerRow 98 rawFull) 95=true := by decide +kernel
private theorem lower96 : (lowerRow 98 rawFull) 96=true := by decide +kernel
private theorem lower97 : (lowerRow 98 rawFull) 97=true := by decide +kernel
private theorem lowerChecked : allBelow 98 (lowerRow 98 rawFull)=true := by
  have h : allBelow 0 (lowerRow 98 rawFull)=true := rfl
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
  have h := allBelow_step h lower82
  have h := allBelow_step h lower83
  have h := allBelow_step h lower84
  have h := allBelow_step h lower85
  have h := allBelow_step h lower86
  have h := allBelow_step h lower87
  have h := allBelow_step h lower88
  have h := allBelow_step h lower89
  have h := allBelow_step h lower90
  have h := allBelow_step h lower91
  have h := allBelow_step h lower92
  have h := allBelow_step h lower93
  have h := allBelow_step h lower94
  have h := allBelow_step h lower95
  have h := allBelow_step h lower96
  have h := allBelow_step h lower97
  exact h

private theorem fullPairs : ∀ i j : Fin 98, i≠j →
    correlation 98 (fullRows i) (fullRows j)=2*sign (fullRows i) j.val :=
  correlations_of_lower rawFull fullSymmetric lowerChecked


namespace SplitSquares
def rawWords (i : ℕ) : ℕ := #[0, 59290558250336, 82830490293888, 180107094735936, 376827116185984, 332275346228482, 166454134691850, 346396488774676, 278478415162418, 508990636150788, 388645087150510, 505451109106010, 345044338508494, 194510426538394, 393109117209460, 496273501327986, 103479541509966, 171654449781692, 349079869591064, 266879453126306, 550545251177572, 226064749310142, 434984389307452, 52462757521638, 122051833485804, 244567523328984, 453366014392272, 264836293781318, 549964703688396, 167821850948798, 305561215595836, 107477647031026, 272043318304996, 505569906713064, 344289122413326, 205889096091290, 393634239192116, 506898258079346, 398073910310734, 516782963587610, 140942604819918, 335192196221692, 176683541283698, 352316836748196, 284281706328530, 6999078892970, 9842374332180, 6233045773128, 29645279125168][i]!
def words (i : Fin 49) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[97, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 49 rawWords i=rowTotals i)

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
private theorem row41 : rowAgrees 41=true := by decide +kernel
private theorem row42 : rowAgrees 42=true := by decide +kernel
private theorem row43 : rowAgrees 43=true := by decide +kernel
private theorem row44 : rowAgrees 44=true := by decide +kernel
private theorem row45 : rowAgrees 45=true := by decide +kernel
private theorem row46 : rowAgrees 46=true := by decide +kernel
private theorem row47 : rowAgrees 47=true := by decide +kernel
private theorem row48 : rowAgrees 48=true := by decide +kernel
private theorem rowChecked : allBelow 49 rowAgrees=true := by
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
  have h := allBelow_step h row41
  have h := allBelow_step h row42
  have h := allBelow_step h row43
  have h := allBelow_step h row44
  have h := allBelow_step h row45
  have h := allBelow_step h row46
  have h := allBelow_step h row47
  have h := allBelow_step h row48
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 49, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 49, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(1488:ℤ) := by
  change cubicInteger (fun i : Fin 49 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(1488:ℤ) ∧
    87*(49:ℤ)^3+375*49*(4*49-3)+1000*((wordMatrix words-1)^3).trace-
      1110*97*(49-1)=(10101678:ℤ) ∧ 0≤(10101678:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 49 ⊕ Fin 49 → Fin 98
  | .inl i => Fin.ofNat 98 (#[0, 1, 2, 3, 4, 6, 8, 9, 11, 12, 16, 18, 22, 24, 25, 27, 31, 32, 33, 35, 36, 43, 44, 47, 48, 49, 50, 53, 54, 61, 62, 64, 65, 66, 70, 72, 73, 75, 79, 81, 85, 86, 88, 89, 91, 93, 94, 95, 96][i.val]!)
  | .inr i => Fin.ofNat 98 (#[5, 7, 10, 13, 14, 15, 17, 19, 20, 21, 23, 26, 28, 29, 30, 34, 37, 38, 39, 40, 41, 42, 45, 46, 51, 52, 55, 56, 57, 58, 59, 60, 63, 67, 68, 69, 71, 74, 76, 77, 78, 80, 82, 83, 84, 87, 90, 92, 97][i.val]!)

def pointPosition (i : Fin 98) : Fin 49 ⊕ Fin 49 :=
  let j : ℕ := #[0, 1, 2, 3, 4, 49, 5, 50, 6, 7, 51, 8, 9, 52, 53, 54, 10, 55, 11, 56, 57, 58, 12, 59, 13, 14, 60, 15, 61, 62, 63, 16, 17, 18, 64, 19, 20, 65, 66, 67, 68, 69, 70, 21, 22, 71, 72, 23, 24, 25, 26, 73, 74, 27, 28, 75, 76, 77, 78, 79, 80, 29, 30, 81, 31, 32, 33, 82, 83, 84, 34, 85, 35, 36, 86, 37, 87, 88, 89, 38, 90, 39, 91, 92, 93, 40, 41, 94, 42, 43, 95, 44, 96, 45, 46, 47, 48, 97][i.val]!
  if j<49 then .inl (Fin.ofNat 49 j) else .inr (Fin.ofNat 49 (j-49))

def indexing : (Fin 49 ⊕ Fin 49) ≃ Fin 98 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 49,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*97)*(97-1)^48) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 48 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 48 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 48=(2*97)*(97-1)^48 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquares


namespace SplitNonsquares
def rawWords (i : ℕ) : ℕ := #[562949953421310, 379104747139913, 266935533221537, 531184880503491, 260278481172993, 450188243330309, 345681460322827, 41622454108173, 224171269115939, 96352780124255, 465676635811877, 455589315911705, 65073548100887, 127940413361271, 391971286352233, 220717607160541, 427620536174579, 312155912047269, 201815924682185, 184296325337883, 298361320153001, 385058229794389, 137072740560179, 273133279162823, 409944195619463, 428158061358267, 437831664031869, 337382582080761, 186582026596843, 96636836998083, 390507061503893, 86655358519221, 164119453605731, 351329689230471, 260864052491341, 98965892495515, 484612387694777, 460147610866545, 105646189144551, 158547531761559, 536593653700521, 299251514875725, 211139107319441, 353074580461939, 143602934495847, 1607824340189, 296098834998047, 23867511639357, 82679449209963][i]!
def words (i : Fin 49) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[193, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 49 rawWords i=rowTotals i)

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
private theorem row41 : rowAgrees 41=true := by decide +kernel
private theorem row42 : rowAgrees 42=true := by decide +kernel
private theorem row43 : rowAgrees 43=true := by decide +kernel
private theorem row44 : rowAgrees 44=true := by decide +kernel
private theorem row45 : rowAgrees 45=true := by decide +kernel
private theorem row46 : rowAgrees 46=true := by decide +kernel
private theorem row47 : rowAgrees 47=true := by decide +kernel
private theorem row48 : rowAgrees 48=true := by decide +kernel
private theorem rowChecked : allBelow 49 rowAgrees=true := by
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
  have h := allBelow_step h row41
  have h := allBelow_step h row42
  have h := allBelow_step h row43
  have h := allBelow_step h row44
  have h := allBelow_step h row45
  have h := allBelow_step h row46
  have h := allBelow_step h row47
  have h := allBelow_step h row48
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 49, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 49, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-1488:ℤ) := by
  change cubicInteger (fun i : Fin 49 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-1488:ℤ) ∧
    87*(49:ℤ)^3+375*49*(4*49-3)+1000*((wordMatrix words-1)^3).trace-
      1110*97*(49-1)=(7125678:ℤ) ∧ 0≤(7125678:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 49 ⊕ Fin 49 → Fin 98
  | .inl i => Fin.ofNat 98 (#[0, 5, 7, 10, 13, 14, 15, 17, 19, 20, 21, 23, 26, 28, 29, 30, 34, 37, 38, 39, 40, 41, 42, 45, 46, 51, 52, 55, 56, 57, 58, 59, 60, 63, 67, 68, 69, 71, 74, 76, 77, 78, 80, 82, 83, 84, 87, 90, 92][i.val]!)
  | .inr i => Fin.ofNat 98 (#[1, 2, 3, 4, 6, 8, 9, 11, 12, 16, 18, 22, 24, 25, 27, 31, 32, 33, 35, 36, 43, 44, 47, 48, 49, 50, 53, 54, 61, 62, 64, 65, 66, 70, 72, 73, 75, 79, 81, 85, 86, 88, 89, 91, 93, 94, 95, 96, 97][i.val]!)

def pointPosition (i : Fin 98) : Fin 49 ⊕ Fin 49 :=
  let j : ℕ := #[0, 49, 50, 51, 52, 1, 53, 2, 54, 55, 3, 56, 57, 4, 5, 6, 58, 7, 59, 8, 9, 10, 60, 11, 61, 62, 12, 63, 13, 14, 15, 64, 65, 66, 16, 67, 68, 17, 18, 19, 20, 21, 22, 69, 70, 23, 24, 71, 72, 73, 74, 25, 26, 75, 76, 27, 28, 29, 30, 31, 32, 77, 78, 33, 79, 80, 81, 34, 35, 36, 82, 37, 83, 84, 38, 85, 39, 40, 41, 86, 42, 87, 43, 44, 45, 88, 89, 46, 90, 91, 47, 92, 48, 93, 94, 95, 96, 97][i.val]!
  if j<49 then .inl (Fin.ofNat 49 j) else .inr (Fin.ofNat 49 (j-49))

def indexing : (Fin 49 ⊕ Fin 49) ≃ Fin 98 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 49,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*97)*(97-1)^48) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 48 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 48 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 48=(2*97)*(97-1)^48 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquares


namespace NonsplitNegative
def rawWords (i : ℕ) : ℕ := #[296200756828866, 517551695015073, 418671330981056, 476463128678656, 234946778440960, 531740819710466, 157355190148101, 470841063942151, 308638245425176, 133542693912609, 477641594056790, 213109357568195, 325068604441933, 386254292651190, 66620070562404, 557652576043437, 251084556732214, 519763679780194, 476869531060951, 320446358629802, 358901803488196, 87535628382567, 66689434198935, 414733384810287, 268714361482268, 247251607525564, 514567693480571, 465171808752881, 451058564130761, 157393466644874, 376926790630162, 472016967611959, 311024458429550, 478838099339420, 235298565247871, 168502676923632, 480213291977706, 222656303372179, 294779830742541, 466413154621750, 17638032718457, 105722704082018, 422577158844631, 141741183394757, 282709071423262, 2828434003628, 2354845035062, 14013388262650, 22900172043695][i]!
def words (i : Fin 49) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 49 rawWords i=rowTotals i)

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
private theorem row41 : rowAgrees 41=true := by decide +kernel
private theorem row42 : rowAgrees 42=true := by decide +kernel
private theorem row43 : rowAgrees 43=true := by decide +kernel
private theorem row44 : rowAgrees 44=true := by decide +kernel
private theorem row45 : rowAgrees 45=true := by decide +kernel
private theorem row46 : rowAgrees 46=true := by decide +kernel
private theorem row47 : rowAgrees 47=true := by decide +kernel
private theorem row48 : rowAgrees 48=true := by decide +kernel
private theorem rowChecked : allBelow 49 rowAgrees=true := by
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
  have h := allBelow_step h row41
  have h := allBelow_step h row42
  have h := allBelow_step h row43
  have h := allBelow_step h row44
  have h := allBelow_step h row45
  have h := allBelow_step h row46
  have h := allBelow_step h row47
  have h := allBelow_step h row48
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 49, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 49, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-1764:ℤ) := by
  change cubicInteger (fun i : Fin 49 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-1764:ℤ) ∧
    87*(49:ℤ)^3+375*49*(4*49-3)+1000*((wordMatrix words-1)^3).trace-
      1110*97*(49-1)=(6849678:ℤ) ∧ 0≤(6849678:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 49 ⊕ Fin 49 → Fin 98
  | .inl i => Fin.ofNat 98 (#[0, 5, 8, 9, 11, 12, 13, 15, 16, 17, 18, 20, 23, 25, 27, 29, 31, 33, 34, 35, 36, 42, 45, 46, 48, 49, 51, 52, 55, 61, 62, 63, 64, 66, 68, 70, 72, 74, 77, 79, 80, 81, 82, 84, 85, 86, 88, 89, 92][i.val]!)
  | .inr i => Fin.ofNat 98 (#[1, 2, 3, 4, 6, 7, 10, 14, 19, 21, 22, 24, 26, 28, 30, 32, 37, 38, 39, 40, 41, 43, 44, 47, 50, 53, 54, 56, 57, 58, 59, 60, 65, 67, 69, 71, 73, 75, 76, 78, 83, 87, 90, 91, 93, 94, 95, 96, 97][i.val]!)

def pointPosition (i : Fin 98) : Fin 49 ⊕ Fin 49 :=
  let j : ℕ := #[0, 49, 50, 51, 52, 1, 53, 54, 2, 3, 55, 4, 5, 6, 56, 7, 8, 9, 10, 57, 11, 58, 59, 12, 60, 13, 61, 14, 62, 15, 63, 16, 64, 17, 18, 19, 20, 65, 66, 67, 68, 69, 21, 70, 71, 22, 23, 72, 24, 25, 73, 26, 27, 74, 75, 28, 76, 77, 78, 79, 80, 29, 30, 31, 32, 81, 33, 82, 34, 83, 35, 84, 36, 85, 37, 86, 87, 38, 88, 39, 40, 41, 42, 89, 43, 44, 45, 90, 46, 47, 91, 92, 48, 93, 94, 95, 96, 97][i.val]!
  if j<49 then .inl (Fin.ofNat 49 j) else .inr (Fin.ofNat 49 (j-49))

def indexing : (Fin 49 ⊕ Fin 49) ≃ Fin 98 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 49,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*97)*(97-1)^48) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 48 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 48 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 48=(2*97)*(97-1)^48 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegative


namespace SplitSquaresOpposite
def rawWords (i : ℕ) : ℕ := #[189552373569956, 133467766610768, 265592440251745, 130139240586496, 225094121665154, 172840730161413, 20811227054086, 112085634557969, 48176390062127, 232838317905938, 227794657955852, 32536774050443, 63970206680635, 195985643176116, 110358803580270, 213810268087289, 156077956023634, 100907962341092, 92148162668941, 149180660076500, 192529114897194, 68536370280089, 136566639581411, 204972097809731, 214079030679133, 218915832015934, 168691291040380, 93291013298421, 48318418499041, 195253530751946, 43327679259610, 82059726802865, 175664844615235, 130432026245670, 49482946247757, 242306193847388, 230073805433272, 52823094572275, 79273765880779, 268296826850260, 149625757437862, 105569553659720, 176537290230969, 71801467247923, 803912170094, 148049417499023, 11933755819678, 41339724604981, 0][i]!
def words (i : Fin 49) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 193]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 49 rawWords i=rowTotals i)

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
private theorem row41 : rowAgrees 41=true := by decide +kernel
private theorem row42 : rowAgrees 42=true := by decide +kernel
private theorem row43 : rowAgrees 43=true := by decide +kernel
private theorem row44 : rowAgrees 44=true := by decide +kernel
private theorem row45 : rowAgrees 45=true := by decide +kernel
private theorem row46 : rowAgrees 46=true := by decide +kernel
private theorem row47 : rowAgrees 47=true := by decide +kernel
private theorem row48 : rowAgrees 48=true := by decide +kernel
private theorem rowChecked : allBelow 49 rowAgrees=true := by
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
  have h := allBelow_step h row41
  have h := allBelow_step h row42
  have h := allBelow_step h row43
  have h := allBelow_step h row44
  have h := allBelow_step h row45
  have h := allBelow_step h row46
  have h := allBelow_step h row47
  have h := allBelow_step h row48
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 49, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 49, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-1488:ℤ) := by
  change cubicInteger (fun i : Fin 49 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-1488:ℤ) ∧
    87*(49:ℤ)^3+375*49*(4*49-3)+1000*((wordMatrix words-1)^3).trace-
      1110*97*(49-1)=(7125678:ℤ) ∧ 0≤(7125678:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 49 ⊕ Fin 49 → Fin 98
  | .inl i => Fin.ofNat 98 (#[5, 7, 10, 13, 14, 15, 17, 19, 20, 21, 23, 26, 28, 29, 30, 34, 37, 38, 39, 40, 41, 42, 45, 46, 51, 52, 55, 56, 57, 58, 59, 60, 63, 67, 68, 69, 71, 74, 76, 77, 78, 80, 82, 83, 84, 87, 90, 92, 97][i.val]!)
  | .inr i => Fin.ofNat 98 (#[0, 1, 2, 3, 4, 6, 8, 9, 11, 12, 16, 18, 22, 24, 25, 27, 31, 32, 33, 35, 36, 43, 44, 47, 48, 49, 50, 53, 54, 61, 62, 64, 65, 66, 70, 72, 73, 75, 79, 81, 85, 86, 88, 89, 91, 93, 94, 95, 96][i.val]!)

def pointPosition (i : Fin 98) : Fin 49 ⊕ Fin 49 :=
  let j : ℕ := #[49, 50, 51, 52, 53, 0, 54, 1, 55, 56, 2, 57, 58, 3, 4, 5, 59, 6, 60, 7, 8, 9, 61, 10, 62, 63, 11, 64, 12, 13, 14, 65, 66, 67, 15, 68, 69, 16, 17, 18, 19, 20, 21, 70, 71, 22, 23, 72, 73, 74, 75, 24, 25, 76, 77, 26, 27, 28, 29, 30, 31, 78, 79, 32, 80, 81, 82, 33, 34, 35, 83, 36, 84, 85, 37, 86, 38, 39, 40, 87, 41, 88, 42, 43, 44, 89, 90, 45, 91, 92, 46, 93, 47, 94, 95, 96, 97, 48][i.val]!
  if j<49 then .inl (Fin.ofNat 49 j) else .inr (Fin.ofNat 49 (j-49))

def indexing : (Fin 49 ⊕ Fin 49) ≃ Fin 98 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 49,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*97)*(97-1)^48) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 48 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 48 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 48=(2*97)*(97-1)^48 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquaresOpposite


namespace SplitNonsquaresOpposite
def rawWords (i : ℕ) : ℕ := #[29645279125168, 41415245146944, 90053547367968, 188413558092992, 166137673114241, 83227067345925, 173198244387338, 139239207581209, 254495318075394, 194322543575255, 252725554553005, 172522169254247, 97255213269197, 196554558604730, 248136750663993, 51739770754983, 85827224890846, 174539934795532, 133439726563153, 275272625588786, 113032374655071, 217492194653726, 26231378760819, 61025916742902, 122283761664492, 226683007196136, 132418146890659, 274982351844198, 83910925474399, 152780607797918, 53738823515513, 136021659152498, 252784953356532, 172144561206663, 102944548045645, 196817119596058, 253449129039673, 199036955155367, 258391481793805, 70471302409959, 167596098110846, 88341770641849, 176158418374098, 142140853164265, 3499539446485, 4921187166090, 3116522886564, 14822639562584, 0][i]!
def words (i : Fin 49) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 97]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 49 rawWords i=rowTotals i)

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
private theorem row41 : rowAgrees 41=true := by decide +kernel
private theorem row42 : rowAgrees 42=true := by decide +kernel
private theorem row43 : rowAgrees 43=true := by decide +kernel
private theorem row44 : rowAgrees 44=true := by decide +kernel
private theorem row45 : rowAgrees 45=true := by decide +kernel
private theorem row46 : rowAgrees 46=true := by decide +kernel
private theorem row47 : rowAgrees 47=true := by decide +kernel
private theorem row48 : rowAgrees 48=true := by decide +kernel
private theorem rowChecked : allBelow 49 rowAgrees=true := by
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
  have h := allBelow_step h row41
  have h := allBelow_step h row42
  have h := allBelow_step h row43
  have h := allBelow_step h row44
  have h := allBelow_step h row45
  have h := allBelow_step h row46
  have h := allBelow_step h row47
  have h := allBelow_step h row48
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 49, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 49, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(1488:ℤ) := by
  change cubicInteger (fun i : Fin 49 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(1488:ℤ) ∧
    87*(49:ℤ)^3+375*49*(4*49-3)+1000*((wordMatrix words-1)^3).trace-
      1110*97*(49-1)=(10101678:ℤ) ∧ 0≤(10101678:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 49 ⊕ Fin 49 → Fin 98
  | .inl i => Fin.ofNat 98 (#[1, 2, 3, 4, 6, 8, 9, 11, 12, 16, 18, 22, 24, 25, 27, 31, 32, 33, 35, 36, 43, 44, 47, 48, 49, 50, 53, 54, 61, 62, 64, 65, 66, 70, 72, 73, 75, 79, 81, 85, 86, 88, 89, 91, 93, 94, 95, 96, 97][i.val]!)
  | .inr i => Fin.ofNat 98 (#[0, 5, 7, 10, 13, 14, 15, 17, 19, 20, 21, 23, 26, 28, 29, 30, 34, 37, 38, 39, 40, 41, 42, 45, 46, 51, 52, 55, 56, 57, 58, 59, 60, 63, 67, 68, 69, 71, 74, 76, 77, 78, 80, 82, 83, 84, 87, 90, 92][i.val]!)

def pointPosition (i : Fin 98) : Fin 49 ⊕ Fin 49 :=
  let j : ℕ := #[49, 0, 1, 2, 3, 50, 4, 51, 5, 6, 52, 7, 8, 53, 54, 55, 9, 56, 10, 57, 58, 59, 11, 60, 12, 13, 61, 14, 62, 63, 64, 15, 16, 17, 65, 18, 19, 66, 67, 68, 69, 70, 71, 20, 21, 72, 73, 22, 23, 24, 25, 74, 75, 26, 27, 76, 77, 78, 79, 80, 81, 28, 29, 82, 30, 31, 32, 83, 84, 85, 33, 86, 34, 35, 87, 36, 88, 89, 90, 37, 91, 38, 92, 93, 94, 39, 40, 95, 41, 42, 96, 43, 97, 44, 45, 46, 47, 48][i.val]!
  if j<49 then .inl (Fin.ofNat 49 j) else .inr (Fin.ofNat 49 (j-49))

def indexing : (Fin 49 ⊕ Fin 49) ≃ Fin 98 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 49,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*97)*(97-1)^48) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 48 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 48 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 48=(2*97)*(97-1)^48 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquaresOpposite


namespace NonsplitNegativeOpposite
def rawWords (i : ℕ) : ℕ := #[28196372106896, 36137703630624, 95695704529984, 187719220382592, 164055686353665, 52653661978242, 60022332475396, 190343528655657, 236300419373210, 75672522993851, 172154254884903, 100490020323821, 124844175524660, 223300662985378, 24665660129387, 87534160119070, 265994803137700, 270352926124873, 260412159335747, 220472876749783, 162378419289647, 106776024480927, 217237097368318, 20283319253875, 227459591654984, 139992851466659, 274045771528326, 268813416625609, 259252848107795, 214099866151735, 161439302961071, 40901036332943, 132631295769074, 235298035824232, 76142476060883, 49204172018062, 201764408436442, 250695841433913, 243045144939298, 97965811144555, 163640778143925, 35263620376940, 72011758356468, 141601163488425, 2007068007765, 2446489751786, 5391248243460, 10387334309272, 0][i]!
def words (i : Fin 49) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 49 rawWords i=rowTotals i)

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
private theorem row41 : rowAgrees 41=true := by decide +kernel
private theorem row42 : rowAgrees 42=true := by decide +kernel
private theorem row43 : rowAgrees 43=true := by decide +kernel
private theorem row44 : rowAgrees 44=true := by decide +kernel
private theorem row45 : rowAgrees 45=true := by decide +kernel
private theorem row46 : rowAgrees 46=true := by decide +kernel
private theorem row47 : rowAgrees 47=true := by decide +kernel
private theorem row48 : rowAgrees 48=true := by decide +kernel
private theorem rowChecked : allBelow 49 rowAgrees=true := by
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
  have h := allBelow_step h row41
  have h := allBelow_step h row42
  have h := allBelow_step h row43
  have h := allBelow_step h row44
  have h := allBelow_step h row45
  have h := allBelow_step h row46
  have h := allBelow_step h row47
  have h := allBelow_step h row48
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 49, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 49, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(1764:ℤ) := by
  change cubicInteger (fun i : Fin 49 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(1764:ℤ) ∧
    87*(49:ℤ)^3+375*49*(4*49-3)+1000*((wordMatrix words-1)^3).trace-
      1110*97*(49-1)=(10377678:ℤ) ∧ 0≤(10377678:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 49 ⊕ Fin 49 → Fin 98
  | .inl i => Fin.ofNat 98 (#[1, 2, 3, 4, 6, 7, 10, 14, 19, 21, 22, 24, 26, 28, 30, 32, 37, 38, 39, 40, 41, 43, 44, 47, 50, 53, 54, 56, 57, 58, 59, 60, 65, 67, 69, 71, 73, 75, 76, 78, 83, 87, 90, 91, 93, 94, 95, 96, 97][i.val]!)
  | .inr i => Fin.ofNat 98 (#[0, 5, 8, 9, 11, 12, 13, 15, 16, 17, 18, 20, 23, 25, 27, 29, 31, 33, 34, 35, 36, 42, 45, 46, 48, 49, 51, 52, 55, 61, 62, 63, 64, 66, 68, 70, 72, 74, 77, 79, 80, 81, 82, 84, 85, 86, 88, 89, 92][i.val]!)

def pointPosition (i : Fin 98) : Fin 49 ⊕ Fin 49 :=
  let j : ℕ := #[49, 0, 1, 2, 3, 50, 4, 5, 51, 52, 6, 53, 54, 55, 7, 56, 57, 58, 59, 8, 60, 9, 10, 61, 11, 62, 12, 63, 13, 64, 14, 65, 15, 66, 67, 68, 69, 16, 17, 18, 19, 20, 70, 21, 22, 71, 72, 23, 73, 74, 24, 75, 76, 25, 26, 77, 27, 28, 29, 30, 31, 78, 79, 80, 81, 32, 82, 33, 83, 34, 84, 35, 85, 36, 86, 37, 38, 87, 39, 88, 89, 90, 91, 40, 92, 93, 94, 41, 95, 96, 42, 43, 97, 44, 45, 46, 47, 48][i.val]!
  if j<49 then .inl (Fin.ofNat 49 j) else .inr (Fin.ofNat 49 (j-49))

def indexing : (Fin 49 ⊕ Fin 49) ≃ Fin 98 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 49,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*97)*(97-1)^48) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 48 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 48 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 48=(2*97)*(97-1)^48 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegativeOpposite

end PaleyBits97
