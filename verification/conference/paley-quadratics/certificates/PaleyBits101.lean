import Quantum.Hadamard.ConferenceBitCompletion
open Hadamard.BitTrace Hadamard.DeterminantRatio Matrix
set_option maxHeartbeats 12000000
set_option maxRecDepth 60000
namespace PaleyBits101

def rawFull (i : ℕ) : ℕ := #[984868415575749434490170416524, 1969736831151498868980340833048, 1404172461846538934967275255345, 273043723236619066941144099939, 546087446473238133882288199878, 1092174892946476267764576399756, 2184349785892952535529152799512, 1833398371329446268064899188273, 1131495542202433733136391965795, 2262991084404867466272783931590, 1990680968353276129552161452429, 1446060736250093456110916494107, 356820272043728109228426577463, 713640544087456218456853154926, 1427281088174912436913706309852, 319260975893366070834006208953, 638521951786732141668012417906, 1277043903573464283336024835812, 18786606690469763678643260873, 37573213380939527357286521746, 75146426761879054714573043492, 150292853523758109429146086984, 300585707047516218858292173968, 601171414095032437716584347936, 1202342828190064875433168695872, 2404685656380129750866337391744, 2274070112303800698739268372737, 2012839024151142594485130334723, 1490376847845826385976854258695, 445452495235193968960302106639, 890904990470387937920604213278, 1781809980940775875841208426556, 1028318761425092948689010442361, 2056637522850185897378020884722, 1577973845243912991762635358693, 620646490031367180531864306635, 1241292980062734361063728613270, 2482585960125468722127457226540, 2429870719794478641261508042329, 2324440239132498479529609673907, 2113579277808538156065812937063, 1691857355160617509138219463375, 848413509864776215283032515999, 1696827019729552430566065031998, 858352839002646058138723653245, 1716705678005292116277447306490, 898110155554125429561488202229, 1796220311108250859122976404458, 1057139421760042915252546398165, 2114278843520085830505092796330, 1693256486583712858016779181909, 851211772710966913040151953067, 1702423545421933826080303906134, 869545890387408849167201401517, 1739091780774817698334402803034, 942882361093176593675399195317, 1885764722186353187350798390634, 1236228243916247571708190370517, 2472456487832495143416380741034, 2409611775208531483839355071317, 2283922349960604164685303731883, 2032543499464749526377201053015, 1529785798473040249760995695279, 524270396489621696528584979807, 1048540792979243393057169959614, 2097081585958486786114339919228, 1658861971460514769235273427705, 782422742464570735477140444659, 1564845484929141470954280889318, 594389769401824138915155367885, 1188779538803648277830310735770, 2377559077607296555660621471540, 2219816954758134308327836532329, 1904332709059809813662266653907, 1273364217663160824331126897063, 11427234869862845668847383375, 22854469739725691337694766750, 45708939479451382675389533500, 91417878958902765350779067000, 182835757917805530701558134000, 365671515835611061403116268000, 731343031671222122806232536000, 1462686063342444245612465072000, 390070926228429688231523733249, 780141852456859376463047466498, 1560283704913718752926094932996, 585266209370978702858783455241, 1170532418741957405717566910482, 2341064837483914811435133820964, 2146828474511370819876861231177, 1758355748566282836760316051603, 981410296676106870527225692455, 1962820593352213741054451384910, 1390339986247968679115496359069, 245378772039478555237586307387, 490757544078957110475172614774, 981515088157914220950345229548, 1963030176315828441900690459096, 1390759152175198080807974507441, 246217103893937358622542604131, 492434207787874717245085208262, 0][i]!
def fullRows (i : Fin 102) : ℕ := rawFull i.val

private theorem fullSymmetric : (wordMatrix fullRows).IsSymm := by
  have h : ∀ i j : Fin 102, sign (fullRows i) j.val=sign (fullRows j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem fullDiagonal : ∀ i : Fin 102, sign (fullRows i) i.val=1 := by decide +kernel
private theorem lower0 : (lowerRow 102 rawFull) 0=true := by decide +kernel
private theorem lower1 : (lowerRow 102 rawFull) 1=true := by decide +kernel
private theorem lower2 : (lowerRow 102 rawFull) 2=true := by decide +kernel
private theorem lower3 : (lowerRow 102 rawFull) 3=true := by decide +kernel
private theorem lower4 : (lowerRow 102 rawFull) 4=true := by decide +kernel
private theorem lower5 : (lowerRow 102 rawFull) 5=true := by decide +kernel
private theorem lower6 : (lowerRow 102 rawFull) 6=true := by decide +kernel
private theorem lower7 : (lowerRow 102 rawFull) 7=true := by decide +kernel
private theorem lower8 : (lowerRow 102 rawFull) 8=true := by decide +kernel
private theorem lower9 : (lowerRow 102 rawFull) 9=true := by decide +kernel
private theorem lower10 : (lowerRow 102 rawFull) 10=true := by decide +kernel
private theorem lower11 : (lowerRow 102 rawFull) 11=true := by decide +kernel
private theorem lower12 : (lowerRow 102 rawFull) 12=true := by decide +kernel
private theorem lower13 : (lowerRow 102 rawFull) 13=true := by decide +kernel
private theorem lower14 : (lowerRow 102 rawFull) 14=true := by decide +kernel
private theorem lower15 : (lowerRow 102 rawFull) 15=true := by decide +kernel
private theorem lower16 : (lowerRow 102 rawFull) 16=true := by decide +kernel
private theorem lower17 : (lowerRow 102 rawFull) 17=true := by decide +kernel
private theorem lower18 : (lowerRow 102 rawFull) 18=true := by decide +kernel
private theorem lower19 : (lowerRow 102 rawFull) 19=true := by decide +kernel
private theorem lower20 : (lowerRow 102 rawFull) 20=true := by decide +kernel
private theorem lower21 : (lowerRow 102 rawFull) 21=true := by decide +kernel
private theorem lower22 : (lowerRow 102 rawFull) 22=true := by decide +kernel
private theorem lower23 : (lowerRow 102 rawFull) 23=true := by decide +kernel
private theorem lower24 : (lowerRow 102 rawFull) 24=true := by decide +kernel
private theorem lower25 : (lowerRow 102 rawFull) 25=true := by decide +kernel
private theorem lower26 : (lowerRow 102 rawFull) 26=true := by decide +kernel
private theorem lower27 : (lowerRow 102 rawFull) 27=true := by decide +kernel
private theorem lower28 : (lowerRow 102 rawFull) 28=true := by decide +kernel
private theorem lower29 : (lowerRow 102 rawFull) 29=true := by decide +kernel
private theorem lower30 : (lowerRow 102 rawFull) 30=true := by decide +kernel
private theorem lower31 : (lowerRow 102 rawFull) 31=true := by decide +kernel
private theorem lower32 : (lowerRow 102 rawFull) 32=true := by decide +kernel
private theorem lower33 : (lowerRow 102 rawFull) 33=true := by decide +kernel
private theorem lower34 : (lowerRow 102 rawFull) 34=true := by decide +kernel
private theorem lower35 : (lowerRow 102 rawFull) 35=true := by decide +kernel
private theorem lower36 : (lowerRow 102 rawFull) 36=true := by decide +kernel
private theorem lower37 : (lowerRow 102 rawFull) 37=true := by decide +kernel
private theorem lower38 : (lowerRow 102 rawFull) 38=true := by decide +kernel
private theorem lower39 : (lowerRow 102 rawFull) 39=true := by decide +kernel
private theorem lower40 : (lowerRow 102 rawFull) 40=true := by decide +kernel
private theorem lower41 : (lowerRow 102 rawFull) 41=true := by decide +kernel
private theorem lower42 : (lowerRow 102 rawFull) 42=true := by decide +kernel
private theorem lower43 : (lowerRow 102 rawFull) 43=true := by decide +kernel
private theorem lower44 : (lowerRow 102 rawFull) 44=true := by decide +kernel
private theorem lower45 : (lowerRow 102 rawFull) 45=true := by decide +kernel
private theorem lower46 : (lowerRow 102 rawFull) 46=true := by decide +kernel
private theorem lower47 : (lowerRow 102 rawFull) 47=true := by decide +kernel
private theorem lower48 : (lowerRow 102 rawFull) 48=true := by decide +kernel
private theorem lower49 : (lowerRow 102 rawFull) 49=true := by decide +kernel
private theorem lower50 : (lowerRow 102 rawFull) 50=true := by decide +kernel
private theorem lower51 : (lowerRow 102 rawFull) 51=true := by decide +kernel
private theorem lower52 : (lowerRow 102 rawFull) 52=true := by decide +kernel
private theorem lower53 : (lowerRow 102 rawFull) 53=true := by decide +kernel
private theorem lower54 : (lowerRow 102 rawFull) 54=true := by decide +kernel
private theorem lower55 : (lowerRow 102 rawFull) 55=true := by decide +kernel
private theorem lower56 : (lowerRow 102 rawFull) 56=true := by decide +kernel
private theorem lower57 : (lowerRow 102 rawFull) 57=true := by decide +kernel
private theorem lower58 : (lowerRow 102 rawFull) 58=true := by decide +kernel
private theorem lower59 : (lowerRow 102 rawFull) 59=true := by decide +kernel
private theorem lower60 : (lowerRow 102 rawFull) 60=true := by decide +kernel
private theorem lower61 : (lowerRow 102 rawFull) 61=true := by decide +kernel
private theorem lower62 : (lowerRow 102 rawFull) 62=true := by decide +kernel
private theorem lower63 : (lowerRow 102 rawFull) 63=true := by decide +kernel
private theorem lower64 : (lowerRow 102 rawFull) 64=true := by decide +kernel
private theorem lower65 : (lowerRow 102 rawFull) 65=true := by decide +kernel
private theorem lower66 : (lowerRow 102 rawFull) 66=true := by decide +kernel
private theorem lower67 : (lowerRow 102 rawFull) 67=true := by decide +kernel
private theorem lower68 : (lowerRow 102 rawFull) 68=true := by decide +kernel
private theorem lower69 : (lowerRow 102 rawFull) 69=true := by decide +kernel
private theorem lower70 : (lowerRow 102 rawFull) 70=true := by decide +kernel
private theorem lower71 : (lowerRow 102 rawFull) 71=true := by decide +kernel
private theorem lower72 : (lowerRow 102 rawFull) 72=true := by decide +kernel
private theorem lower73 : (lowerRow 102 rawFull) 73=true := by decide +kernel
private theorem lower74 : (lowerRow 102 rawFull) 74=true := by decide +kernel
private theorem lower75 : (lowerRow 102 rawFull) 75=true := by decide +kernel
private theorem lower76 : (lowerRow 102 rawFull) 76=true := by decide +kernel
private theorem lower77 : (lowerRow 102 rawFull) 77=true := by decide +kernel
private theorem lower78 : (lowerRow 102 rawFull) 78=true := by decide +kernel
private theorem lower79 : (lowerRow 102 rawFull) 79=true := by decide +kernel
private theorem lower80 : (lowerRow 102 rawFull) 80=true := by decide +kernel
private theorem lower81 : (lowerRow 102 rawFull) 81=true := by decide +kernel
private theorem lower82 : (lowerRow 102 rawFull) 82=true := by decide +kernel
private theorem lower83 : (lowerRow 102 rawFull) 83=true := by decide +kernel
private theorem lower84 : (lowerRow 102 rawFull) 84=true := by decide +kernel
private theorem lower85 : (lowerRow 102 rawFull) 85=true := by decide +kernel
private theorem lower86 : (lowerRow 102 rawFull) 86=true := by decide +kernel
private theorem lower87 : (lowerRow 102 rawFull) 87=true := by decide +kernel
private theorem lower88 : (lowerRow 102 rawFull) 88=true := by decide +kernel
private theorem lower89 : (lowerRow 102 rawFull) 89=true := by decide +kernel
private theorem lower90 : (lowerRow 102 rawFull) 90=true := by decide +kernel
private theorem lower91 : (lowerRow 102 rawFull) 91=true := by decide +kernel
private theorem lower92 : (lowerRow 102 rawFull) 92=true := by decide +kernel
private theorem lower93 : (lowerRow 102 rawFull) 93=true := by decide +kernel
private theorem lower94 : (lowerRow 102 rawFull) 94=true := by decide +kernel
private theorem lower95 : (lowerRow 102 rawFull) 95=true := by decide +kernel
private theorem lower96 : (lowerRow 102 rawFull) 96=true := by decide +kernel
private theorem lower97 : (lowerRow 102 rawFull) 97=true := by decide +kernel
private theorem lower98 : (lowerRow 102 rawFull) 98=true := by decide +kernel
private theorem lower99 : (lowerRow 102 rawFull) 99=true := by decide +kernel
private theorem lower100 : (lowerRow 102 rawFull) 100=true := by decide +kernel
private theorem lower101 : (lowerRow 102 rawFull) 101=true := by decide +kernel
private theorem lowerChecked : allBelow 102 (lowerRow 102 rawFull)=true := by
  have h : allBelow 0 (lowerRow 102 rawFull)=true := rfl
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
  have h := allBelow_step h lower98
  have h := allBelow_step h lower99
  have h := allBelow_step h lower100
  have h := allBelow_step h lower101
  exact h

private theorem fullPairs : ∀ i j : Fin 102, i≠j →
    correlation 102 (fullRows i) (fullRows j)=2*sign (fullRows i) j.val :=
  correlations_of_lower rawFull fullSymmetric lowerChecked


namespace SplitSquares
def rawWords (i : ℕ) : ℕ := #[0, 1359045761566052, 721824230811026, 458453196491584, 2183499591750628, 1344905715687186, 346119830100250, 1743400210641684, 46714090472702, 1201747800460472, 118655612760870, 232922234118760, 483426807104752, 1037197460081796, 1071666919577928, 876671344587760, 1828130490180288, 943037121850374, 1802471647796556, 1659530280136734, 1010175390093350, 2103901667140648, 1441692353627054, 1579809589823326, 1894770635971706, 1888103411514026, 1501805286640342, 1657517357739478, 2161663121994650, 2071529588707210, 354369668377070, 1759876426487452, 2112087482083962, 892464748998246, 1692566365886892, 57595028264934, 277912351452044, 327169241995068, 583966397345628, 266303215722200, 391864485067952, 1773264646274400, 513575929901602, 2236622236280128, 717809964521670, 1558807296423368, 1283752507428402, 699912628500542, 49630443925592, 1295532646981780, 679522880783026][i]!
def words (i : Fin 51) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 51 rawWords i=rowTotals i)

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
private theorem row49 : rowAgrees 49=true := by decide +kernel
private theorem row50 : rowAgrees 50=true := by decide +kernel
private theorem rowChecked : allBelow 51 rowAgrees=true := by
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
  have h := allBelow_step h row49
  have h := allBelow_step h row50
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 51, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 51, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-2550:ℤ) := by
  change cubicInteger (fun i : Fin 51 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-2550:ℤ) ∧
    87*(51:ℤ)^3+375*51*(4*51-3)+1000*((wordMatrix words-1)^3).trace-
      1110*101*(51-1)=(7229262:ℤ) ∧ 0≤(7229262:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 51 ⊕ Fin 51 → Fin 102
  | .inl i => Fin.ofNat 102 (#[0, 1, 4, 5, 6, 9, 13, 14, 16, 17, 19, 20, 21, 22, 23, 24, 25, 30, 31, 33, 36, 37, 43, 45, 47, 49, 52, 54, 56, 58, 64, 65, 68, 70, 71, 76, 77, 78, 79, 80, 81, 82, 84, 85, 87, 88, 92, 95, 96, 97, 100][i.val]!)
  | .inr i => Fin.ofNat 102 (#[2, 3, 7, 8, 10, 11, 12, 15, 18, 26, 27, 28, 29, 32, 34, 35, 38, 39, 40, 41, 42, 44, 46, 48, 50, 51, 53, 55, 57, 59, 60, 61, 62, 63, 66, 67, 69, 72, 73, 74, 75, 83, 86, 89, 90, 91, 93, 94, 98, 99, 101][i.val]!)

def pointPosition (i : Fin 102) : Fin 51 ⊕ Fin 51 :=
  let j : ℕ := #[0, 1, 51, 52, 2, 3, 4, 53, 54, 5, 55, 56, 57, 6, 7, 58, 8, 9, 59, 10, 11, 12, 13, 14, 15, 16, 60, 61, 62, 63, 17, 18, 64, 19, 65, 66, 20, 21, 67, 68, 69, 70, 71, 22, 72, 23, 73, 24, 74, 25, 75, 76, 26, 77, 27, 78, 28, 79, 29, 80, 81, 82, 83, 84, 30, 31, 85, 86, 32, 87, 33, 34, 88, 89, 90, 91, 35, 36, 37, 38, 39, 40, 41, 92, 42, 43, 93, 44, 45, 94, 95, 96, 46, 97, 98, 47, 48, 49, 99, 100, 50, 101][i.val]!
  if j<51 then .inl (Fin.ofNat 51 j) else .inr (Fin.ofNat 51 (j-51))

def indexing : (Fin 51 ⊕ Fin 51) ≃ Fin 102 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 51,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*101)*(101-1)^50) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 50 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 50 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 50=(2*101)*(101-1)^50 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquares


namespace SplitNonsquares
def rawWords (i : ℕ) : ℕ := #[2251799813685246, 214574351036577, 451274570163041, 740773372199713, 2048618930997089, 1272089980310175, 296642629477909, 576103540197667, 619357813083805, 249223710782845, 1861857993470801, 1612688684196225, 410661965202979, 697868572446279, 2205456083558405, 514500590586907, 896888134064157, 1927272279383269, 2029252437375209, 1384800923578579, 939740140840335, 1316255714625855, 1456588039710631, 1455483504792283, 2039649209548859, 967585955791859, 1403179931271405, 1618505119240143, 1605966273985867, 1792688523588427, 2191580703247187, 1999282230056621, 1320394523012467, 406685457947343, 689984835269047, 986967731789645, 1551552374340793, 563342476950207, 1731883835250149, 1202930427882217, 26793107903963, 190029244246935, 1102536181634161, 1010455043321029, 1206197392178437, 710589855644425, 2133629930762771, 121055199546927, 83678241085525, 119214922229145, 88862838639665][i]!
def words (i : Fin 51) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 51 rawWords i=rowTotals i)

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
private theorem row49 : rowAgrees 49=true := by decide +kernel
private theorem row50 : rowAgrees 50=true := by decide +kernel
private theorem rowChecked : allBelow 51 rowAgrees=true := by
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
  have h := allBelow_step h row49
  have h := allBelow_step h row50
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 51, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 51, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(2550:ℤ) := by
  change cubicInteger (fun i : Fin 51 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(2550:ℤ) ∧
    87*(51:ℤ)^3+375*51*(4*51-3)+1000*((wordMatrix words-1)^3).trace-
      1110*101*(51-1)=(12329262:ℤ) ∧ 0≤(12329262:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 51 ⊕ Fin 51 → Fin 102
  | .inl i => Fin.ofNat 102 (#[0, 2, 3, 7, 8, 10, 11, 12, 15, 18, 26, 27, 28, 29, 32, 34, 35, 38, 39, 40, 41, 42, 44, 46, 48, 50, 51, 53, 55, 57, 59, 60, 61, 62, 63, 66, 67, 69, 72, 73, 74, 75, 83, 86, 89, 90, 91, 93, 94, 98, 99][i.val]!)
  | .inr i => Fin.ofNat 102 (#[1, 4, 5, 6, 9, 13, 14, 16, 17, 19, 20, 21, 22, 23, 24, 25, 30, 31, 33, 36, 37, 43, 45, 47, 49, 52, 54, 56, 58, 64, 65, 68, 70, 71, 76, 77, 78, 79, 80, 81, 82, 84, 85, 87, 88, 92, 95, 96, 97, 100, 101][i.val]!)

def pointPosition (i : Fin 102) : Fin 51 ⊕ Fin 51 :=
  let j : ℕ := #[0, 51, 1, 2, 52, 53, 54, 3, 4, 55, 5, 6, 7, 56, 57, 8, 58, 59, 9, 60, 61, 62, 63, 64, 65, 66, 10, 11, 12, 13, 67, 68, 14, 69, 15, 16, 70, 71, 17, 18, 19, 20, 21, 72, 22, 73, 23, 74, 24, 75, 25, 26, 76, 27, 77, 28, 78, 29, 79, 30, 31, 32, 33, 34, 80, 81, 35, 36, 82, 37, 83, 84, 38, 39, 40, 41, 85, 86, 87, 88, 89, 90, 91, 42, 92, 93, 43, 94, 95, 44, 45, 46, 96, 47, 48, 97, 98, 99, 49, 50, 100, 101][i.val]!
  if j<51 then .inl (Fin.ofNat 51 j) else .inr (Fin.ofNat 51 (j-51))

def indexing : (Fin 51 ⊕ Fin 51) ≃ Fin 102 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 51,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*101)*(101-1)^50) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 50 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 50 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 50=(2*101)*(101-1)^50 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquares


namespace NonsplitNegative
def rawWords (i : ℕ) : ℕ := #[1953417005076726, 502847569163169, 159694089611113, 1427846508547860, 1763026824134761, 1268800689411479, 4305014097685, 849740752103971, 1142041959226478, 34985605893326, 473164517792620, 1940829786720136, 418078434747683, 1396864566857862, 820226020744454, 2206631843933709, 890286655051805, 2211840021852397, 1664766218253275, 658264474936207, 797638220698198, 1452318453694639, 1081667935740268, 1177039683146459, 1086870908143004, 696006984830203, 1674687343757797, 1013863095997372, 1606028956538691, 959102853988028, 2058359247237451, 1869973858609844, 2001543918311077, 1614995994543483, 968580426456511, 986900739840333, 852442763589311, 1701518138669428, 1707091130640114, 1207738661848041, 314700949834358, 965027826673496, 2026483981270912, 2079877300180738, 1202072751616525, 719109438667777, 1858743320901651, 387073682369575, 720315364119690, 402962075338897, 102133595023673][i]!
def words (i : Fin 51) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 51 rawWords i=rowTotals i)

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
private theorem row49 : rowAgrees 49=true := by decide +kernel
private theorem row50 : rowAgrees 50=true := by decide +kernel
private theorem rowChecked : allBelow 51 rowAgrees=true := by
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
  have h := allBelow_step h row49
  have h := allBelow_step h row50
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 51, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 51, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(510:ℤ) := by
  change cubicInteger (fun i : Fin 51 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(510:ℤ) ∧
    87*(51:ℤ)^3+375*51*(4*51-3)+1000*((wordMatrix words-1)^3).trace-
      1110*101*(51-1)=(10289262:ℤ) ∧ 0≤(10289262:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 51 ⊕ Fin 51 → Fin 102
  | .inl i => Fin.ofNat 102 (#[0, 2, 3, 6, 8, 10, 11, 12, 13, 14, 21, 24, 28, 30, 31, 32, 35, 38, 40, 41, 43, 44, 45, 46, 47, 50, 51, 54, 55, 56, 57, 58, 60, 61, 63, 66, 69, 70, 71, 73, 77, 80, 87, 88, 89, 90, 91, 93, 95, 98, 99][i.val]!)
  | .inr i => Fin.ofNat 102 (#[1, 4, 5, 7, 9, 15, 16, 17, 18, 19, 20, 22, 23, 25, 26, 27, 29, 33, 34, 36, 37, 39, 42, 48, 49, 52, 53, 59, 62, 64, 65, 67, 68, 72, 74, 75, 76, 78, 79, 81, 82, 83, 84, 85, 86, 92, 94, 96, 97, 100, 101][i.val]!)

def pointPosition (i : Fin 102) : Fin 51 ⊕ Fin 51 :=
  let j : ℕ := #[0, 51, 1, 2, 52, 53, 3, 54, 4, 55, 5, 6, 7, 8, 9, 56, 57, 58, 59, 60, 61, 10, 62, 63, 11, 64, 65, 66, 12, 67, 13, 14, 15, 68, 69, 16, 70, 71, 17, 72, 18, 19, 73, 20, 21, 22, 23, 24, 74, 75, 25, 26, 76, 77, 27, 28, 29, 30, 31, 78, 32, 33, 79, 34, 80, 81, 35, 82, 83, 36, 37, 38, 84, 39, 85, 86, 87, 40, 88, 89, 41, 90, 91, 92, 93, 94, 95, 42, 43, 44, 45, 46, 96, 47, 97, 48, 98, 99, 49, 50, 100, 101][i.val]!
  if j<51 then .inl (Fin.ofNat 51 j) else .inr (Fin.ofNat 51 (j-51))

def indexing : (Fin 51 ⊕ Fin 51) ≃ Fin 102 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 51,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*101)*(101-1)^50) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 50 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 50 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 50=(2*101)*(101-1)^50 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegative


namespace SplitSquaresOpposite
def rawWords (i : ℕ) : ℕ := #[107287175518288, 225637285081520, 370386686099856, 1024309465498544, 636044990155087, 148321314738954, 288051770098833, 309678906541902, 124611855391422, 930928996735400, 806344342098112, 205330982601489, 348934286223139, 1102728041779202, 257250295293453, 448444067032078, 963636139691634, 1014626218687604, 692400461789289, 469870070420167, 658127857312927, 728294019855315, 727741752396141, 1019824604774429, 483792977895929, 701589965635702, 809252559620071, 802983136992933, 896344261794213, 1095790351623593, 999641115028310, 660197261506233, 203342728973671, 344992417634523, 493483865894822, 775776187170396, 281671238475103, 865941917625074, 601465213941108, 13396553951981, 95014622123467, 551268090817080, 505227521660514, 603098696089218, 355294927822212, 1066814965381385, 60527599773463, 41839120542762, 59607461114572, 44431419319832, 0][i]!
def words (i : Fin 51) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201, 201]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 51 rawWords i=rowTotals i)

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
private theorem row49 : rowAgrees 49=true := by decide +kernel
private theorem row50 : rowAgrees 50=true := by decide +kernel
private theorem rowChecked : allBelow 51 rowAgrees=true := by
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
  have h := allBelow_step h row49
  have h := allBelow_step h row50
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 51, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 51, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(2550:ℤ) := by
  change cubicInteger (fun i : Fin 51 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(2550:ℤ) ∧
    87*(51:ℤ)^3+375*51*(4*51-3)+1000*((wordMatrix words-1)^3).trace-
      1110*101*(51-1)=(12329262:ℤ) ∧ 0≤(12329262:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 51 ⊕ Fin 51 → Fin 102
  | .inl i => Fin.ofNat 102 (#[2, 3, 7, 8, 10, 11, 12, 15, 18, 26, 27, 28, 29, 32, 34, 35, 38, 39, 40, 41, 42, 44, 46, 48, 50, 51, 53, 55, 57, 59, 60, 61, 62, 63, 66, 67, 69, 72, 73, 74, 75, 83, 86, 89, 90, 91, 93, 94, 98, 99, 101][i.val]!)
  | .inr i => Fin.ofNat 102 (#[0, 1, 4, 5, 6, 9, 13, 14, 16, 17, 19, 20, 21, 22, 23, 24, 25, 30, 31, 33, 36, 37, 43, 45, 47, 49, 52, 54, 56, 58, 64, 65, 68, 70, 71, 76, 77, 78, 79, 80, 81, 82, 84, 85, 87, 88, 92, 95, 96, 97, 100][i.val]!)

def pointPosition (i : Fin 102) : Fin 51 ⊕ Fin 51 :=
  let j : ℕ := #[51, 52, 0, 1, 53, 54, 55, 2, 3, 56, 4, 5, 6, 57, 58, 7, 59, 60, 8, 61, 62, 63, 64, 65, 66, 67, 9, 10, 11, 12, 68, 69, 13, 70, 14, 15, 71, 72, 16, 17, 18, 19, 20, 73, 21, 74, 22, 75, 23, 76, 24, 25, 77, 26, 78, 27, 79, 28, 80, 29, 30, 31, 32, 33, 81, 82, 34, 35, 83, 36, 84, 85, 37, 38, 39, 40, 86, 87, 88, 89, 90, 91, 92, 41, 93, 94, 42, 95, 96, 43, 44, 45, 97, 46, 47, 98, 99, 100, 48, 49, 101, 50][i.val]!
  if j<51 then .inl (Fin.ofNat 51 j) else .inr (Fin.ofNat 51 (j-51))

def indexing : (Fin 51 ⊕ Fin 51) ≃ Fin 102 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 51,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*101)*(101-1)^50) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 50 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 50 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 50=(2*101)*(101-1)^50 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquaresOpposite


namespace SplitNonsquaresOpposite
def rawWords (i : ℕ) : ℕ := #[679522880783026, 360912115405513, 229226598245792, 1091749795875314, 672452857843593, 173059915050125, 871700105320842, 23357045236351, 600873900230236, 59327806380435, 116461117059380, 241713403552376, 518598730040898, 535833459788964, 438335672293880, 914065245090144, 471518560925187, 901235823898278, 829765140068367, 505087695046675, 1051950833570324, 720846176813527, 789904794911663, 947385317985853, 944051705757013, 750902643320171, 828758678869739, 1080831560997325, 1035764794353605, 177184834188535, 879938213243726, 1056043741041981, 446232374499123, 846283182943446, 28797514132467, 138956175726022, 163584620997534, 291983198672814, 133151607861100, 195932242533976, 886632323137200, 256787964950801, 1118311118140064, 358904982260835, 779403648211684, 641876253714201, 349956314250271, 24815221962796, 647766323490890, 339761440391513, 0][i]!
def words (i : Fin 51) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101, 101]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 51 rawWords i=rowTotals i)

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
private theorem row49 : rowAgrees 49=true := by decide +kernel
private theorem row50 : rowAgrees 50=true := by decide +kernel
private theorem rowChecked : allBelow 51 rowAgrees=true := by
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
  have h := allBelow_step h row49
  have h := allBelow_step h row50
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 51, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 51, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-2550:ℤ) := by
  change cubicInteger (fun i : Fin 51 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-2550:ℤ) ∧
    87*(51:ℤ)^3+375*51*(4*51-3)+1000*((wordMatrix words-1)^3).trace-
      1110*101*(51-1)=(7229262:ℤ) ∧ 0≤(7229262:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 51 ⊕ Fin 51 → Fin 102
  | .inl i => Fin.ofNat 102 (#[1, 4, 5, 6, 9, 13, 14, 16, 17, 19, 20, 21, 22, 23, 24, 25, 30, 31, 33, 36, 37, 43, 45, 47, 49, 52, 54, 56, 58, 64, 65, 68, 70, 71, 76, 77, 78, 79, 80, 81, 82, 84, 85, 87, 88, 92, 95, 96, 97, 100, 101][i.val]!)
  | .inr i => Fin.ofNat 102 (#[0, 2, 3, 7, 8, 10, 11, 12, 15, 18, 26, 27, 28, 29, 32, 34, 35, 38, 39, 40, 41, 42, 44, 46, 48, 50, 51, 53, 55, 57, 59, 60, 61, 62, 63, 66, 67, 69, 72, 73, 74, 75, 83, 86, 89, 90, 91, 93, 94, 98, 99][i.val]!)

def pointPosition (i : Fin 102) : Fin 51 ⊕ Fin 51 :=
  let j : ℕ := #[51, 0, 52, 53, 1, 2, 3, 54, 55, 4, 56, 57, 58, 5, 6, 59, 7, 8, 60, 9, 10, 11, 12, 13, 14, 15, 61, 62, 63, 64, 16, 17, 65, 18, 66, 67, 19, 20, 68, 69, 70, 71, 72, 21, 73, 22, 74, 23, 75, 24, 76, 77, 25, 78, 26, 79, 27, 80, 28, 81, 82, 83, 84, 85, 29, 30, 86, 87, 31, 88, 32, 33, 89, 90, 91, 92, 34, 35, 36, 37, 38, 39, 40, 93, 41, 42, 94, 43, 44, 95, 96, 97, 45, 98, 99, 46, 47, 48, 100, 101, 49, 50][i.val]!
  if j<51 then .inl (Fin.ofNat 51 j) else .inr (Fin.ofNat 51 (j-51))

def indexing : (Fin 51 ⊕ Fin 51) ≃ Fin 102 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 51,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*101)*(101-1)^50) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 50 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 50 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 50=(2*101)*(101-1)^50 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquaresOpposite


namespace NonsplitNegativeOpposite
def rawWords (i : ℕ) : ℕ := #[673028680417874, 352328698432105, 211552728126696, 987179810433974, 606635099195081, 6319193127310, 12612989670167, 622838088312380, 49380279936104, 134100901284059, 127308123904404, 509946594010666, 491709113197668, 982108396493224, 627648906597216, 797325722461937, 199327825316737, 834322504907055, 1070095721355852, 445566092271899, 1102786064673300, 821222465699855, 342588186198123, 267301720559194, 851815133617341, 832195972593027, 397754241180476, 941201608058802, 1055558711811421, 177427634027871, 952295520662182, 221467491168975, 1075838916218301, 570974832839348, 630650330567341, 29840923143537, 94993433522939, 167785099211766, 371169567133646, 182948551872312, 963509958327928, 97423849577680, 265626602944945, 1023836656270144, 499715331061376, 648181011675025, 483037233458695, 101849558390796, 661087227492362, 326586548543641, 0][i]!
def words (i : Fin 51) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141, 141]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 51 rawWords i=rowTotals i)

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
private theorem row49 : rowAgrees 49=true := by decide +kernel
private theorem row50 : rowAgrees 50=true := by decide +kernel
private theorem rowChecked : allBelow 51 rowAgrees=true := by
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
  have h := allBelow_step h row49
  have h := allBelow_step h row50
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 51, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 51, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-510:ℤ) := by
  change cubicInteger (fun i : Fin 51 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-510:ℤ) ∧
    87*(51:ℤ)^3+375*51*(4*51-3)+1000*((wordMatrix words-1)^3).trace-
      1110*101*(51-1)=(9269262:ℤ) ∧ 0≤(9269262:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 51 ⊕ Fin 51 → Fin 102
  | .inl i => Fin.ofNat 102 (#[1, 4, 5, 7, 9, 15, 16, 17, 18, 19, 20, 22, 23, 25, 26, 27, 29, 33, 34, 36, 37, 39, 42, 48, 49, 52, 53, 59, 62, 64, 65, 67, 68, 72, 74, 75, 76, 78, 79, 81, 82, 83, 84, 85, 86, 92, 94, 96, 97, 100, 101][i.val]!)
  | .inr i => Fin.ofNat 102 (#[0, 2, 3, 6, 8, 10, 11, 12, 13, 14, 21, 24, 28, 30, 31, 32, 35, 38, 40, 41, 43, 44, 45, 46, 47, 50, 51, 54, 55, 56, 57, 58, 60, 61, 63, 66, 69, 70, 71, 73, 77, 80, 87, 88, 89, 90, 91, 93, 95, 98, 99][i.val]!)

def pointPosition (i : Fin 102) : Fin 51 ⊕ Fin 51 :=
  let j : ℕ := #[51, 0, 52, 53, 1, 2, 54, 3, 55, 4, 56, 57, 58, 59, 60, 5, 6, 7, 8, 9, 10, 61, 11, 12, 62, 13, 14, 15, 63, 16, 64, 65, 66, 17, 18, 67, 19, 20, 68, 21, 69, 70, 22, 71, 72, 73, 74, 75, 23, 24, 76, 77, 25, 26, 78, 79, 80, 81, 82, 27, 83, 84, 28, 85, 29, 30, 86, 31, 32, 87, 88, 89, 33, 90, 34, 35, 36, 91, 37, 38, 92, 39, 40, 41, 42, 43, 44, 93, 94, 95, 96, 97, 45, 98, 46, 99, 47, 48, 100, 101, 49, 50][i.val]!
  if j<51 then .inl (Fin.ofNat 51 j) else .inr (Fin.ofNat 51 (j-51))

def indexing : (Fin 51 ⊕ Fin 51) ≃ Fin 102 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 51,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*101)*(101-1)^50) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 50 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 50 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 50=(2*101)*(101-1)^50 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegativeOpposite

end PaleyBits101
