import Quantum.Hadamard.ConferenceBitCompletion
open Hadamard.BitTrace Hadamard.DeterminantRatio Matrix
set_option maxHeartbeats 12000000
set_option maxRecDepth 60000
namespace PaleyBits113

def rawFull (i : ℕ) : ℕ := #[1797644397492755318821822240789608, 3595288794985510637643644481579216, 7190577589971021275287288963158432, 3996561462872387293513585267876673, 7993122925744774587027170535753346, 5601652134419893916993348413066501, 818710551770132576925704167692811, 1637421103540265153851408335385622, 3274842207080530307702816670771244, 6549684414161060615405633341542488, 2714775111252465973750274024644785, 5429550222504931947500548049289570, 474506727940208637940103440138949, 949013455880417275880206880277898, 1898026911760834551760413760555796, 3796053823521669103520827521111592, 7592107647043338207041655042223184, 4799621577017021157022317426006177, 9599243154034042314044634852012354, 8813892590998429371028277045584517, 7243191464927203484995561432728843, 4101789212784751712930130207017495, 8203578425569503425860260414034990, 6022563134069351594659528169629789, 1660532551069047932258063680819387, 3321065102138095864516127361638774, 6642130204276191729032254723277548, 2899666691482728201003516788114905, 5799333382965456402007033576229810, 1214073048861257546953074494019429, 2428146097722515093906148988038858, 4856292195445030187812297976077716, 9712584390890060375624595952155432, 9040575064710465494188199245870673, 7696556412351275731315405833301155, 5008519107632896205569819008162119, 10017038215265792411139638016324238, 9649482713461929565218283374208285, 8914371709854203873375574089976379, 7444149702638752489690155521512567, 4503705688207849722319318384584943, 9007411376415699444638636769169886, 7630229035761743632216280879899581, 4875864354453832007371569101358971, 9751728708907664014743138202717942, 9118863700745672772425283746995693, 7853133684421690287789574835551195, 5321673651773725318518157012662199, 258753586477795379975321366884207, 517507172955590759950642733768414, 1035014345911181519901285467536828, 2070028691822363039802570935073656, 4140057383644726079605141870147312, 8280114767289452159210283740294624, 6175635817509249061359574822149057, 1966677917948842865658156985857923, 3933355835897685731316313971715846, 7866711671795371462632627943431692, 5348829626521087668204263228423193, 313065535972520079347533798406195, 626131071945040158695067596812390, 1252262143890080317390135193624780, 2504524287780160634780270387249560, 5009048575560321269560540774499120, 10018097151120642539121081548998240, 9651600585171629821181170439556289, 8918607453273604385301348220672387, 7452621189477553513541703782904583, 4520648661885451770022414907368975, 9041297323770903540044829814737950, 7698000930472151823028666971035709, 5011408143874648388996341283631227, 10022816287749296777992682567262454, 9661038858428938298924372476084717, 8937483999788221340787752293729243, 7490374282506787424514511929018295, 4596154847943919591968031199596399, 9192309695887839183936062399192798, 8000025674706023110811132139945405, 5615457632342390964561271621450619, 846321547615126672061550584461047, 1692643095230253344123101168922094, 3385286190460506688246202337844188, 6770572380921013376492404675688376, 3156551044772371495923816692936561, 6313102089544742991847633385873122, 2241610462019830726634274113306053, 4483220924039661453268548226612106, 8966441848079322906537096453224212, 7548289979088990556013200248008233, 4711986241108325854965407837576275, 9423972482216651709930815675152550, 8463351247363648162800638691864909, 6542108777657641068540284725289627, 2699623838245626880019576792139063, 5399247676491253760039153584278126, 413901635912852263017314510116061, 827803271825704526034629020232122, 1655606543651409052069258040464244, 3311213087302818104138516080928488, 6622426174605636208277032161856976, 2860258632141617159493071665273761, 5720517264283234318986143330547522, 1056440811496813380911294002654853, 2112881622993626761822588005309706, 4225763245987253523645176010619412, 8451526491974507047290352021238824, 6518459266879358837519711384037457, 2652324816689062417978430109634723, 5304649633378124835956860219269446, 224705549686594414852727780098701, 449411099373188829705455560197402, 898822198746377659410911120394804, 0][i]!
def fullRows (i : Fin 114) : ℕ := rawFull i.val

private theorem fullSymmetric : (wordMatrix fullRows).IsSymm := by
  have h : ∀ i j : Fin 114, sign (fullRows i) j.val=sign (fullRows j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem fullDiagonal : ∀ i : Fin 114, sign (fullRows i) i.val=1 := by decide +kernel
private theorem lower0 : (lowerRow 114 rawFull) 0=true := by decide +kernel
private theorem lower1 : (lowerRow 114 rawFull) 1=true := by decide +kernel
private theorem lower2 : (lowerRow 114 rawFull) 2=true := by decide +kernel
private theorem lower3 : (lowerRow 114 rawFull) 3=true := by decide +kernel
private theorem lower4 : (lowerRow 114 rawFull) 4=true := by decide +kernel
private theorem lower5 : (lowerRow 114 rawFull) 5=true := by decide +kernel
private theorem lower6 : (lowerRow 114 rawFull) 6=true := by decide +kernel
private theorem lower7 : (lowerRow 114 rawFull) 7=true := by decide +kernel
private theorem lower8 : (lowerRow 114 rawFull) 8=true := by decide +kernel
private theorem lower9 : (lowerRow 114 rawFull) 9=true := by decide +kernel
private theorem lower10 : (lowerRow 114 rawFull) 10=true := by decide +kernel
private theorem lower11 : (lowerRow 114 rawFull) 11=true := by decide +kernel
private theorem lower12 : (lowerRow 114 rawFull) 12=true := by decide +kernel
private theorem lower13 : (lowerRow 114 rawFull) 13=true := by decide +kernel
private theorem lower14 : (lowerRow 114 rawFull) 14=true := by decide +kernel
private theorem lower15 : (lowerRow 114 rawFull) 15=true := by decide +kernel
private theorem lower16 : (lowerRow 114 rawFull) 16=true := by decide +kernel
private theorem lower17 : (lowerRow 114 rawFull) 17=true := by decide +kernel
private theorem lower18 : (lowerRow 114 rawFull) 18=true := by decide +kernel
private theorem lower19 : (lowerRow 114 rawFull) 19=true := by decide +kernel
private theorem lower20 : (lowerRow 114 rawFull) 20=true := by decide +kernel
private theorem lower21 : (lowerRow 114 rawFull) 21=true := by decide +kernel
private theorem lower22 : (lowerRow 114 rawFull) 22=true := by decide +kernel
private theorem lower23 : (lowerRow 114 rawFull) 23=true := by decide +kernel
private theorem lower24 : (lowerRow 114 rawFull) 24=true := by decide +kernel
private theorem lower25 : (lowerRow 114 rawFull) 25=true := by decide +kernel
private theorem lower26 : (lowerRow 114 rawFull) 26=true := by decide +kernel
private theorem lower27 : (lowerRow 114 rawFull) 27=true := by decide +kernel
private theorem lower28 : (lowerRow 114 rawFull) 28=true := by decide +kernel
private theorem lower29 : (lowerRow 114 rawFull) 29=true := by decide +kernel
private theorem lower30 : (lowerRow 114 rawFull) 30=true := by decide +kernel
private theorem lower31 : (lowerRow 114 rawFull) 31=true := by decide +kernel
private theorem lower32 : (lowerRow 114 rawFull) 32=true := by decide +kernel
private theorem lower33 : (lowerRow 114 rawFull) 33=true := by decide +kernel
private theorem lower34 : (lowerRow 114 rawFull) 34=true := by decide +kernel
private theorem lower35 : (lowerRow 114 rawFull) 35=true := by decide +kernel
private theorem lower36 : (lowerRow 114 rawFull) 36=true := by decide +kernel
private theorem lower37 : (lowerRow 114 rawFull) 37=true := by decide +kernel
private theorem lower38 : (lowerRow 114 rawFull) 38=true := by decide +kernel
private theorem lower39 : (lowerRow 114 rawFull) 39=true := by decide +kernel
private theorem lower40 : (lowerRow 114 rawFull) 40=true := by decide +kernel
private theorem lower41 : (lowerRow 114 rawFull) 41=true := by decide +kernel
private theorem lower42 : (lowerRow 114 rawFull) 42=true := by decide +kernel
private theorem lower43 : (lowerRow 114 rawFull) 43=true := by decide +kernel
private theorem lower44 : (lowerRow 114 rawFull) 44=true := by decide +kernel
private theorem lower45 : (lowerRow 114 rawFull) 45=true := by decide +kernel
private theorem lower46 : (lowerRow 114 rawFull) 46=true := by decide +kernel
private theorem lower47 : (lowerRow 114 rawFull) 47=true := by decide +kernel
private theorem lower48 : (lowerRow 114 rawFull) 48=true := by decide +kernel
private theorem lower49 : (lowerRow 114 rawFull) 49=true := by decide +kernel
private theorem lower50 : (lowerRow 114 rawFull) 50=true := by decide +kernel
private theorem lower51 : (lowerRow 114 rawFull) 51=true := by decide +kernel
private theorem lower52 : (lowerRow 114 rawFull) 52=true := by decide +kernel
private theorem lower53 : (lowerRow 114 rawFull) 53=true := by decide +kernel
private theorem lower54 : (lowerRow 114 rawFull) 54=true := by decide +kernel
private theorem lower55 : (lowerRow 114 rawFull) 55=true := by decide +kernel
private theorem lower56 : (lowerRow 114 rawFull) 56=true := by decide +kernel
private theorem lower57 : (lowerRow 114 rawFull) 57=true := by decide +kernel
private theorem lower58 : (lowerRow 114 rawFull) 58=true := by decide +kernel
private theorem lower59 : (lowerRow 114 rawFull) 59=true := by decide +kernel
private theorem lower60 : (lowerRow 114 rawFull) 60=true := by decide +kernel
private theorem lower61 : (lowerRow 114 rawFull) 61=true := by decide +kernel
private theorem lower62 : (lowerRow 114 rawFull) 62=true := by decide +kernel
private theorem lower63 : (lowerRow 114 rawFull) 63=true := by decide +kernel
private theorem lower64 : (lowerRow 114 rawFull) 64=true := by decide +kernel
private theorem lower65 : (lowerRow 114 rawFull) 65=true := by decide +kernel
private theorem lower66 : (lowerRow 114 rawFull) 66=true := by decide +kernel
private theorem lower67 : (lowerRow 114 rawFull) 67=true := by decide +kernel
private theorem lower68 : (lowerRow 114 rawFull) 68=true := by decide +kernel
private theorem lower69 : (lowerRow 114 rawFull) 69=true := by decide +kernel
private theorem lower70 : (lowerRow 114 rawFull) 70=true := by decide +kernel
private theorem lower71 : (lowerRow 114 rawFull) 71=true := by decide +kernel
private theorem lower72 : (lowerRow 114 rawFull) 72=true := by decide +kernel
private theorem lower73 : (lowerRow 114 rawFull) 73=true := by decide +kernel
private theorem lower74 : (lowerRow 114 rawFull) 74=true := by decide +kernel
private theorem lower75 : (lowerRow 114 rawFull) 75=true := by decide +kernel
private theorem lower76 : (lowerRow 114 rawFull) 76=true := by decide +kernel
private theorem lower77 : (lowerRow 114 rawFull) 77=true := by decide +kernel
private theorem lower78 : (lowerRow 114 rawFull) 78=true := by decide +kernel
private theorem lower79 : (lowerRow 114 rawFull) 79=true := by decide +kernel
private theorem lower80 : (lowerRow 114 rawFull) 80=true := by decide +kernel
private theorem lower81 : (lowerRow 114 rawFull) 81=true := by decide +kernel
private theorem lower82 : (lowerRow 114 rawFull) 82=true := by decide +kernel
private theorem lower83 : (lowerRow 114 rawFull) 83=true := by decide +kernel
private theorem lower84 : (lowerRow 114 rawFull) 84=true := by decide +kernel
private theorem lower85 : (lowerRow 114 rawFull) 85=true := by decide +kernel
private theorem lower86 : (lowerRow 114 rawFull) 86=true := by decide +kernel
private theorem lower87 : (lowerRow 114 rawFull) 87=true := by decide +kernel
private theorem lower88 : (lowerRow 114 rawFull) 88=true := by decide +kernel
private theorem lower89 : (lowerRow 114 rawFull) 89=true := by decide +kernel
private theorem lower90 : (lowerRow 114 rawFull) 90=true := by decide +kernel
private theorem lower91 : (lowerRow 114 rawFull) 91=true := by decide +kernel
private theorem lower92 : (lowerRow 114 rawFull) 92=true := by decide +kernel
private theorem lower93 : (lowerRow 114 rawFull) 93=true := by decide +kernel
private theorem lower94 : (lowerRow 114 rawFull) 94=true := by decide +kernel
private theorem lower95 : (lowerRow 114 rawFull) 95=true := by decide +kernel
private theorem lower96 : (lowerRow 114 rawFull) 96=true := by decide +kernel
private theorem lower97 : (lowerRow 114 rawFull) 97=true := by decide +kernel
private theorem lower98 : (lowerRow 114 rawFull) 98=true := by decide +kernel
private theorem lower99 : (lowerRow 114 rawFull) 99=true := by decide +kernel
private theorem lower100 : (lowerRow 114 rawFull) 100=true := by decide +kernel
private theorem lower101 : (lowerRow 114 rawFull) 101=true := by decide +kernel
private theorem lower102 : (lowerRow 114 rawFull) 102=true := by decide +kernel
private theorem lower103 : (lowerRow 114 rawFull) 103=true := by decide +kernel
private theorem lower104 : (lowerRow 114 rawFull) 104=true := by decide +kernel
private theorem lower105 : (lowerRow 114 rawFull) 105=true := by decide +kernel
private theorem lower106 : (lowerRow 114 rawFull) 106=true := by decide +kernel
private theorem lower107 : (lowerRow 114 rawFull) 107=true := by decide +kernel
private theorem lower108 : (lowerRow 114 rawFull) 108=true := by decide +kernel
private theorem lower109 : (lowerRow 114 rawFull) 109=true := by decide +kernel
private theorem lower110 : (lowerRow 114 rawFull) 110=true := by decide +kernel
private theorem lower111 : (lowerRow 114 rawFull) 111=true := by decide +kernel
private theorem lower112 : (lowerRow 114 rawFull) 112=true := by decide +kernel
private theorem lower113 : (lowerRow 114 rawFull) 113=true := by decide +kernel
private theorem lowerChecked : allBelow 114 (lowerRow 114 rawFull)=true := by
  have h : allBelow 0 (lowerRow 114 rawFull)=true := rfl
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
  have h := allBelow_step h lower102
  have h := allBelow_step h lower103
  have h := allBelow_step h lower104
  have h := allBelow_step h lower105
  have h := allBelow_step h lower106
  have h := allBelow_step h lower107
  have h := allBelow_step h lower108
  have h := allBelow_step h lower109
  have h := allBelow_step h lower110
  have h := allBelow_step h lower111
  have h := allBelow_step h lower112
  have h := allBelow_step h lower113
  exact h

private theorem fullPairs : ∀ i j : Fin 114, i≠j →
    correlation 114 (fullRows i) (fullRows j)=2*sign (fullRows i) j.val :=
  correlations_of_lower rawFull fullSymmetric lowerChecked


namespace SplitSquares
def rawWords (i : ℕ) : ℕ := #[0, 57551154375258520, 94778971525538352, 113374745766218322, 941119910674702, 58210083060667268, 78161696968640008, 79506683240319522, 33035174196959282, 11979015953088748, 61145817000988736, 105330772714561928, 111705120015844642, 119042397138667526, 61837733395899694, 89881084633549396, 84905952842905850, 34597499898450386, 71426664536588988, 123800854422660576, 138540434210590038, 136002191521755710, 127672981968667870, 2389893821755102, 25032758804254140, 32046446168456168, 46151301042362200, 109138288966279088, 39884928369310694, 116935721374398148, 15733402065237766, 30305581615660820, 26867460869287480, 69460033960926312, 139012666070333504, 138635592121362062, 139946567150523166, 120125564379869406, 8607036689395638, 68976983795633916, 85049592310226296, 107093006309824210, 47640628957883378, 131329570994534252, 108168121043967382, 77268256912796870, 19727606866686394, 2296256471724652, 61929537141589328, 85684270804953784, 76917226864490850, 18444778686895778, 38046209244319180, 126672255471037184, 83680117048888614, 13823877242975274, 28775577187629260][i]!
def words (i : Fin 57) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[113, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 57 rawWords i=rowTotals i)

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
private theorem row51 : rowAgrees 51=true := by decide +kernel
private theorem row52 : rowAgrees 52=true := by decide +kernel
private theorem row53 : rowAgrees 53=true := by decide +kernel
private theorem row54 : rowAgrees 54=true := by decide +kernel
private theorem row55 : rowAgrees 55=true := by decide +kernel
private theorem row56 : rowAgrees 56=true := by decide +kernel
private theorem rowChecked : allBelow 57 rowAgrees=true := by
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
  have h := allBelow_step h row51
  have h := allBelow_step h row52
  have h := allBelow_step h row53
  have h := allBelow_step h row54
  have h := allBelow_step h row55
  have h := allBelow_step h row56
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 57, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 57, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-504:ℤ) := by
  change cubicInteger (fun i : Fin 57 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-504:ℤ) ∧
    87*(57:ℤ)^3+375*57*(4*57-3)+1000*((wordMatrix words-1)^3).trace-
      1110*113*(57-1)=(13393086:ℤ) ∧ 0≤(13393086:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 57 ⊕ Fin 57 → Fin 114
  | .inl i => Fin.ofNat 114 (#[0, 1, 2, 4, 7, 8, 9, 11, 13, 14, 15, 16, 18, 22, 25, 26, 28, 30, 31, 32, 36, 41, 44, 49, 50, 51, 52, 53, 56, 57, 60, 61, 62, 63, 64, 69, 72, 77, 81, 82, 83, 85, 87, 88, 91, 95, 97, 98, 99, 100, 102, 104, 105, 106, 109, 111, 112][i.val]!)
  | .inr i => Fin.ofNat 114 (#[3, 5, 6, 10, 12, 17, 19, 20, 21, 23, 24, 27, 29, 33, 34, 35, 37, 38, 39, 40, 42, 43, 45, 46, 47, 48, 54, 55, 58, 59, 65, 66, 67, 68, 70, 71, 73, 74, 75, 76, 78, 79, 80, 84, 86, 89, 90, 92, 93, 94, 96, 101, 103, 107, 108, 110, 113][i.val]!)

def pointPosition (i : Fin 114) : Fin 57 ⊕ Fin 57 :=
  let j : ℕ := #[0, 1, 2, 57, 3, 58, 59, 4, 5, 6, 60, 7, 61, 8, 9, 10, 11, 62, 12, 63, 64, 65, 13, 66, 67, 14, 15, 68, 16, 69, 17, 18, 19, 70, 71, 72, 20, 73, 74, 75, 76, 21, 77, 78, 22, 79, 80, 81, 82, 23, 24, 25, 26, 27, 83, 84, 28, 29, 85, 86, 30, 31, 32, 33, 34, 87, 88, 89, 90, 35, 91, 92, 36, 93, 94, 95, 96, 37, 97, 98, 99, 38, 39, 40, 100, 41, 101, 42, 43, 102, 103, 44, 104, 105, 106, 45, 107, 46, 47, 48, 49, 108, 50, 109, 51, 52, 53, 110, 111, 54, 112, 55, 56, 113][i.val]!
  if j<57 then .inl (Fin.ofNat 57 j) else .inr (Fin.ofNat 57 (j-57))

def indexing : (Fin 57 ⊕ Fin 57) ≃ Fin 114 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 57,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*113)*(113-1)^56) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 56 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 56 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 56=(2*113)*(113-1)^56 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquares


namespace SplitNonsquares
def rawWords (i : ℕ) : ℕ := #[144115188075855870, 75232417320148233, 41763541622761553, 20755964413703203, 12661446396276997, 43257104496683081, 106839067476800805, 47272832110700545, 76181621540783187, 98355195552225281, 35679279617499467, 118718786185507495, 33531718317787739, 66447710240738557, 67852782548031033, 131533984283371605, 123509156816888873, 137674082168639827, 48197860805657287, 91821750960058813, 127278238774036431, 133099807312578183, 112848423515213215, 82083239899515455, 6611001035240683, 6748111957597493, 31138816377240223, 44828125294744553, 87775948677940081, 16614222344466355, 26791870872751077, 136639180458694105, 50352203913396129, 98151376178445217, 139974911116044051, 137018539042364455, 109635902751829103, 130471408569274511, 69308901314245003, 111756598404674389, 83919371674509919, 22677038508625335, 47377279344102191, 31983471542387261, 71149683378888925, 101693022048883641, 114054598613896855, 92915583403757049, 115126523321067, 83458883217888707, 89038415019925, 41295055803524987, 20365461382354533, 36659150922939601, 76766178566665801, 11352446961445029, 18825557055343427][i]!
def words (i : Fin 57) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[225, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 57 rawWords i=rowTotals i)

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
private theorem row51 : rowAgrees 51=true := by decide +kernel
private theorem row52 : rowAgrees 52=true := by decide +kernel
private theorem row53 : rowAgrees 53=true := by decide +kernel
private theorem row54 : rowAgrees 54=true := by decide +kernel
private theorem row55 : rowAgrees 55=true := by decide +kernel
private theorem row56 : rowAgrees 56=true := by decide +kernel
private theorem rowChecked : allBelow 57 rowAgrees=true := by
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
  have h := allBelow_step h row51
  have h := allBelow_step h row52
  have h := allBelow_step h row53
  have h := allBelow_step h row54
  have h := allBelow_step h row55
  have h := allBelow_step h row56
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 57, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 57, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(504:ℤ) := by
  change cubicInteger (fun i : Fin 57 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(504:ℤ) ∧
    87*(57:ℤ)^3+375*57*(4*57-3)+1000*((wordMatrix words-1)^3).trace-
      1110*113*(57-1)=(14401086:ℤ) ∧ 0≤(14401086:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 57 ⊕ Fin 57 → Fin 114
  | .inl i => Fin.ofNat 114 (#[0, 3, 5, 6, 10, 12, 17, 19, 20, 21, 23, 24, 27, 29, 33, 34, 35, 37, 38, 39, 40, 42, 43, 45, 46, 47, 48, 54, 55, 58, 59, 65, 66, 67, 68, 70, 71, 73, 74, 75, 76, 78, 79, 80, 84, 86, 89, 90, 92, 93, 94, 96, 101, 103, 107, 108, 110][i.val]!)
  | .inr i => Fin.ofNat 114 (#[1, 2, 4, 7, 8, 9, 11, 13, 14, 15, 16, 18, 22, 25, 26, 28, 30, 31, 32, 36, 41, 44, 49, 50, 51, 52, 53, 56, 57, 60, 61, 62, 63, 64, 69, 72, 77, 81, 82, 83, 85, 87, 88, 91, 95, 97, 98, 99, 100, 102, 104, 105, 106, 109, 111, 112, 113][i.val]!)

def pointPosition (i : Fin 114) : Fin 57 ⊕ Fin 57 :=
  let j : ℕ := #[0, 57, 58, 1, 59, 2, 3, 60, 61, 62, 4, 63, 5, 64, 65, 66, 67, 6, 68, 7, 8, 9, 69, 10, 11, 70, 71, 12, 72, 13, 73, 74, 75, 14, 15, 16, 76, 17, 18, 19, 20, 77, 21, 22, 78, 23, 24, 25, 26, 79, 80, 81, 82, 83, 27, 28, 84, 85, 29, 30, 86, 87, 88, 89, 90, 31, 32, 33, 34, 91, 35, 36, 92, 37, 38, 39, 40, 93, 41, 42, 43, 94, 95, 96, 44, 97, 45, 98, 99, 46, 47, 100, 48, 49, 50, 101, 51, 102, 103, 104, 105, 52, 106, 53, 107, 108, 109, 54, 55, 110, 56, 111, 112, 113][i.val]!
  if j<57 then .inl (Fin.ofNat 57 j) else .inr (Fin.ofNat 57 (j-57))

def indexing : (Fin 57 ⊕ Fin 57) ≃ Fin 114 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 57,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*113)*(113-1)^56) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 56 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 56 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 56=(2*113)*(113-1)^56 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquares


namespace NonsplitNegative
def rawWords (i : ℕ) : ℕ := #[109025218150705926, 102777803484184085, 42889132373227699, 75921967772037376, 79146433648841030, 46443150696728772, 136074624031986480, 95409126029153572, 4359021001802969, 102449761824020547, 24031266839093634, 44968509031371303, 107959083381918430, 60545903899444239, 70705588077792440, 53520341948307733, 143088102219075944, 124134275347498089, 95493333086931173, 121754939329553091, 56354138896041550, 109334699763567899, 77927791492407255, 79085204279536188, 83861566744974511, 10024306034785599, 23501354668161625, 38828600909272044, 78610551827551897, 28617582279887779, 62809775957163588, 29687863120100137, 140444090931275537, 131915626160053843, 67924669468490850, 121564485614660771, 99853533681801351, 128781973791354956, 75737765160666167, 43985012169968427, 24926226896061047, 25378275596331262, 45706291816468981, 32865513464476540, 126241825803559853, 138844180564723706, 112920521131495397, 73774185826491048, 74415415102963547, 30546740860222401, 41280934022069546, 14394706533538590, 39489541355076756, 110949646625133154, 628061189273282, 86822589006866533, 45581882622939867][i]!
def words (i : Fin 57) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 57 rawWords i=rowTotals i)

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
private theorem row51 : rowAgrees 51=true := by decide +kernel
private theorem row52 : rowAgrees 52=true := by decide +kernel
private theorem row53 : rowAgrees 53=true := by decide +kernel
private theorem row54 : rowAgrees 54=true := by decide +kernel
private theorem row55 : rowAgrees 55=true := by decide +kernel
private theorem row56 : rowAgrees 56=true := by decide +kernel
private theorem rowChecked : allBelow 57 rowAgrees=true := by
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
  have h := allBelow_step h row51
  have h := allBelow_step h row52
  have h := allBelow_step h row53
  have h := allBelow_step h row54
  have h := allBelow_step h row55
  have h := allBelow_step h row56
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 57, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 57, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-3192:ℤ) := by
  change cubicInteger (fun i : Fin 57 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-3192:ℤ) ∧
    87*(57:ℤ)^3+375*57*(4*57-3)+1000*((wordMatrix words-1)^3).trace-
      1110*113*(57-1)=(10705086:ℤ) ∧ 0≤(10705086:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 57 ⊕ Fin 57 → Fin 114
  | .inl i => Fin.ofNat 114 (#[0, 3, 6, 7, 9, 11, 14, 16, 19, 20, 22, 23, 26, 27, 28, 29, 31, 34, 35, 37, 41, 42, 43, 44, 45, 46, 47, 53, 55, 58, 60, 66, 67, 68, 69, 70, 71, 72, 76, 78, 79, 82, 84, 85, 86, 87, 90, 91, 93, 94, 97, 99, 102, 104, 106, 107, 110][i.val]!)
  | .inr i => Fin.ofNat 114 (#[1, 2, 4, 5, 8, 10, 12, 13, 15, 17, 18, 21, 24, 25, 30, 32, 33, 36, 38, 39, 40, 48, 49, 50, 51, 52, 54, 56, 57, 59, 61, 62, 63, 64, 65, 73, 74, 75, 77, 80, 81, 83, 88, 89, 92, 95, 96, 98, 100, 101, 103, 105, 108, 109, 111, 112, 113][i.val]!)

def pointPosition (i : Fin 114) : Fin 57 ⊕ Fin 57 :=
  let j : ℕ := #[0, 57, 58, 1, 59, 60, 2, 3, 61, 4, 62, 5, 63, 64, 6, 65, 7, 66, 67, 8, 9, 68, 10, 11, 69, 70, 12, 13, 14, 15, 71, 16, 72, 73, 17, 18, 74, 19, 75, 76, 77, 20, 21, 22, 23, 24, 25, 26, 78, 79, 80, 81, 82, 27, 83, 28, 84, 85, 29, 86, 30, 87, 88, 89, 90, 91, 31, 32, 33, 34, 35, 36, 37, 92, 93, 94, 38, 95, 39, 40, 96, 97, 41, 98, 42, 43, 44, 45, 99, 100, 46, 47, 101, 48, 49, 102, 103, 50, 104, 51, 105, 106, 52, 107, 53, 108, 54, 55, 109, 110, 56, 111, 112, 113][i.val]!
  if j<57 then .inl (Fin.ofNat 57 j) else .inr (Fin.ofNat 57 (j-57))

def indexing : (Fin 57 ⊕ Fin 57) ≃ Fin 114 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 57,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*113)*(113-1)^56) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 56 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 56 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 56=(2*113)*(113-1)^56 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegative


namespace SplitSquaresOpposite
def rawWords (i : ℕ) : ℕ := #[37616208660074116, 20881770811380776, 10377982206851601, 6330723198138498, 21628552248341540, 53419533738400402, 23636416055350272, 38090810770391593, 49177597776112640, 17839639808749733, 59359393092753747, 16765859158893869, 33223855120369278, 33926391274015516, 65766992141685802, 61754578408444436, 68837041084319913, 24098930402828643, 45910875480029406, 63639119387018215, 66549903656289091, 56424211757606607, 41041619949757727, 3305500517620341, 3374055978798746, 15569408188620111, 22414062647372276, 43887974338970040, 8307111172233177, 13395935436375538, 68319590229347052, 25176101956698064, 49075688089222608, 69987455558022025, 68509269521182227, 54817951375914551, 65235704284637255, 34654450657122501, 55878299202337194, 41959685837254959, 11338519254312667, 23688639672051095, 15991735771193630, 35574841689444462, 50846511024441820, 57027299306948427, 46457791701878524, 57563261660533, 41729441608944353, 44519207509962, 20647527901762493, 10182730691177266, 18329575461469800, 38383089283332900, 5676223480722514, 9412778527671713, 0][i]!
def words (i : Fin 57) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 177, 225]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 57 rawWords i=rowTotals i)

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
private theorem row51 : rowAgrees 51=true := by decide +kernel
private theorem row52 : rowAgrees 52=true := by decide +kernel
private theorem row53 : rowAgrees 53=true := by decide +kernel
private theorem row54 : rowAgrees 54=true := by decide +kernel
private theorem row55 : rowAgrees 55=true := by decide +kernel
private theorem row56 : rowAgrees 56=true := by decide +kernel
private theorem rowChecked : allBelow 57 rowAgrees=true := by
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
  have h := allBelow_step h row51
  have h := allBelow_step h row52
  have h := allBelow_step h row53
  have h := allBelow_step h row54
  have h := allBelow_step h row55
  have h := allBelow_step h row56
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 57, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 57, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(504:ℤ) := by
  change cubicInteger (fun i : Fin 57 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(504:ℤ) ∧
    87*(57:ℤ)^3+375*57*(4*57-3)+1000*((wordMatrix words-1)^3).trace-
      1110*113*(57-1)=(14401086:ℤ) ∧ 0≤(14401086:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 57 ⊕ Fin 57 → Fin 114
  | .inl i => Fin.ofNat 114 (#[3, 5, 6, 10, 12, 17, 19, 20, 21, 23, 24, 27, 29, 33, 34, 35, 37, 38, 39, 40, 42, 43, 45, 46, 47, 48, 54, 55, 58, 59, 65, 66, 67, 68, 70, 71, 73, 74, 75, 76, 78, 79, 80, 84, 86, 89, 90, 92, 93, 94, 96, 101, 103, 107, 108, 110, 113][i.val]!)
  | .inr i => Fin.ofNat 114 (#[0, 1, 2, 4, 7, 8, 9, 11, 13, 14, 15, 16, 18, 22, 25, 26, 28, 30, 31, 32, 36, 41, 44, 49, 50, 51, 52, 53, 56, 57, 60, 61, 62, 63, 64, 69, 72, 77, 81, 82, 83, 85, 87, 88, 91, 95, 97, 98, 99, 100, 102, 104, 105, 106, 109, 111, 112][i.val]!)

def pointPosition (i : Fin 114) : Fin 57 ⊕ Fin 57 :=
  let j : ℕ := #[57, 58, 59, 0, 60, 1, 2, 61, 62, 63, 3, 64, 4, 65, 66, 67, 68, 5, 69, 6, 7, 8, 70, 9, 10, 71, 72, 11, 73, 12, 74, 75, 76, 13, 14, 15, 77, 16, 17, 18, 19, 78, 20, 21, 79, 22, 23, 24, 25, 80, 81, 82, 83, 84, 26, 27, 85, 86, 28, 29, 87, 88, 89, 90, 91, 30, 31, 32, 33, 92, 34, 35, 93, 36, 37, 38, 39, 94, 40, 41, 42, 95, 96, 97, 43, 98, 44, 99, 100, 45, 46, 101, 47, 48, 49, 102, 50, 103, 104, 105, 106, 51, 107, 52, 108, 109, 110, 53, 54, 111, 55, 112, 113, 56][i.val]!
  if j<57 then .inl (Fin.ofNat 57 j) else .inr (Fin.ofNat 57 (j-57))

def indexing : (Fin 57 ⊕ Fin 57) ≃ Fin 114 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 57,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*113)*(113-1)^56) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 56 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 56 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 56=(2*113)*(113-1)^56 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquaresOpposite


namespace SplitNonsquaresOpposite
def rawWords (i : ℕ) : ℕ := #[28775577187629260, 47389485762769176, 56687372883109161, 470559955337351, 29105041530333634, 39080848484320004, 39753341620159761, 16517587098479641, 5989507976544374, 30572908500494368, 52665386357280964, 55852560007922321, 59521198569333763, 30918866697949847, 44940542316774698, 42452976421452925, 17298749949225193, 35713332268294494, 61900427211330288, 69270217105295019, 68001095760877855, 63836490984333935, 1194946910877551, 12516379402127070, 16023223084228084, 23075650521181100, 54569144483139544, 19942464184655347, 58467860687199074, 7866701032618883, 15152790807830410, 13433730434643740, 34730016980463156, 69506333035166752, 69317796060681031, 69973283575261583, 60062782189934703, 4303518344697819, 34488491897816958, 42524796155113148, 53546503154912105, 23820314478941689, 65664785497267126, 54084060521983691, 38634128456398435, 9863803433343197, 1148128235862326, 30964768570794664, 42842135402476892, 38458613432245425, 9222389343447889, 19023104622159590, 63336127735518592, 41840058524444307, 6911938621487637, 14387788593814630, 0][i]!
def words (i : Fin 57) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 113]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 57 rawWords i=rowTotals i)

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
private theorem row51 : rowAgrees 51=true := by decide +kernel
private theorem row52 : rowAgrees 52=true := by decide +kernel
private theorem row53 : rowAgrees 53=true := by decide +kernel
private theorem row54 : rowAgrees 54=true := by decide +kernel
private theorem row55 : rowAgrees 55=true := by decide +kernel
private theorem row56 : rowAgrees 56=true := by decide +kernel
private theorem rowChecked : allBelow 57 rowAgrees=true := by
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
  have h := allBelow_step h row51
  have h := allBelow_step h row52
  have h := allBelow_step h row53
  have h := allBelow_step h row54
  have h := allBelow_step h row55
  have h := allBelow_step h row56
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 57, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 57, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-504:ℤ) := by
  change cubicInteger (fun i : Fin 57 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-504:ℤ) ∧
    87*(57:ℤ)^3+375*57*(4*57-3)+1000*((wordMatrix words-1)^3).trace-
      1110*113*(57-1)=(13393086:ℤ) ∧ 0≤(13393086:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 57 ⊕ Fin 57 → Fin 114
  | .inl i => Fin.ofNat 114 (#[1, 2, 4, 7, 8, 9, 11, 13, 14, 15, 16, 18, 22, 25, 26, 28, 30, 31, 32, 36, 41, 44, 49, 50, 51, 52, 53, 56, 57, 60, 61, 62, 63, 64, 69, 72, 77, 81, 82, 83, 85, 87, 88, 91, 95, 97, 98, 99, 100, 102, 104, 105, 106, 109, 111, 112, 113][i.val]!)
  | .inr i => Fin.ofNat 114 (#[0, 3, 5, 6, 10, 12, 17, 19, 20, 21, 23, 24, 27, 29, 33, 34, 35, 37, 38, 39, 40, 42, 43, 45, 46, 47, 48, 54, 55, 58, 59, 65, 66, 67, 68, 70, 71, 73, 74, 75, 76, 78, 79, 80, 84, 86, 89, 90, 92, 93, 94, 96, 101, 103, 107, 108, 110][i.val]!)

def pointPosition (i : Fin 114) : Fin 57 ⊕ Fin 57 :=
  let j : ℕ := #[57, 0, 1, 58, 2, 59, 60, 3, 4, 5, 61, 6, 62, 7, 8, 9, 10, 63, 11, 64, 65, 66, 12, 67, 68, 13, 14, 69, 15, 70, 16, 17, 18, 71, 72, 73, 19, 74, 75, 76, 77, 20, 78, 79, 21, 80, 81, 82, 83, 22, 23, 24, 25, 26, 84, 85, 27, 28, 86, 87, 29, 30, 31, 32, 33, 88, 89, 90, 91, 34, 92, 93, 35, 94, 95, 96, 97, 36, 98, 99, 100, 37, 38, 39, 101, 40, 102, 41, 42, 103, 104, 43, 105, 106, 107, 44, 108, 45, 46, 47, 48, 109, 49, 110, 50, 51, 52, 111, 112, 53, 113, 54, 55, 56][i.val]!
  if j<57 then .inl (Fin.ofNat 57 j) else .inr (Fin.ofNat 57 (j-57))

def indexing : (Fin 57 ⊕ Fin 57) ≃ Fin 114 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 57,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*113)*(113-1)^56) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 56 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 56 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 56=(2*113)*(113-1)^56 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquaresOpposite


namespace NonsplitNegativeOpposite
def rawWords (i : ℕ) : ℕ := #[31562512746839172, 48684074268239960, 56795211456395297, 41284098127082290, 28032296139400330, 19509623105601932, 7554470452631298, 12419535398495281, 34392284941167720, 28840360714567752, 58791227567135185, 21247664598619399, 6115500604148813, 31510421200454047, 17992885921330337, 62347757113049560, 69688870694701284, 64777990485660611, 71023971245592333, 47430018179204463, 24953396838550155, 1239579185527227, 5768074070909287, 16042254889470974, 11484061195884252, 18499465947228140, 50488999250324304, 19961534307077811, 57827514954241890, 3050623136103117, 15733504743873922, 16724758251778836, 35978941325541148, 64887749145034280, 62377908670752288, 58918435704235290, 69419601864851733, 49805149689334335, 55110357944681575, 10997802663782895, 7740711481835963, 37485425194317820, 70230233192681462, 50157815905410472, 63235856684891858, 39294556385213195, 5067004811964006, 6251236510266462, 39450261751724084, 18271494916500312, 13935860393702050, 22840179498478022, 21617763409057097, 37186255365038995, 7340748086685493, 9357385454814222, 0][i]!
def words (i : Fin 57) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225, 225]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 57 rawWords i=rowTotals i)

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
private theorem row51 : rowAgrees 51=true := by decide +kernel
private theorem row52 : rowAgrees 52=true := by decide +kernel
private theorem row53 : rowAgrees 53=true := by decide +kernel
private theorem row54 : rowAgrees 54=true := by decide +kernel
private theorem row55 : rowAgrees 55=true := by decide +kernel
private theorem row56 : rowAgrees 56=true := by decide +kernel
private theorem rowChecked : allBelow 57 rowAgrees=true := by
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
  have h := allBelow_step h row51
  have h := allBelow_step h row52
  have h := allBelow_step h row53
  have h := allBelow_step h row54
  have h := allBelow_step h row55
  have h := allBelow_step h row56
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 57, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 57, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(3192:ℤ) := by
  change cubicInteger (fun i : Fin 57 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(3192:ℤ) ∧
    87*(57:ℤ)^3+375*57*(4*57-3)+1000*((wordMatrix words-1)^3).trace-
      1110*113*(57-1)=(17089086:ℤ) ∧ 0≤(17089086:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 57 ⊕ Fin 57 → Fin 114
  | .inl i => Fin.ofNat 114 (#[1, 2, 4, 5, 8, 10, 12, 13, 15, 17, 18, 21, 24, 25, 30, 32, 33, 36, 38, 39, 40, 48, 49, 50, 51, 52, 54, 56, 57, 59, 61, 62, 63, 64, 65, 73, 74, 75, 77, 80, 81, 83, 88, 89, 92, 95, 96, 98, 100, 101, 103, 105, 108, 109, 111, 112, 113][i.val]!)
  | .inr i => Fin.ofNat 114 (#[0, 3, 6, 7, 9, 11, 14, 16, 19, 20, 22, 23, 26, 27, 28, 29, 31, 34, 35, 37, 41, 42, 43, 44, 45, 46, 47, 53, 55, 58, 60, 66, 67, 68, 69, 70, 71, 72, 76, 78, 79, 82, 84, 85, 86, 87, 90, 91, 93, 94, 97, 99, 102, 104, 106, 107, 110][i.val]!)

def pointPosition (i : Fin 114) : Fin 57 ⊕ Fin 57 :=
  let j : ℕ := #[57, 0, 1, 58, 2, 3, 59, 60, 4, 61, 5, 62, 6, 7, 63, 8, 64, 9, 10, 65, 66, 11, 67, 68, 12, 13, 69, 70, 71, 72, 14, 73, 15, 16, 74, 75, 17, 76, 18, 19, 20, 77, 78, 79, 80, 81, 82, 83, 21, 22, 23, 24, 25, 84, 26, 85, 27, 28, 86, 29, 87, 30, 31, 32, 33, 34, 88, 89, 90, 91, 92, 93, 94, 35, 36, 37, 95, 38, 96, 97, 39, 40, 98, 41, 99, 100, 101, 102, 42, 43, 103, 104, 44, 105, 106, 45, 46, 107, 47, 108, 48, 49, 109, 50, 110, 51, 111, 112, 52, 53, 113, 54, 55, 56][i.val]!
  if j<57 then .inl (Fin.ofNat 57 j) else .inr (Fin.ofNat 57 (j-57))

def indexing : (Fin 57 ⊕ Fin 57) ≃ Fin 114 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 57,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*113)*(113-1)^56) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 56 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 56 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 56=(2*113)*(113-1)^56 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegativeOpposite

end PaleyBits113
