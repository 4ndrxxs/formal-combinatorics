import Quantum.Hadamard.ConferenceBitCompletion
open Hadamard.BitTrace Hadamard.DeterminantRatio Matrix
set_option maxHeartbeats 12000000
set_option maxRecDepth 60000
namespace PaleyBits137

def rawFull (i : ℕ) : ℕ := #[30179077125861480759279369339831925617768, 60358154251722961518558738679663851235536, 120716308503445923037117477359327702471072, 67208045143371352780987155713590080676673, 134416090286742705561974311427180161353346, 94607608709964917830700823849294998441221, 14990645556409342368153848693524672616971, 29981291112818684736307697387049345233942, 59962582225637369472615394774098690467884, 119925164451274738945230789548197380935768, 65625757039028984597213780091329437606065, 131251514078057969194427560182658875212130, 88278456292595445095607321360252426158789, 2332340721670396897966843715439528052107, 4664681443340793795933687430879056104214, 9329362886681587591867374861758112208428, 18658725773363175183734749723516224416856, 37317451546726350367469499447032448833712, 74634903093452700734938998894064897667424, 149269806186905401469877997788129795334848, 124315040510290309646508196571194266404225, 74405509157060125999768594137323208542979, 148811018314120251999537188274646417085958, 123397464764720010705826577544227509906445, 72570357665919528118405356083389695547419, 145140715331839056236810712166779391094838, 116056858800157619180373625328493457924205, 57889145736794745067499451651921591582939, 115778291473589490134998903303843183165878, 57332011083658486976750007602621042066285, 114664022167316973953500015205242084132570, 55103472471113454613752231405418843999669, 110206944942226909227504462810837687999338, 46189318020933325161761126616610051733205, 92378636041866650323522253233220103466410, 10532700220212807353796707461374882667349, 21065400440425614707593414922749765334698, 42130800880851229415186829845499530669396, 84261601761702458830373659690999061338792, 168523203523404917660747319381998122677584, 162821835183289342028246839758930921089697, 151419098503058190763245880512796517913923, 128613625142595888233243962020527711562375, 83002678421671283173240125035990098859279, 166005356843342566346480250071980197718558, 157786141823164639399712701138895071171645, 141347711782808785506177603272724818077819, 108470851702097077719107407540384311890167, 42717131540673662144967016075703299514863, 85434263081347324289934032151406599029726, 170868526162694648579868064302813198059452, 167512480461868803866488329600561071853433, 160800389060217114439728860196056819441395, 147376206256913735586209921387048314617319, 120527840650306977879172043769031304969167, 66831109437093462465096288532997285672863, 133662218874186924930192577065994571345726, 93099865884853356567137355126923818425981, 11975159906186219841026911248782312586491, 23950319812372439682053822497564625172982, 47900639624744879364107644995129250345964, 95801279249489758728215289990258500691928, 17377986635459024163182780975451677118385, 34755973270918048326365561950903354236770, 69511946541836096652731123901806708473540, 139023893083672193305462247803613416947080, 103823214303823893317676696602161509628689, 33421856744127293342105594199257694991907, 66843713488254586684211188398515389983814, 133687426976509173368422376797030779967628, 93150282089497853443596954588996235669785, 12075992315475213593946110172927147074099, 24151984630950427187892220345854294148198, 48303969261900854375784440691708588296396, 96607938523801708751568881383417176592792, 18991305184082924209889963761769028920113, 37982610368165848419779927523538057840226, 75965220736331696839559855047076115680452, 151930441472663393679119710094152231360904, 129636311081806294064991621183239138456337, 85048050300092094836735443361412952647203, 170096100600184189673470886722825905294406, 165967629336847886053693974440586486323341, 157710686810175278814140149876107648381211, 141196801756830064335032500747149972496951, 108169031650139635376817202489234620728431, 42113491436758777460386605973403917191391, 84226982873517554920773211946807834382782, 168453965747035109841546423893615668765564, 162683359630549726389845048782166013265657, 151142147397578959486442298559266702265843, 128059722931637425679636798113468080266215, 81894873999754358066025797221870836266959, 163789747999508716132051594443741672533918, 153354924135496938970855389882418020802365, 132485276407473384648462980759770717339259, 90745980951426276003678162514476110413047, 7267390039332058714108526023886896560623, 14534780078664117428217052047773793121246, 29069560157328234856434104095547586242492, 58139120314656469712868208191095172484984, 116278240629312939425736416382190344969968, 58331909395105385558225033759315365674465, 116663818790210771116450067518630731348930, 59103065716901048939652336032196138432389, 118206131433802097879304672064392276864778, 62187691004083702465361545123719229464085, 124375382008167404930723090247438458928170, 74526192152814316568198381489811593590869, 149052384305628633136396762979623187181738, 123880196747736772979545726954181050098005, 73535821631953052665843654903296775930539, 147071643263906105331687309806593551861078, 119918714664291717370126820608121779456685, 65612857465062941447005842211178234647899, 131225714930125882894011684422356469295798, 88226857996731272494775569839647614326125, 2229144129942051696303340674229904386779, 4458288259884103392606681348459808773558, 8916576519768206785213362696919617547116, 17833153039536413570426725393839235094232, 35666306079072827140853450787678470188464, 71332612158145654281706901575356940376928, 142665224316291308563413803150713880753856, 111105876769062123833579807296362437242241, 47987181674603754373911815587659550219011, 95974363349207508747823631175319100438022, 17724154834894524202399463345572876610573, 35448309669789048404798926691145753221146, 70896619339578096809597853382291506442292, 141793238679156193619195706764583012884584, 109361905494791893945143614524100701503697, 44499239126063294597039430043136078741923, 88998478252126589194078860086272157483846, 3772384640732685094909921167478990702221, 7544769281465370189819842334957981404442, 15089538562930740379639684669915962808884, 0][i]!
def fullRows (i : Fin 138) : ℕ := rawFull i.val

private theorem fullSymmetric : (wordMatrix fullRows).IsSymm := by
  have h : ∀ i j : Fin 138, sign (fullRows i) j.val=sign (fullRows j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem fullDiagonal : ∀ i : Fin 138, sign (fullRows i) i.val=1 := by decide +kernel
private theorem lower0 : (lowerRow 138 rawFull) 0=true := by decide +kernel
private theorem lower1 : (lowerRow 138 rawFull) 1=true := by decide +kernel
private theorem lower2 : (lowerRow 138 rawFull) 2=true := by decide +kernel
private theorem lower3 : (lowerRow 138 rawFull) 3=true := by decide +kernel
private theorem lower4 : (lowerRow 138 rawFull) 4=true := by decide +kernel
private theorem lower5 : (lowerRow 138 rawFull) 5=true := by decide +kernel
private theorem lower6 : (lowerRow 138 rawFull) 6=true := by decide +kernel
private theorem lower7 : (lowerRow 138 rawFull) 7=true := by decide +kernel
private theorem lower8 : (lowerRow 138 rawFull) 8=true := by decide +kernel
private theorem lower9 : (lowerRow 138 rawFull) 9=true := by decide +kernel
private theorem lower10 : (lowerRow 138 rawFull) 10=true := by decide +kernel
private theorem lower11 : (lowerRow 138 rawFull) 11=true := by decide +kernel
private theorem lower12 : (lowerRow 138 rawFull) 12=true := by decide +kernel
private theorem lower13 : (lowerRow 138 rawFull) 13=true := by decide +kernel
private theorem lower14 : (lowerRow 138 rawFull) 14=true := by decide +kernel
private theorem lower15 : (lowerRow 138 rawFull) 15=true := by decide +kernel
private theorem lower16 : (lowerRow 138 rawFull) 16=true := by decide +kernel
private theorem lower17 : (lowerRow 138 rawFull) 17=true := by decide +kernel
private theorem lower18 : (lowerRow 138 rawFull) 18=true := by decide +kernel
private theorem lower19 : (lowerRow 138 rawFull) 19=true := by decide +kernel
private theorem lower20 : (lowerRow 138 rawFull) 20=true := by decide +kernel
private theorem lower21 : (lowerRow 138 rawFull) 21=true := by decide +kernel
private theorem lower22 : (lowerRow 138 rawFull) 22=true := by decide +kernel
private theorem lower23 : (lowerRow 138 rawFull) 23=true := by decide +kernel
private theorem lower24 : (lowerRow 138 rawFull) 24=true := by decide +kernel
private theorem lower25 : (lowerRow 138 rawFull) 25=true := by decide +kernel
private theorem lower26 : (lowerRow 138 rawFull) 26=true := by decide +kernel
private theorem lower27 : (lowerRow 138 rawFull) 27=true := by decide +kernel
private theorem lower28 : (lowerRow 138 rawFull) 28=true := by decide +kernel
private theorem lower29 : (lowerRow 138 rawFull) 29=true := by decide +kernel
private theorem lower30 : (lowerRow 138 rawFull) 30=true := by decide +kernel
private theorem lower31 : (lowerRow 138 rawFull) 31=true := by decide +kernel
private theorem lower32 : (lowerRow 138 rawFull) 32=true := by decide +kernel
private theorem lower33 : (lowerRow 138 rawFull) 33=true := by decide +kernel
private theorem lower34 : (lowerRow 138 rawFull) 34=true := by decide +kernel
private theorem lower35 : (lowerRow 138 rawFull) 35=true := by decide +kernel
private theorem lower36 : (lowerRow 138 rawFull) 36=true := by decide +kernel
private theorem lower37 : (lowerRow 138 rawFull) 37=true := by decide +kernel
private theorem lower38 : (lowerRow 138 rawFull) 38=true := by decide +kernel
private theorem lower39 : (lowerRow 138 rawFull) 39=true := by decide +kernel
private theorem lower40 : (lowerRow 138 rawFull) 40=true := by decide +kernel
private theorem lower41 : (lowerRow 138 rawFull) 41=true := by decide +kernel
private theorem lower42 : (lowerRow 138 rawFull) 42=true := by decide +kernel
private theorem lower43 : (lowerRow 138 rawFull) 43=true := by decide +kernel
private theorem lower44 : (lowerRow 138 rawFull) 44=true := by decide +kernel
private theorem lower45 : (lowerRow 138 rawFull) 45=true := by decide +kernel
private theorem lower46 : (lowerRow 138 rawFull) 46=true := by decide +kernel
private theorem lower47 : (lowerRow 138 rawFull) 47=true := by decide +kernel
private theorem lower48 : (lowerRow 138 rawFull) 48=true := by decide +kernel
private theorem lower49 : (lowerRow 138 rawFull) 49=true := by decide +kernel
private theorem lower50 : (lowerRow 138 rawFull) 50=true := by decide +kernel
private theorem lower51 : (lowerRow 138 rawFull) 51=true := by decide +kernel
private theorem lower52 : (lowerRow 138 rawFull) 52=true := by decide +kernel
private theorem lower53 : (lowerRow 138 rawFull) 53=true := by decide +kernel
private theorem lower54 : (lowerRow 138 rawFull) 54=true := by decide +kernel
private theorem lower55 : (lowerRow 138 rawFull) 55=true := by decide +kernel
private theorem lower56 : (lowerRow 138 rawFull) 56=true := by decide +kernel
private theorem lower57 : (lowerRow 138 rawFull) 57=true := by decide +kernel
private theorem lower58 : (lowerRow 138 rawFull) 58=true := by decide +kernel
private theorem lower59 : (lowerRow 138 rawFull) 59=true := by decide +kernel
private theorem lower60 : (lowerRow 138 rawFull) 60=true := by decide +kernel
private theorem lower61 : (lowerRow 138 rawFull) 61=true := by decide +kernel
private theorem lower62 : (lowerRow 138 rawFull) 62=true := by decide +kernel
private theorem lower63 : (lowerRow 138 rawFull) 63=true := by decide +kernel
private theorem lower64 : (lowerRow 138 rawFull) 64=true := by decide +kernel
private theorem lower65 : (lowerRow 138 rawFull) 65=true := by decide +kernel
private theorem lower66 : (lowerRow 138 rawFull) 66=true := by decide +kernel
private theorem lower67 : (lowerRow 138 rawFull) 67=true := by decide +kernel
private theorem lower68 : (lowerRow 138 rawFull) 68=true := by decide +kernel
private theorem lower69 : (lowerRow 138 rawFull) 69=true := by decide +kernel
private theorem lower70 : (lowerRow 138 rawFull) 70=true := by decide +kernel
private theorem lower71 : (lowerRow 138 rawFull) 71=true := by decide +kernel
private theorem lower72 : (lowerRow 138 rawFull) 72=true := by decide +kernel
private theorem lower73 : (lowerRow 138 rawFull) 73=true := by decide +kernel
private theorem lower74 : (lowerRow 138 rawFull) 74=true := by decide +kernel
private theorem lower75 : (lowerRow 138 rawFull) 75=true := by decide +kernel
private theorem lower76 : (lowerRow 138 rawFull) 76=true := by decide +kernel
private theorem lower77 : (lowerRow 138 rawFull) 77=true := by decide +kernel
private theorem lower78 : (lowerRow 138 rawFull) 78=true := by decide +kernel
private theorem lower79 : (lowerRow 138 rawFull) 79=true := by decide +kernel
private theorem lower80 : (lowerRow 138 rawFull) 80=true := by decide +kernel
private theorem lower81 : (lowerRow 138 rawFull) 81=true := by decide +kernel
private theorem lower82 : (lowerRow 138 rawFull) 82=true := by decide +kernel
private theorem lower83 : (lowerRow 138 rawFull) 83=true := by decide +kernel
private theorem lower84 : (lowerRow 138 rawFull) 84=true := by decide +kernel
private theorem lower85 : (lowerRow 138 rawFull) 85=true := by decide +kernel
private theorem lower86 : (lowerRow 138 rawFull) 86=true := by decide +kernel
private theorem lower87 : (lowerRow 138 rawFull) 87=true := by decide +kernel
private theorem lower88 : (lowerRow 138 rawFull) 88=true := by decide +kernel
private theorem lower89 : (lowerRow 138 rawFull) 89=true := by decide +kernel
private theorem lower90 : (lowerRow 138 rawFull) 90=true := by decide +kernel
private theorem lower91 : (lowerRow 138 rawFull) 91=true := by decide +kernel
private theorem lower92 : (lowerRow 138 rawFull) 92=true := by decide +kernel
private theorem lower93 : (lowerRow 138 rawFull) 93=true := by decide +kernel
private theorem lower94 : (lowerRow 138 rawFull) 94=true := by decide +kernel
private theorem lower95 : (lowerRow 138 rawFull) 95=true := by decide +kernel
private theorem lower96 : (lowerRow 138 rawFull) 96=true := by decide +kernel
private theorem lower97 : (lowerRow 138 rawFull) 97=true := by decide +kernel
private theorem lower98 : (lowerRow 138 rawFull) 98=true := by decide +kernel
private theorem lower99 : (lowerRow 138 rawFull) 99=true := by decide +kernel
private theorem lower100 : (lowerRow 138 rawFull) 100=true := by decide +kernel
private theorem lower101 : (lowerRow 138 rawFull) 101=true := by decide +kernel
private theorem lower102 : (lowerRow 138 rawFull) 102=true := by decide +kernel
private theorem lower103 : (lowerRow 138 rawFull) 103=true := by decide +kernel
private theorem lower104 : (lowerRow 138 rawFull) 104=true := by decide +kernel
private theorem lower105 : (lowerRow 138 rawFull) 105=true := by decide +kernel
private theorem lower106 : (lowerRow 138 rawFull) 106=true := by decide +kernel
private theorem lower107 : (lowerRow 138 rawFull) 107=true := by decide +kernel
private theorem lower108 : (lowerRow 138 rawFull) 108=true := by decide +kernel
private theorem lower109 : (lowerRow 138 rawFull) 109=true := by decide +kernel
private theorem lower110 : (lowerRow 138 rawFull) 110=true := by decide +kernel
private theorem lower111 : (lowerRow 138 rawFull) 111=true := by decide +kernel
private theorem lower112 : (lowerRow 138 rawFull) 112=true := by decide +kernel
private theorem lower113 : (lowerRow 138 rawFull) 113=true := by decide +kernel
private theorem lower114 : (lowerRow 138 rawFull) 114=true := by decide +kernel
private theorem lower115 : (lowerRow 138 rawFull) 115=true := by decide +kernel
private theorem lower116 : (lowerRow 138 rawFull) 116=true := by decide +kernel
private theorem lower117 : (lowerRow 138 rawFull) 117=true := by decide +kernel
private theorem lower118 : (lowerRow 138 rawFull) 118=true := by decide +kernel
private theorem lower119 : (lowerRow 138 rawFull) 119=true := by decide +kernel
private theorem lower120 : (lowerRow 138 rawFull) 120=true := by decide +kernel
private theorem lower121 : (lowerRow 138 rawFull) 121=true := by decide +kernel
private theorem lower122 : (lowerRow 138 rawFull) 122=true := by decide +kernel
private theorem lower123 : (lowerRow 138 rawFull) 123=true := by decide +kernel
private theorem lower124 : (lowerRow 138 rawFull) 124=true := by decide +kernel
private theorem lower125 : (lowerRow 138 rawFull) 125=true := by decide +kernel
private theorem lower126 : (lowerRow 138 rawFull) 126=true := by decide +kernel
private theorem lower127 : (lowerRow 138 rawFull) 127=true := by decide +kernel
private theorem lower128 : (lowerRow 138 rawFull) 128=true := by decide +kernel
private theorem lower129 : (lowerRow 138 rawFull) 129=true := by decide +kernel
private theorem lower130 : (lowerRow 138 rawFull) 130=true := by decide +kernel
private theorem lower131 : (lowerRow 138 rawFull) 131=true := by decide +kernel
private theorem lower132 : (lowerRow 138 rawFull) 132=true := by decide +kernel
private theorem lower133 : (lowerRow 138 rawFull) 133=true := by decide +kernel
private theorem lower134 : (lowerRow 138 rawFull) 134=true := by decide +kernel
private theorem lower135 : (lowerRow 138 rawFull) 135=true := by decide +kernel
private theorem lower136 : (lowerRow 138 rawFull) 136=true := by decide +kernel
private theorem lower137 : (lowerRow 138 rawFull) 137=true := by decide +kernel
private theorem lowerChecked : allBelow 138 (lowerRow 138 rawFull)=true := by
  have h : allBelow 0 (lowerRow 138 rawFull)=true := rfl
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
  have h := allBelow_step h lower114
  have h := allBelow_step h lower115
  have h := allBelow_step h lower116
  have h := allBelow_step h lower117
  have h := allBelow_step h lower118
  have h := allBelow_step h lower119
  have h := allBelow_step h lower120
  have h := allBelow_step h lower121
  have h := allBelow_step h lower122
  have h := allBelow_step h lower123
  have h := allBelow_step h lower124
  have h := allBelow_step h lower125
  have h := allBelow_step h lower126
  have h := allBelow_step h lower127
  have h := allBelow_step h lower128
  have h := allBelow_step h lower129
  have h := allBelow_step h lower130
  have h := allBelow_step h lower131
  have h := allBelow_step h lower132
  have h := allBelow_step h lower133
  have h := allBelow_step h lower134
  have h := allBelow_step h lower135
  have h := allBelow_step h lower136
  have h := allBelow_step h lower137
  exact h

private theorem fullPairs : ∀ i j : Fin 138, i≠j →
    correlation 138 (fullRows i) (fullRows j)=2*sign (fullRows i) j.val :=
  correlations_of_lower rawFull fullSymmetric lowerChecked


namespace SplitSquares
def rawWords (i : ℕ) : ℕ := #[0, 235339095613479305624, 392263805983464211248, 471383883177911356754, 3289575424620439566, 223328432662392934788, 377478192933193016072, 453863524857558076706, 47642987402331957486, 35343059366198743108, 135277940805240709256, 122963918487766057368, 181366554871225057824, 574780564341883454800, 567478940701335333958, 537169391706429415950, 336028421418320975422, 301987500491501770842, 331596886557702775010, 367145577804447433138, 126791106443079714386, 110560154874488327596, 290331628820408671184, 585335707069993989672, 588170895454129363662, 249505896271457670526, 572740328076850899580, 450879787148617615342, 60554151660560530878, 190366923369460841332, 306962567054918367096, 130112450838642253538, 191094691858781076692, 446710167991524194736, 193593587781968449414, 451720441601136877460, 62824901476214029062, 199419851666641909396, 329645277171367636024, 142619311446477762882, 216120788764634047124, 579864018100289963184, 552851240989362955142, 287442709394409557054, 584162860424463276140, 531932779025693430270, 94181020721439127422, 54648976635626598268, 247611313706207191016, 342998747240592998104, 357451091466530404850, 327538258602579650530, 415502680872673730178, 573777894237952195346, 517783798178535398958, 452912395958728700126, 49055542177211172158, 19613444620517362404, 117638995901431911768, 78516695906913790648, 156969285836326016480, 549152498244033260112, 316769025622189954630, 77361354320021052298, 154648368528852039180, 516884492887541771520, 344467245264165465190, 58862398076606279850, 117669547806739652812][i]!
def words (i : Fin 69) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[137, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 69 rawWords i=rowTotals i)

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
private theorem row57 : rowAgrees 57=true := by decide +kernel
private theorem row58 : rowAgrees 58=true := by decide +kernel
private theorem row59 : rowAgrees 59=true := by decide +kernel
private theorem row60 : rowAgrees 60=true := by decide +kernel
private theorem row61 : rowAgrees 61=true := by decide +kernel
private theorem row62 : rowAgrees 62=true := by decide +kernel
private theorem row63 : rowAgrees 63=true := by decide +kernel
private theorem row64 : rowAgrees 64=true := by decide +kernel
private theorem row65 : rowAgrees 65=true := by decide +kernel
private theorem row66 : rowAgrees 66=true := by decide +kernel
private theorem row67 : rowAgrees 67=true := by decide +kernel
private theorem row68 : rowAgrees 68=true := by decide +kernel
private theorem rowChecked : allBelow 69 rowAgrees=true := by
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
  have h := allBelow_step h row57
  have h := allBelow_step h row58
  have h := allBelow_step h row59
  have h := allBelow_step h row60
  have h := allBelow_step h row61
  have h := allBelow_step h row62
  have h := allBelow_step h row63
  have h := allBelow_step h row64
  have h := allBelow_step h row65
  have h := allBelow_step h row66
  have h := allBelow_step h row67
  have h := allBelow_step h row68
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 69, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 69, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(3468:ℤ) := by
  change cubicInteger (fun i : Fin 69 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(3468:ℤ) ∧
    87*(69:ℤ)^3+375*69*(4*69-3)+1000*((wordMatrix words-1)^3).trace-
      1110*137*(69-1)=(28771398:ℤ) ∧ 0≤(28771398:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 69 ⊕ Fin 69 → Fin 138
  | .inl i => Fin.ofNat 138 (#[0, 1, 2, 4, 7, 8, 9, 11, 14, 15, 16, 17, 18, 19, 22, 25, 28, 30, 32, 34, 36, 37, 38, 39, 44, 49, 50, 56, 59, 60, 61, 63, 64, 65, 68, 69, 72, 73, 74, 76, 77, 78, 81, 87, 88, 93, 98, 99, 100, 101, 103, 105, 107, 109, 112, 115, 118, 119, 120, 121, 122, 123, 126, 128, 129, 130, 133, 135, 136][i.val]!)
  | .inr i => Fin.ofNat 138 (#[3, 5, 6, 10, 12, 13, 20, 21, 23, 24, 26, 27, 29, 31, 33, 35, 40, 41, 42, 43, 45, 46, 47, 48, 51, 52, 53, 54, 55, 57, 58, 62, 66, 67, 70, 71, 75, 79, 80, 82, 83, 84, 85, 86, 89, 90, 91, 92, 94, 95, 96, 97, 102, 104, 106, 108, 110, 111, 113, 114, 116, 117, 124, 125, 127, 131, 132, 134, 137][i.val]!)

def pointPosition (i : Fin 138) : Fin 69 ⊕ Fin 69 :=
  let j : ℕ := #[0, 1, 2, 69, 3, 70, 71, 4, 5, 6, 72, 7, 73, 74, 8, 9, 10, 11, 12, 13, 75, 76, 14, 77, 78, 15, 79, 80, 16, 81, 17, 82, 18, 83, 19, 84, 20, 21, 22, 23, 85, 86, 87, 88, 24, 89, 90, 91, 92, 25, 26, 93, 94, 95, 96, 97, 27, 98, 99, 28, 29, 30, 100, 31, 32, 33, 101, 102, 34, 35, 103, 104, 36, 37, 38, 105, 39, 40, 41, 106, 107, 42, 108, 109, 110, 111, 112, 43, 44, 113, 114, 115, 116, 45, 117, 118, 119, 120, 46, 47, 48, 49, 121, 50, 122, 51, 123, 52, 124, 53, 125, 126, 54, 127, 128, 55, 129, 130, 56, 57, 58, 59, 60, 61, 131, 132, 62, 133, 63, 64, 65, 134, 135, 66, 136, 67, 68, 137][i.val]!
  if j<69 then .inl (Fin.ofNat 69 j) else .inr (Fin.ofNat 69 (j-69))

def indexing : (Fin 69 ⊕ Fin 69) ≃ Fin 138 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 69,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*137)*(137-1)^68) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 68 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 68 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 68=(2*137)*(137-1)^68 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquares


namespace SplitNonsquares
def rawWords (i : ℕ) : ℕ := #[590295810358705651710, 340983073821569334857, 150762198441522259985, 82091042265417234467, 344790917321317466821, 22049486675899679753, 50979911048004012563, 386725455937083443729, 579832121478743907329, 430733953661492373715, 447029218203557441827, 450186863144389862351, 90986836720259073291, 103568321554443734543, 64469098295651993877, 72149034799381615609, 291883204105474548265, 544662976865592479941, 288594946775975027129, 586359223600164118849, 499944311021220577971, 436108841316598383927, 247397276744016104143, 264624584553791299501, 554748584523168552271, 374265900642626458783, 554759887439461509949, 157359735555141057789, 325537679408473363307, 319051979991732022515, 195380039273160952895, 31038999226067546751, 165693265554929742229, 163540744132898836449, 324775610249377095157, 220071425653603645027, 36674929435871964869, 191667580026785347525, 582487040324010040673, 572768181230502132309, 365306959611854550179, 400265351617016981859, 291642521720039733317, 280562085060805317151, 558773324927213233291, 528769627053872730655, 248899328511642797725, 531810403537728480685, 500977099628175886715, 356311473258883847735, 11601671982904419583, 136162066619380279677, 161563131506799106159, 93465843498689450749, 146566138796312143345, 187064359601628733361, 518538846333989334633, 371839833448345984457, 533910969088962099591, 316117075847858943751, 346264546376139499195, 1066625482224885183, 38360207226045062091, 333506373135664918737, 74393642678922240801, 162619104453277369171, 314128605909626073993, 37294868076785765637, 85245175827120394131][i]!
def words (i : Fin 69) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[273, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 69 rawWords i=rowTotals i)

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
private theorem row57 : rowAgrees 57=true := by decide +kernel
private theorem row58 : rowAgrees 58=true := by decide +kernel
private theorem row59 : rowAgrees 59=true := by decide +kernel
private theorem row60 : rowAgrees 60=true := by decide +kernel
private theorem row61 : rowAgrees 61=true := by decide +kernel
private theorem row62 : rowAgrees 62=true := by decide +kernel
private theorem row63 : rowAgrees 63=true := by decide +kernel
private theorem row64 : rowAgrees 64=true := by decide +kernel
private theorem row65 : rowAgrees 65=true := by decide +kernel
private theorem row66 : rowAgrees 66=true := by decide +kernel
private theorem row67 : rowAgrees 67=true := by decide +kernel
private theorem row68 : rowAgrees 68=true := by decide +kernel
private theorem rowChecked : allBelow 69 rowAgrees=true := by
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
  have h := allBelow_step h row57
  have h := allBelow_step h row58
  have h := allBelow_step h row59
  have h := allBelow_step h row60
  have h := allBelow_step h row61
  have h := allBelow_step h row62
  have h := allBelow_step h row63
  have h := allBelow_step h row64
  have h := allBelow_step h row65
  have h := allBelow_step h row66
  have h := allBelow_step h row67
  have h := allBelow_step h row68
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 69, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 69, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-3468:ℤ) := by
  change cubicInteger (fun i : Fin 69 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-3468:ℤ) ∧
    87*(69:ℤ)^3+375*69*(4*69-3)+1000*((wordMatrix words-1)^3).trace-
      1110*137*(69-1)=(21835398:ℤ) ∧ 0≤(21835398:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 69 ⊕ Fin 69 → Fin 138
  | .inl i => Fin.ofNat 138 (#[0, 3, 5, 6, 10, 12, 13, 20, 21, 23, 24, 26, 27, 29, 31, 33, 35, 40, 41, 42, 43, 45, 46, 47, 48, 51, 52, 53, 54, 55, 57, 58, 62, 66, 67, 70, 71, 75, 79, 80, 82, 83, 84, 85, 86, 89, 90, 91, 92, 94, 95, 96, 97, 102, 104, 106, 108, 110, 111, 113, 114, 116, 117, 124, 125, 127, 131, 132, 134][i.val]!)
  | .inr i => Fin.ofNat 138 (#[1, 2, 4, 7, 8, 9, 11, 14, 15, 16, 17, 18, 19, 22, 25, 28, 30, 32, 34, 36, 37, 38, 39, 44, 49, 50, 56, 59, 60, 61, 63, 64, 65, 68, 69, 72, 73, 74, 76, 77, 78, 81, 87, 88, 93, 98, 99, 100, 101, 103, 105, 107, 109, 112, 115, 118, 119, 120, 121, 122, 123, 126, 128, 129, 130, 133, 135, 136, 137][i.val]!)

def pointPosition (i : Fin 138) : Fin 69 ⊕ Fin 69 :=
  let j : ℕ := #[0, 69, 70, 1, 71, 2, 3, 72, 73, 74, 4, 75, 5, 6, 76, 77, 78, 79, 80, 81, 7, 8, 82, 9, 10, 83, 11, 12, 84, 13, 85, 14, 86, 15, 87, 16, 88, 89, 90, 91, 17, 18, 19, 20, 92, 21, 22, 23, 24, 93, 94, 25, 26, 27, 28, 29, 95, 30, 31, 96, 97, 98, 32, 99, 100, 101, 33, 34, 102, 103, 35, 36, 104, 105, 106, 37, 107, 108, 109, 38, 39, 110, 40, 41, 42, 43, 44, 111, 112, 45, 46, 47, 48, 113, 49, 50, 51, 52, 114, 115, 116, 117, 53, 118, 54, 119, 55, 120, 56, 121, 57, 58, 122, 59, 60, 123, 61, 62, 124, 125, 126, 127, 128, 129, 63, 64, 130, 65, 131, 132, 133, 66, 67, 134, 68, 135, 136, 137][i.val]!
  if j<69 then .inl (Fin.ofNat 69 j) else .inr (Fin.ofNat 69 (j-69))

def indexing : (Fin 69 ⊕ Fin 69) ≃ Fin 138 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 69,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*137)*(137-1)^68) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 68 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 68 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 68=(2*137)*(137-1)^68 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquares


namespace NonsplitNegative
def rawWords (i : ℕ) : ℕ := #[396804553719224520810, 352413967787958387145, 77624410669507642160, 264758446403720498435, 382024519856854633060, 326717401092295631317, 67553962794545597747, 76740709071840187426, 218251576647945910382, 574781941232999505940, 384028276964152512712, 205503477930986316120, 387948578441000437121, 194743708876394564384, 340681729353382629707, 238578335041626976927, 347953531343775212948, 331710566738382325310, 330281347770696656906, 70258229669580214397, 122078016701653397618, 515656659317497349778, 421523692733901015889, 551107116371498384849, 434909165275986017575, 113132600146230012623, 483226934135127988918, 560621513180994315567, 158661048797271876729, 28386091477549933487, 334553598249164296028, 134142634148161425114, 158778578765393476533, 161170861445383478469, 460983982059917998561, 35149347303333277639, 162455238025003880261, 211508541127653307973, 421700894278366423224, 271854463419591610642, 543149354760085038177, 139061173549194470981, 537941800058674284959, 504318049908734956310, 531894965053077066009, 464558911941304808059, 54122043927838654959, 49896007384908883675, 338430889224460635126, 359936849164360293976, 286100512115248348401, 369349602459667036642, 573597817022628345826, 192035605251464810194, 559391140416468540877, 380610775335412562835, 22223706349345070164, 7549836420548851755, 122284262654268535092, 87780054886470361802, 184562467022023378238, 544728641865777597172, 314342626657590822152, 353696621041087915377, 200686643696674675555, 176718939170130193226, 298380389927644862109, 58831715688916232968, 89989587742807774771][i]!
def words (i : Fin 69) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 69 rawWords i=rowTotals i)

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
private theorem row57 : rowAgrees 57=true := by decide +kernel
private theorem row58 : rowAgrees 58=true := by decide +kernel
private theorem row59 : rowAgrees 59=true := by decide +kernel
private theorem row60 : rowAgrees 60=true := by decide +kernel
private theorem row61 : rowAgrees 61=true := by decide +kernel
private theorem row62 : rowAgrees 62=true := by decide +kernel
private theorem row63 : rowAgrees 63=true := by decide +kernel
private theorem row64 : rowAgrees 64=true := by decide +kernel
private theorem row65 : rowAgrees 65=true := by decide +kernel
private theorem row66 : rowAgrees 66=true := by decide +kernel
private theorem row67 : rowAgrees 67=true := by decide +kernel
private theorem row68 : rowAgrees 68=true := by decide +kernel
private theorem rowChecked : allBelow 69 rowAgrees=true := by
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
  have h := allBelow_step h row57
  have h := allBelow_step h row58
  have h := allBelow_step h row59
  have h := allBelow_step h row60
  have h := allBelow_step h row61
  have h := allBelow_step h row62
  have h := allBelow_step h row63
  have h := allBelow_step h row64
  have h := allBelow_step h row65
  have h := allBelow_step h row66
  have h := allBelow_step h row67
  have h := allBelow_step h row68
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 69, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 69, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-3036:ℤ) := by
  change cubicInteger (fun i : Fin 69 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-3036:ℤ) ∧
    87*(69:ℤ)^3+375*69*(4*69-3)+1000*((wordMatrix words-1)^3).trace-
      1110*137*(69-1)=(22267398:ℤ) ∧ 0≤(22267398:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 69 ⊕ Fin 69 → Fin 138
  | .inl i => Fin.ofNat 138 (#[0, 3, 4, 6, 7, 10, 13, 15, 16, 17, 18, 19, 21, 22, 26, 27, 28, 30, 32, 33, 34, 38, 40, 42, 45, 46, 50, 51, 53, 57, 59, 60, 62, 66, 67, 70, 71, 75, 77, 78, 80, 84, 86, 87, 91, 92, 95, 97, 99, 103, 104, 105, 107, 109, 110, 111, 115, 116, 118, 119, 120, 121, 122, 124, 127, 130, 131, 133, 134][i.val]!)
  | .inr i => Fin.ofNat 138 (#[1, 2, 5, 8, 9, 11, 12, 14, 20, 23, 24, 25, 29, 31, 35, 36, 37, 39, 41, 43, 44, 47, 48, 49, 52, 54, 55, 56, 58, 61, 63, 64, 65, 68, 69, 72, 73, 74, 76, 79, 81, 82, 83, 85, 88, 89, 90, 93, 94, 96, 98, 100, 101, 102, 106, 108, 112, 113, 114, 117, 123, 125, 126, 128, 129, 132, 135, 136, 137][i.val]!)

def pointPosition (i : Fin 138) : Fin 69 ⊕ Fin 69 :=
  let j : ℕ := #[0, 69, 70, 1, 2, 71, 3, 4, 72, 73, 5, 74, 75, 6, 76, 7, 8, 9, 10, 11, 77, 12, 13, 78, 79, 80, 14, 15, 16, 81, 17, 82, 18, 19, 20, 83, 84, 85, 21, 86, 22, 87, 23, 88, 89, 24, 25, 90, 91, 92, 26, 27, 93, 28, 94, 95, 96, 29, 97, 30, 31, 98, 32, 99, 100, 101, 33, 34, 102, 103, 35, 36, 104, 105, 106, 37, 107, 38, 39, 108, 40, 109, 110, 111, 41, 112, 42, 43, 113, 114, 115, 44, 45, 116, 117, 46, 118, 47, 119, 48, 120, 121, 122, 49, 50, 51, 123, 52, 124, 53, 54, 55, 125, 126, 127, 56, 57, 128, 58, 59, 60, 61, 62, 129, 63, 130, 131, 64, 132, 133, 65, 66, 134, 67, 68, 135, 136, 137][i.val]!
  if j<69 then .inl (Fin.ofNat 69 j) else .inr (Fin.ofNat 69 (j-69))

def indexing : (Fin 69 ⊕ Fin 69) ≃ Fin 138 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 69,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*137)*(137-1)^68) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 68 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 68 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 68=(2*137)*(137-1)^68 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegative


namespace SplitSquaresOpposite
def rawWords (i : ℕ) : ℕ := #[170491536910784667428, 75381099220761129992, 41045521132708617233, 172395458660658733410, 11024743337949839876, 25489955524002006281, 193362727968541721864, 289916060739371953664, 215366976830746186857, 223514609101778720913, 225093431572194931175, 45493418360129536645, 51784160777221867271, 32234549147825996938, 36074517399690807804, 145941602052737274132, 272331488432796239970, 144297473387987513564, 293179611800082059424, 249972155510610288985, 218054420658299191963, 123698638372008052071, 132312292276895649750, 277374292261584276135, 187132950321313229391, 277379943719730754974, 78679867777570528894, 162768839704236681653, 159525989995866011257, 97690019636580476447, 15519499613033773375, 82846632777464871114, 81770372066449418224, 162387805124688547578, 110035712826801822513, 18337464717935982434, 95833790013392673762, 291243520162005020336, 286384090615251066154, 182653479805927275089, 200132675808508490929, 145821260860019866658, 140281042530402658575, 279386662463606616645, 264384813526936365327, 124449664255821398862, 265905201768864240342, 250488549814087943357, 178155736629441923867, 5800835991452209791, 68081033309690139838, 80781565753399553079, 46732921749344725374, 73283069398156071672, 93532179800814366680, 259269423166994667316, 185919916724172992228, 266955484544481049795, 158058537923929471875, 173132273188069749597, 533312741112442591, 19180103613022531045, 166753186567832459368, 37196821339461120400, 81309552226638684585, 157064302954813036996, 18647434038392882818, 42622587913560197065, 0][i]!
def words (i : Fin 69) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 273]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 69 rawWords i=rowTotals i)

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
private theorem row57 : rowAgrees 57=true := by decide +kernel
private theorem row58 : rowAgrees 58=true := by decide +kernel
private theorem row59 : rowAgrees 59=true := by decide +kernel
private theorem row60 : rowAgrees 60=true := by decide +kernel
private theorem row61 : rowAgrees 61=true := by decide +kernel
private theorem row62 : rowAgrees 62=true := by decide +kernel
private theorem row63 : rowAgrees 63=true := by decide +kernel
private theorem row64 : rowAgrees 64=true := by decide +kernel
private theorem row65 : rowAgrees 65=true := by decide +kernel
private theorem row66 : rowAgrees 66=true := by decide +kernel
private theorem row67 : rowAgrees 67=true := by decide +kernel
private theorem row68 : rowAgrees 68=true := by decide +kernel
private theorem rowChecked : allBelow 69 rowAgrees=true := by
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
  have h := allBelow_step h row57
  have h := allBelow_step h row58
  have h := allBelow_step h row59
  have h := allBelow_step h row60
  have h := allBelow_step h row61
  have h := allBelow_step h row62
  have h := allBelow_step h row63
  have h := allBelow_step h row64
  have h := allBelow_step h row65
  have h := allBelow_step h row66
  have h := allBelow_step h row67
  have h := allBelow_step h row68
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 69, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 69, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-3468:ℤ) := by
  change cubicInteger (fun i : Fin 69 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-3468:ℤ) ∧
    87*(69:ℤ)^3+375*69*(4*69-3)+1000*((wordMatrix words-1)^3).trace-
      1110*137*(69-1)=(21835398:ℤ) ∧ 0≤(21835398:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 69 ⊕ Fin 69 → Fin 138
  | .inl i => Fin.ofNat 138 (#[3, 5, 6, 10, 12, 13, 20, 21, 23, 24, 26, 27, 29, 31, 33, 35, 40, 41, 42, 43, 45, 46, 47, 48, 51, 52, 53, 54, 55, 57, 58, 62, 66, 67, 70, 71, 75, 79, 80, 82, 83, 84, 85, 86, 89, 90, 91, 92, 94, 95, 96, 97, 102, 104, 106, 108, 110, 111, 113, 114, 116, 117, 124, 125, 127, 131, 132, 134, 137][i.val]!)
  | .inr i => Fin.ofNat 138 (#[0, 1, 2, 4, 7, 8, 9, 11, 14, 15, 16, 17, 18, 19, 22, 25, 28, 30, 32, 34, 36, 37, 38, 39, 44, 49, 50, 56, 59, 60, 61, 63, 64, 65, 68, 69, 72, 73, 74, 76, 77, 78, 81, 87, 88, 93, 98, 99, 100, 101, 103, 105, 107, 109, 112, 115, 118, 119, 120, 121, 122, 123, 126, 128, 129, 130, 133, 135, 136][i.val]!)

def pointPosition (i : Fin 138) : Fin 69 ⊕ Fin 69 :=
  let j : ℕ := #[69, 70, 71, 0, 72, 1, 2, 73, 74, 75, 3, 76, 4, 5, 77, 78, 79, 80, 81, 82, 6, 7, 83, 8, 9, 84, 10, 11, 85, 12, 86, 13, 87, 14, 88, 15, 89, 90, 91, 92, 16, 17, 18, 19, 93, 20, 21, 22, 23, 94, 95, 24, 25, 26, 27, 28, 96, 29, 30, 97, 98, 99, 31, 100, 101, 102, 32, 33, 103, 104, 34, 35, 105, 106, 107, 36, 108, 109, 110, 37, 38, 111, 39, 40, 41, 42, 43, 112, 113, 44, 45, 46, 47, 114, 48, 49, 50, 51, 115, 116, 117, 118, 52, 119, 53, 120, 54, 121, 55, 122, 56, 57, 123, 58, 59, 124, 60, 61, 125, 126, 127, 128, 129, 130, 62, 63, 131, 64, 132, 133, 134, 65, 66, 135, 67, 136, 137, 68][i.val]!
  if j<69 then .inl (Fin.ofNat 69 j) else .inr (Fin.ofNat 69 (j-69))

def indexing : (Fin 69 ⊕ Fin 69) ≃ Fin 138 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 69,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*137)*(137-1)^68) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 68 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 68 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 68=(2*137)*(137-1)^68 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquaresOpposite


namespace SplitNonsquaresOpposite
def rawWords (i : ℕ) : ℕ := #[117669547806739652812, 196131902991732105624, 235691941588955678377, 1644787712310219783, 111664216331196467394, 188739096466596508036, 226931762428779038353, 23821493701165978743, 17671529683099371554, 67638970402620354628, 61481959243883028684, 90683277435612528912, 287390282170941727400, 283739470350667666979, 268584695853214707975, 168014210709160487711, 150993750245750885421, 165798443278851387505, 183572788902223716569, 63395553221539857193, 55280077437244163798, 145165814410204335592, 292667853534996994836, 294085447727064681831, 124752948135728835263, 286370164038425449790, 225439893574308807671, 30277075830280265439, 95183461684730420666, 153481283527459183548, 65056225419321126769, 95547345929390538346, 223355083995762097368, 96796793890984224707, 225860220800568438730, 31412450738107014531, 99709925833320954698, 164822638585683818012, 71309655723238881441, 108060394382317023562, 289932009050144981592, 276425620494681477571, 143721354697204778527, 292081430212231638070, 265966389512846715135, 47090510360719563711, 27324488317813299134, 123805656853103595508, 171499373620296499052, 178725545733265202425, 163769129301289825265, 207751340436336865089, 286888947118976097673, 258891899089267699479, 226456197979364350063, 24527771088605586079, 9806722310258681202, 58819497950715955884, 39258347953456895324, 78484642918163008240, 274576249122016630056, 158384512811094977315, 38680677160010526149, 77324184264426019590, 258442246443770885760, 172233622632082732595, 29431199038303139925, 58834773903369826406, 0][i]!
def words (i : Fin 69) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 257, 137]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 69 rawWords i=rowTotals i)

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
private theorem row57 : rowAgrees 57=true := by decide +kernel
private theorem row58 : rowAgrees 58=true := by decide +kernel
private theorem row59 : rowAgrees 59=true := by decide +kernel
private theorem row60 : rowAgrees 60=true := by decide +kernel
private theorem row61 : rowAgrees 61=true := by decide +kernel
private theorem row62 : rowAgrees 62=true := by decide +kernel
private theorem row63 : rowAgrees 63=true := by decide +kernel
private theorem row64 : rowAgrees 64=true := by decide +kernel
private theorem row65 : rowAgrees 65=true := by decide +kernel
private theorem row66 : rowAgrees 66=true := by decide +kernel
private theorem row67 : rowAgrees 67=true := by decide +kernel
private theorem row68 : rowAgrees 68=true := by decide +kernel
private theorem rowChecked : allBelow 69 rowAgrees=true := by
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
  have h := allBelow_step h row57
  have h := allBelow_step h row58
  have h := allBelow_step h row59
  have h := allBelow_step h row60
  have h := allBelow_step h row61
  have h := allBelow_step h row62
  have h := allBelow_step h row63
  have h := allBelow_step h row64
  have h := allBelow_step h row65
  have h := allBelow_step h row66
  have h := allBelow_step h row67
  have h := allBelow_step h row68
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 69, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 69, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(3468:ℤ) := by
  change cubicInteger (fun i : Fin 69 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(3468:ℤ) ∧
    87*(69:ℤ)^3+375*69*(4*69-3)+1000*((wordMatrix words-1)^3).trace-
      1110*137*(69-1)=(28771398:ℤ) ∧ 0≤(28771398:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 69 ⊕ Fin 69 → Fin 138
  | .inl i => Fin.ofNat 138 (#[1, 2, 4, 7, 8, 9, 11, 14, 15, 16, 17, 18, 19, 22, 25, 28, 30, 32, 34, 36, 37, 38, 39, 44, 49, 50, 56, 59, 60, 61, 63, 64, 65, 68, 69, 72, 73, 74, 76, 77, 78, 81, 87, 88, 93, 98, 99, 100, 101, 103, 105, 107, 109, 112, 115, 118, 119, 120, 121, 122, 123, 126, 128, 129, 130, 133, 135, 136, 137][i.val]!)
  | .inr i => Fin.ofNat 138 (#[0, 3, 5, 6, 10, 12, 13, 20, 21, 23, 24, 26, 27, 29, 31, 33, 35, 40, 41, 42, 43, 45, 46, 47, 48, 51, 52, 53, 54, 55, 57, 58, 62, 66, 67, 70, 71, 75, 79, 80, 82, 83, 84, 85, 86, 89, 90, 91, 92, 94, 95, 96, 97, 102, 104, 106, 108, 110, 111, 113, 114, 116, 117, 124, 125, 127, 131, 132, 134][i.val]!)

def pointPosition (i : Fin 138) : Fin 69 ⊕ Fin 69 :=
  let j : ℕ := #[69, 0, 1, 70, 2, 71, 72, 3, 4, 5, 73, 6, 74, 75, 7, 8, 9, 10, 11, 12, 76, 77, 13, 78, 79, 14, 80, 81, 15, 82, 16, 83, 17, 84, 18, 85, 19, 20, 21, 22, 86, 87, 88, 89, 23, 90, 91, 92, 93, 24, 25, 94, 95, 96, 97, 98, 26, 99, 100, 27, 28, 29, 101, 30, 31, 32, 102, 103, 33, 34, 104, 105, 35, 36, 37, 106, 38, 39, 40, 107, 108, 41, 109, 110, 111, 112, 113, 42, 43, 114, 115, 116, 117, 44, 118, 119, 120, 121, 45, 46, 47, 48, 122, 49, 123, 50, 124, 51, 125, 52, 126, 127, 53, 128, 129, 54, 130, 131, 55, 56, 57, 58, 59, 60, 132, 133, 61, 134, 62, 63, 64, 135, 136, 65, 137, 66, 67, 68][i.val]!
  if j<69 then .inl (Fin.ofNat 69 j) else .inr (Fin.ofNat 69 (j-69))

def indexing : (Fin 69 ⊕ Fin 69) ≃ Fin 138 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 69,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*137)*(137-1)^68) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 68 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 68 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 68=(2*137)*(137-1)^68 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquaresOpposite


namespace NonsplitNegativeOpposite
def rawWords (i : ℕ) : ℕ := #[127760028798428155040, 170904739539842595532, 203075039274639341610, 113359495585426534822, 156391350577837166784, 233681584597343757965, 183672281237237451794, 11587666523798193467, 162375105587890096776, 169472117985112543522, 125002267282241589473, 240711215171598639431, 82400681695218386462, 92122466252666800174, 63154249440617044730, 53063090611264300629, 71013179534562831530, 252801626244518023240, 266435125952986018249, 146862239180308685771, 255117211924412376883, 208552113690801162183, 47592903615680400399, 138385310122889681819, 259717398451540081269, 168469297103415552763, 81568725598795757019, 227609161846014663359, 30218216178429557349, 195416636120510054808, 21673402052542956413, 79065432982982325874, 260258298972463337448, 82330640351011228579, 228075483293033207522, 27604402715828895111, 90426524309579114786, 219927940356331418440, 29411377013515419285, 191810606607719705688, 292099390745663166115, 253273744584508702050, 257480554430008784969, 201023889687438893703, 251165063214695047198, 276931131415887471252, 262733959365910054701, 236224590085884404411, 244151451094636005118, 170123691829491538151, 20793286800174785243, 98232885560780265916, 196448758653276282996, 109924532417784243052, 133818708710382561266, 138793652486184181474, 261166061869882217227, 155687435924985624118, 79025187946329964361, 19961029342319962929, 254375506375392309328, 83242088799740556025, 204528881126753563987, 3508479413926471137, 117088866158232947270, 96976126916948771853, 59225140055244684329, 5986409414565170038, 0][i]!
def words (i : Fin 69) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 69 rawWords i=rowTotals i)

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
private theorem row57 : rowAgrees 57=true := by decide +kernel
private theorem row58 : rowAgrees 58=true := by decide +kernel
private theorem row59 : rowAgrees 59=true := by decide +kernel
private theorem row60 : rowAgrees 60=true := by decide +kernel
private theorem row61 : rowAgrees 61=true := by decide +kernel
private theorem row62 : rowAgrees 62=true := by decide +kernel
private theorem row63 : rowAgrees 63=true := by decide +kernel
private theorem row64 : rowAgrees 64=true := by decide +kernel
private theorem row65 : rowAgrees 65=true := by decide +kernel
private theorem row66 : rowAgrees 66=true := by decide +kernel
private theorem row67 : rowAgrees 67=true := by decide +kernel
private theorem row68 : rowAgrees 68=true := by decide +kernel
private theorem rowChecked : allBelow 69 rowAgrees=true := by
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
  have h := allBelow_step h row57
  have h := allBelow_step h row58
  have h := allBelow_step h row59
  have h := allBelow_step h row60
  have h := allBelow_step h row61
  have h := allBelow_step h row62
  have h := allBelow_step h row63
  have h := allBelow_step h row64
  have h := allBelow_step h row65
  have h := allBelow_step h row66
  have h := allBelow_step h row67
  have h := allBelow_step h row68
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 69, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 69, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(3036:ℤ) := by
  change cubicInteger (fun i : Fin 69 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(3036:ℤ) ∧
    87*(69:ℤ)^3+375*69*(4*69-3)+1000*((wordMatrix words-1)^3).trace-
      1110*137*(69-1)=(28339398:ℤ) ∧ 0≤(28339398:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 69 ⊕ Fin 69 → Fin 138
  | .inl i => Fin.ofNat 138 (#[1, 2, 5, 8, 9, 11, 12, 14, 20, 23, 24, 25, 29, 31, 35, 36, 37, 39, 41, 43, 44, 47, 48, 49, 52, 54, 55, 56, 58, 61, 63, 64, 65, 68, 69, 72, 73, 74, 76, 79, 81, 82, 83, 85, 88, 89, 90, 93, 94, 96, 98, 100, 101, 102, 106, 108, 112, 113, 114, 117, 123, 125, 126, 128, 129, 132, 135, 136, 137][i.val]!)
  | .inr i => Fin.ofNat 138 (#[0, 3, 4, 6, 7, 10, 13, 15, 16, 17, 18, 19, 21, 22, 26, 27, 28, 30, 32, 33, 34, 38, 40, 42, 45, 46, 50, 51, 53, 57, 59, 60, 62, 66, 67, 70, 71, 75, 77, 78, 80, 84, 86, 87, 91, 92, 95, 97, 99, 103, 104, 105, 107, 109, 110, 111, 115, 116, 118, 119, 120, 121, 122, 124, 127, 130, 131, 133, 134][i.val]!)

def pointPosition (i : Fin 138) : Fin 69 ⊕ Fin 69 :=
  let j : ℕ := #[69, 0, 1, 70, 71, 2, 72, 73, 3, 4, 74, 5, 6, 75, 7, 76, 77, 78, 79, 80, 8, 81, 82, 9, 10, 11, 83, 84, 85, 12, 86, 13, 87, 88, 89, 14, 15, 16, 90, 17, 91, 18, 92, 19, 20, 93, 94, 21, 22, 23, 95, 96, 24, 97, 25, 26, 27, 98, 28, 99, 100, 29, 101, 30, 31, 32, 102, 103, 33, 34, 104, 105, 35, 36, 37, 106, 38, 107, 108, 39, 109, 40, 41, 42, 110, 43, 111, 112, 44, 45, 46, 113, 114, 47, 48, 115, 49, 116, 50, 117, 51, 52, 53, 118, 119, 120, 54, 121, 55, 122, 123, 124, 56, 57, 58, 125, 126, 59, 127, 128, 129, 130, 131, 60, 132, 61, 62, 133, 63, 64, 134, 135, 65, 136, 137, 66, 67, 68][i.val]!
  if j<69 then .inl (Fin.ofNat 69 j) else .inr (Fin.ofNat 69 (j-69))

def indexing : (Fin 69 ⊕ Fin 69) ≃ Fin 138 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 69,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*137)*(137-1)^68) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 68 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 68 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 68=(2*137)*(137-1)^68 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegativeOpposite

end PaleyBits137
