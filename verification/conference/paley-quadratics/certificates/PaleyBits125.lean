import Quantum.Hadamard.ConferenceBitCompletion
open Hadamard.BitTrace Hadamard.DeterminantRatio Matrix
set_option maxHeartbeats 12000000
set_option maxRecDepth 60000
namespace PaleyBits125

def rawFull (i : ℕ) : ℕ := #[38760681725711061873958275874179863340, 36315256284919915722709164394373850744, 31424443471234151521940351515424508145, 20313630374520773368734670578203039171, 40627220222598518430872241809466239878, 6818252881459961981051796542508918151, 13635208956318377147785203932673134350, 27270378575891542664851738916065713724, 12006718796098681645572140249490045049, 24012180043187893408260796123731816659, 5507614148781899484004831181067301098, 10973730486315472056674058262005014996, 21946202196785343077238461819045267337, 1397348830306314182815821894555995954, 2754456092309592113360143782207429221, 6102455356395213698465792414390295892, 10876980752843966234192253625673988745, 21713719975797306387987003089234751794, 2179833745770084456507602512493274693, 3071976603010444768550899529826913450, 25137375267671037652961856818507917977, 7780991817056489245117963913545601331, 14274293974781550992627241037267347015, 27219361181814741682906168560357001390, 13232653227845746671213158897463956828, 20124637687736472512498010504830292114, 40249234811853029913609844218045735173, 39250902676675167368208618344379204106, 35966548786602097216366199438721713204, 30685492596652952831874865457713973321, 5958951551350454017765112805265117789, 11916644364031060399396263005681623227, 22505318241710108030979983978600612183, 2476598166111990194050530979227928207, 3623969604052188006160052823487744318, 20545234491481084488628138935769516965, 41050228642694480549193169242169808746, 39605441019293159603496439832694500084, 36715827703358466207579748497372533225, 30896400105219576193082107571837413330, 19418074624189248460934619631381476516, 37548458359812467223884666019019681096, 33850568023195832531834276086385303184, 26453529840568307927948415093658238241, 10373022554689155594885526054574029378, 25884226847655165170596065149964948612, 10562384558364815933944384122003499272, 19835782649634916478543581588138742288, 38342338531558950534584477546711589921, 34189621538268282709125229020868200514, 38434582139176373812133022948303977939, 34374109981538513649948431071903513479, 26212963395129534223055078351550576430, 9930911790577099396125398832226823804, 19861784283946906127805171279410060537, 38918369583371382209940731428283595375, 36589134190155216087217848762399420670, 30644230024626028489222371195793368541, 20042112580898157371285399595923656603, 40082967651164120627163603646393589559, 11864273200144829898329788780926946788, 22399319670956051996889083948787703752, 2303583778647731987493426270389975984, 3318181091438615391387943376975950689, 6596121842648190236598478074333619938, 39374374216045077486716753930552458383, 36213493093415876527630561017887717662, 31179379981007223627838242092970636829, 21111193054596463727399142616226229307, 40934695221863629977121207485707639895, 26456412572148574926119809117454832110, 10378786828189349578863325427162620892, 19428346888630303400736193586601575353, 37528724558520508670321211965522675571, 33851380019670933983199630762037709543, 10978445213638565608268657077338940339, 21956851128871756429584956973217858407, 1378446919030586566105008159908923118, 2755635099428764418704075017975990780, 5509972125880835169750402974643852249, 11027881183145405092966598080483063420, 22054504817319988150310615130186476793, 1574971317295444914897154163831004627, 3109702295522418072715633066522001287, 6177905552958074708641957793042168622, 12609828404413487949758168835159936925, 25179415241760670759593744686411259707, 7863776147131711949705906410609162871, 14439861444073498819781956136751067375, 27551792966538067590529740119229818334, 20696832211019844948338975316490449832, 40105973573085361347378669873691617136, 38964340903170515316846745253970398945, 36722613897432035160649523001747709410, 30951470303378308752240439962853227460, 24269180099370210428283669326921102621, 7332292329369343207214049083411721755, 13335356701367425095012829400813657143, 26670672839116105044971607675763932239, 12135238472155778725567882347352127646, 9746971690915589537517116225166255602, 19452444343744417639325824270423575493, 37615901031971608941802294134873036714, 33985453329139144753047265795352111988, 25477149168028052412080593472051106537, 14155995165165033554079549477198544456, 26984060408721137093748634819169450160, 12720555138059638483429375044966610241, 24152122581025482709601034706388086402, 7098137995512488403074055791079742756, 27638892972361033321378046924354472200, 12784028453236306181656144417496438288, 24240087687696208678639722144494168097, 7232608429559608200143998412303224898, 14463920051355890729656718330623140996, 33738678095616095709088795717709406473, 26271248985155795508444367036921070098, 10047482969467844254254351649896465445, 18766995490922341400716136146859067466, 37492493133419432488084209261153128596, 16255329052444591371277728103442686255, 32509360031912452476592335751331988062, 23772372558294118541237343008717833405, 5049730077329736708223983521351403867, 8771529005052634536162798776563667607, 0][i]!
def fullRows (i : Fin 126) : ℕ := rawFull i.val

private theorem fullSymmetric : (wordMatrix fullRows).IsSymm := by
  have h : ∀ i j : Fin 126, sign (fullRows i) j.val=sign (fullRows j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem fullDiagonal : ∀ i : Fin 126, sign (fullRows i) i.val=1 := by decide +kernel
private theorem lower0 : (lowerRow 126 rawFull) 0=true := by decide +kernel
private theorem lower1 : (lowerRow 126 rawFull) 1=true := by decide +kernel
private theorem lower2 : (lowerRow 126 rawFull) 2=true := by decide +kernel
private theorem lower3 : (lowerRow 126 rawFull) 3=true := by decide +kernel
private theorem lower4 : (lowerRow 126 rawFull) 4=true := by decide +kernel
private theorem lower5 : (lowerRow 126 rawFull) 5=true := by decide +kernel
private theorem lower6 : (lowerRow 126 rawFull) 6=true := by decide +kernel
private theorem lower7 : (lowerRow 126 rawFull) 7=true := by decide +kernel
private theorem lower8 : (lowerRow 126 rawFull) 8=true := by decide +kernel
private theorem lower9 : (lowerRow 126 rawFull) 9=true := by decide +kernel
private theorem lower10 : (lowerRow 126 rawFull) 10=true := by decide +kernel
private theorem lower11 : (lowerRow 126 rawFull) 11=true := by decide +kernel
private theorem lower12 : (lowerRow 126 rawFull) 12=true := by decide +kernel
private theorem lower13 : (lowerRow 126 rawFull) 13=true := by decide +kernel
private theorem lower14 : (lowerRow 126 rawFull) 14=true := by decide +kernel
private theorem lower15 : (lowerRow 126 rawFull) 15=true := by decide +kernel
private theorem lower16 : (lowerRow 126 rawFull) 16=true := by decide +kernel
private theorem lower17 : (lowerRow 126 rawFull) 17=true := by decide +kernel
private theorem lower18 : (lowerRow 126 rawFull) 18=true := by decide +kernel
private theorem lower19 : (lowerRow 126 rawFull) 19=true := by decide +kernel
private theorem lower20 : (lowerRow 126 rawFull) 20=true := by decide +kernel
private theorem lower21 : (lowerRow 126 rawFull) 21=true := by decide +kernel
private theorem lower22 : (lowerRow 126 rawFull) 22=true := by decide +kernel
private theorem lower23 : (lowerRow 126 rawFull) 23=true := by decide +kernel
private theorem lower24 : (lowerRow 126 rawFull) 24=true := by decide +kernel
private theorem lower25 : (lowerRow 126 rawFull) 25=true := by decide +kernel
private theorem lower26 : (lowerRow 126 rawFull) 26=true := by decide +kernel
private theorem lower27 : (lowerRow 126 rawFull) 27=true := by decide +kernel
private theorem lower28 : (lowerRow 126 rawFull) 28=true := by decide +kernel
private theorem lower29 : (lowerRow 126 rawFull) 29=true := by decide +kernel
private theorem lower30 : (lowerRow 126 rawFull) 30=true := by decide +kernel
private theorem lower31 : (lowerRow 126 rawFull) 31=true := by decide +kernel
private theorem lower32 : (lowerRow 126 rawFull) 32=true := by decide +kernel
private theorem lower33 : (lowerRow 126 rawFull) 33=true := by decide +kernel
private theorem lower34 : (lowerRow 126 rawFull) 34=true := by decide +kernel
private theorem lower35 : (lowerRow 126 rawFull) 35=true := by decide +kernel
private theorem lower36 : (lowerRow 126 rawFull) 36=true := by decide +kernel
private theorem lower37 : (lowerRow 126 rawFull) 37=true := by decide +kernel
private theorem lower38 : (lowerRow 126 rawFull) 38=true := by decide +kernel
private theorem lower39 : (lowerRow 126 rawFull) 39=true := by decide +kernel
private theorem lower40 : (lowerRow 126 rawFull) 40=true := by decide +kernel
private theorem lower41 : (lowerRow 126 rawFull) 41=true := by decide +kernel
private theorem lower42 : (lowerRow 126 rawFull) 42=true := by decide +kernel
private theorem lower43 : (lowerRow 126 rawFull) 43=true := by decide +kernel
private theorem lower44 : (lowerRow 126 rawFull) 44=true := by decide +kernel
private theorem lower45 : (lowerRow 126 rawFull) 45=true := by decide +kernel
private theorem lower46 : (lowerRow 126 rawFull) 46=true := by decide +kernel
private theorem lower47 : (lowerRow 126 rawFull) 47=true := by decide +kernel
private theorem lower48 : (lowerRow 126 rawFull) 48=true := by decide +kernel
private theorem lower49 : (lowerRow 126 rawFull) 49=true := by decide +kernel
private theorem lower50 : (lowerRow 126 rawFull) 50=true := by decide +kernel
private theorem lower51 : (lowerRow 126 rawFull) 51=true := by decide +kernel
private theorem lower52 : (lowerRow 126 rawFull) 52=true := by decide +kernel
private theorem lower53 : (lowerRow 126 rawFull) 53=true := by decide +kernel
private theorem lower54 : (lowerRow 126 rawFull) 54=true := by decide +kernel
private theorem lower55 : (lowerRow 126 rawFull) 55=true := by decide +kernel
private theorem lower56 : (lowerRow 126 rawFull) 56=true := by decide +kernel
private theorem lower57 : (lowerRow 126 rawFull) 57=true := by decide +kernel
private theorem lower58 : (lowerRow 126 rawFull) 58=true := by decide +kernel
private theorem lower59 : (lowerRow 126 rawFull) 59=true := by decide +kernel
private theorem lower60 : (lowerRow 126 rawFull) 60=true := by decide +kernel
private theorem lower61 : (lowerRow 126 rawFull) 61=true := by decide +kernel
private theorem lower62 : (lowerRow 126 rawFull) 62=true := by decide +kernel
private theorem lower63 : (lowerRow 126 rawFull) 63=true := by decide +kernel
private theorem lower64 : (lowerRow 126 rawFull) 64=true := by decide +kernel
private theorem lower65 : (lowerRow 126 rawFull) 65=true := by decide +kernel
private theorem lower66 : (lowerRow 126 rawFull) 66=true := by decide +kernel
private theorem lower67 : (lowerRow 126 rawFull) 67=true := by decide +kernel
private theorem lower68 : (lowerRow 126 rawFull) 68=true := by decide +kernel
private theorem lower69 : (lowerRow 126 rawFull) 69=true := by decide +kernel
private theorem lower70 : (lowerRow 126 rawFull) 70=true := by decide +kernel
private theorem lower71 : (lowerRow 126 rawFull) 71=true := by decide +kernel
private theorem lower72 : (lowerRow 126 rawFull) 72=true := by decide +kernel
private theorem lower73 : (lowerRow 126 rawFull) 73=true := by decide +kernel
private theorem lower74 : (lowerRow 126 rawFull) 74=true := by decide +kernel
private theorem lower75 : (lowerRow 126 rawFull) 75=true := by decide +kernel
private theorem lower76 : (lowerRow 126 rawFull) 76=true := by decide +kernel
private theorem lower77 : (lowerRow 126 rawFull) 77=true := by decide +kernel
private theorem lower78 : (lowerRow 126 rawFull) 78=true := by decide +kernel
private theorem lower79 : (lowerRow 126 rawFull) 79=true := by decide +kernel
private theorem lower80 : (lowerRow 126 rawFull) 80=true := by decide +kernel
private theorem lower81 : (lowerRow 126 rawFull) 81=true := by decide +kernel
private theorem lower82 : (lowerRow 126 rawFull) 82=true := by decide +kernel
private theorem lower83 : (lowerRow 126 rawFull) 83=true := by decide +kernel
private theorem lower84 : (lowerRow 126 rawFull) 84=true := by decide +kernel
private theorem lower85 : (lowerRow 126 rawFull) 85=true := by decide +kernel
private theorem lower86 : (lowerRow 126 rawFull) 86=true := by decide +kernel
private theorem lower87 : (lowerRow 126 rawFull) 87=true := by decide +kernel
private theorem lower88 : (lowerRow 126 rawFull) 88=true := by decide +kernel
private theorem lower89 : (lowerRow 126 rawFull) 89=true := by decide +kernel
private theorem lower90 : (lowerRow 126 rawFull) 90=true := by decide +kernel
private theorem lower91 : (lowerRow 126 rawFull) 91=true := by decide +kernel
private theorem lower92 : (lowerRow 126 rawFull) 92=true := by decide +kernel
private theorem lower93 : (lowerRow 126 rawFull) 93=true := by decide +kernel
private theorem lower94 : (lowerRow 126 rawFull) 94=true := by decide +kernel
private theorem lower95 : (lowerRow 126 rawFull) 95=true := by decide +kernel
private theorem lower96 : (lowerRow 126 rawFull) 96=true := by decide +kernel
private theorem lower97 : (lowerRow 126 rawFull) 97=true := by decide +kernel
private theorem lower98 : (lowerRow 126 rawFull) 98=true := by decide +kernel
private theorem lower99 : (lowerRow 126 rawFull) 99=true := by decide +kernel
private theorem lower100 : (lowerRow 126 rawFull) 100=true := by decide +kernel
private theorem lower101 : (lowerRow 126 rawFull) 101=true := by decide +kernel
private theorem lower102 : (lowerRow 126 rawFull) 102=true := by decide +kernel
private theorem lower103 : (lowerRow 126 rawFull) 103=true := by decide +kernel
private theorem lower104 : (lowerRow 126 rawFull) 104=true := by decide +kernel
private theorem lower105 : (lowerRow 126 rawFull) 105=true := by decide +kernel
private theorem lower106 : (lowerRow 126 rawFull) 106=true := by decide +kernel
private theorem lower107 : (lowerRow 126 rawFull) 107=true := by decide +kernel
private theorem lower108 : (lowerRow 126 rawFull) 108=true := by decide +kernel
private theorem lower109 : (lowerRow 126 rawFull) 109=true := by decide +kernel
private theorem lower110 : (lowerRow 126 rawFull) 110=true := by decide +kernel
private theorem lower111 : (lowerRow 126 rawFull) 111=true := by decide +kernel
private theorem lower112 : (lowerRow 126 rawFull) 112=true := by decide +kernel
private theorem lower113 : (lowerRow 126 rawFull) 113=true := by decide +kernel
private theorem lower114 : (lowerRow 126 rawFull) 114=true := by decide +kernel
private theorem lower115 : (lowerRow 126 rawFull) 115=true := by decide +kernel
private theorem lower116 : (lowerRow 126 rawFull) 116=true := by decide +kernel
private theorem lower117 : (lowerRow 126 rawFull) 117=true := by decide +kernel
private theorem lower118 : (lowerRow 126 rawFull) 118=true := by decide +kernel
private theorem lower119 : (lowerRow 126 rawFull) 119=true := by decide +kernel
private theorem lower120 : (lowerRow 126 rawFull) 120=true := by decide +kernel
private theorem lower121 : (lowerRow 126 rawFull) 121=true := by decide +kernel
private theorem lower122 : (lowerRow 126 rawFull) 122=true := by decide +kernel
private theorem lower123 : (lowerRow 126 rawFull) 123=true := by decide +kernel
private theorem lower124 : (lowerRow 126 rawFull) 124=true := by decide +kernel
private theorem lower125 : (lowerRow 126 rawFull) 125=true := by decide +kernel
private theorem lowerChecked : allBelow 126 (lowerRow 126 rawFull)=true := by
  have h : allBelow 0 (lowerRow 126 rawFull)=true := rfl
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
  exact h

private theorem fullPairs : ∀ i j : Fin 126, i≠j →
    correlation 126 (fullRows i) (fullRows j)=2*sign (fullRows i) j.val :=
  correlations_of_lower rawFull fullSymmetric lowerChecked


namespace SplitSquares
def rawWords (i : ℕ) : ℕ := #[0, 6495218003151122092, 7572122907553149906, 5912511584838488418, 2608689158022769764, 390464366144296346, 1224102288233401756, 305645740317475430, 3353590583701584492, 2143914623812789638, 6291647853489314418, 1912335545688827218, 4400258037835982124, 4877938259993156374, 2805421315775411714, 5178640295916742948, 7632343284780380230, 8211464730342606890, 3704311097138459868, 5681419334732701886, 7748407665973675184, 1091734936845003752, 2217942657753944180, 8472373099837948362, 6358771375497525040, 8824362103833634240, 8389464350875807492, 2980174392852794954, 7556489891971439778, 6430598598539368940, 7466357977688092318, 3884139734356421240, 4174258633057869432, 3124206407038229972, 4519037197204132794, 5690454479419907014, 8549980302965232410, 8630382111598216860, 66618534117889850, 5438888407182590812, 1428842102715316396, 2714039076997528258, 3063119998373922494, 7648695801555123600, 4918179857914846124, 6995249465389657722, 5765335018681302488, 18956530891324118, 6660410654988511422, 1520464699914830130, 2932170419034308812, 7395758086072158696, 1577985615281698004, 4836033521974206706, 2166673336901289568, 3610769238200675136, 3328762261471213092, 1866757156355501322, 8168142401377458096, 8306058897072397062, 5679955253748178506, 976206036725092628, 2029285840783123470][i]!
def words (i : Fin 63) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[125, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 63 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 63 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 63, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 63, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(3534:ℤ) := by
  change cubicInteger (fun i : Fin 63 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(3534:ℤ) ∧
    87*(63:ℤ)^3+375*63*(4*63-3)+1000*((wordMatrix words-1)^3).trace-
      1110*125*(63-1)=(22568214:ℤ) ∧ 0≤(22568214:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 63 ⊕ Fin 63 → Fin 126
  | .inl i => Fin.ofNat 126 (#[0, 1, 4, 6, 7, 10, 11, 13, 15, 17, 19, 23, 24, 25, 27, 28, 34, 36, 37, 39, 40, 41, 42, 44, 45, 46, 47, 49, 52, 53, 56, 60, 61, 62, 64, 66, 70, 71, 77, 78, 80, 84, 89, 90, 91, 93, 94, 99, 100, 102, 103, 105, 106, 108, 109, 110, 111, 113, 114, 116, 118, 119, 121][i.val]!)
  | .inr i => Fin.ofNat 126 (#[2, 3, 5, 8, 9, 12, 14, 16, 18, 20, 21, 22, 26, 29, 30, 31, 32, 33, 35, 38, 43, 48, 50, 51, 54, 55, 57, 58, 59, 63, 65, 67, 68, 69, 72, 73, 74, 75, 76, 79, 81, 82, 83, 85, 86, 87, 88, 92, 95, 96, 97, 98, 101, 104, 107, 112, 115, 117, 120, 122, 123, 124, 125][i.val]!)

def pointPosition (i : Fin 126) : Fin 63 ⊕ Fin 63 :=
  let j : ℕ := #[0, 1, 63, 64, 2, 65, 3, 4, 66, 67, 5, 6, 68, 7, 69, 8, 70, 9, 71, 10, 72, 73, 74, 11, 12, 13, 75, 14, 15, 76, 77, 78, 79, 80, 16, 81, 17, 18, 82, 19, 20, 21, 22, 83, 23, 24, 25, 26, 84, 27, 85, 86, 28, 29, 87, 88, 30, 89, 90, 91, 31, 32, 33, 92, 34, 93, 35, 94, 95, 96, 36, 37, 97, 98, 99, 100, 101, 38, 39, 102, 40, 103, 104, 105, 41, 106, 107, 108, 109, 42, 43, 44, 110, 45, 46, 111, 112, 113, 114, 47, 48, 115, 49, 50, 116, 51, 52, 117, 53, 54, 55, 56, 118, 57, 58, 119, 59, 120, 60, 61, 121, 62, 122, 123, 124, 125][i.val]!
  if j<63 then .inl (Fin.ofNat 63 j) else .inr (Fin.ofNat 63 (j-63))

def indexing : (Fin 63 ⊕ Fin 63) ≃ Fin 126 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 63,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*125)*(125-1)^62) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 62 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 62 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 62=(2*125)*(125-1)^62 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquares


namespace SplitNonsquares
def rawWords (i : ℕ) : ℕ := #[9223372036854775806, 6645862406223213193, 4203744164675175761, 2110467465488697491, 3072085895784573005, 4640249103392741313, 4673308172968036789, 67438061886769771, 2745482398408928869, 938914619156674979, 5154174779102900517, 1877876863746008025, 2836438031379645987, 8192622647462973203, 6475419014927890693, 1673882289548702823, 2735575465110284813, 5102155898265587859, 792348496380412967, 4364336943009607867, 7711788561534346461, 5512263784801567833, 8248891271081538313, 8570525506817129553, 7647163145960823539, 3875706340936588749, 8741753050236015471, 6621375932114756247, 4153643363260311477, 8442410962094713211, 555141819764542969, 8907707140791769415, 6672663720116242407, 4447061197050384013, 8326668872391409347, 3707611926998571709, 8586160821354664761, 7922752914406319403, 2372913465659454009, 4656039434086918075, 1551398520115420021, 4740100808865213581, 1086054894273518801, 46693306740931955, 3317119418293519031, 4995212245075952509, 2163166413696976235, 2534182439875873743, 8651073632559718313, 4627911956184411863, 1761270081883954853, 2505007263998466507, 5793358290820657479, 3771351797581848755, 5673447460901966061, 2974640644310394065, 5080244268666320393, 7874777168567770389, 1972705500347471627, 3946653160398670367, 5491366925248817167, 768304085368123669, 1392494873490383971][i]!
def words (i : Fin 63) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[249, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 63 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 63 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 63, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 63, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-3534:ℤ) := by
  change cubicInteger (fun i : Fin 63 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-3534:ℤ) ∧
    87*(63:ℤ)^3+375*63*(4*63-3)+1000*((wordMatrix words-1)^3).trace-
      1110*125*(63-1)=(15500214:ℤ) ∧ 0≤(15500214:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 63 ⊕ Fin 63 → Fin 126
  | .inl i => Fin.ofNat 126 (#[0, 2, 3, 5, 8, 9, 12, 14, 16, 18, 20, 21, 22, 26, 29, 30, 31, 32, 33, 35, 38, 43, 48, 50, 51, 54, 55, 57, 58, 59, 63, 65, 67, 68, 69, 72, 73, 74, 75, 76, 79, 81, 82, 83, 85, 86, 87, 88, 92, 95, 96, 97, 98, 101, 104, 107, 112, 115, 117, 120, 122, 123, 124][i.val]!)
  | .inr i => Fin.ofNat 126 (#[1, 4, 6, 7, 10, 11, 13, 15, 17, 19, 23, 24, 25, 27, 28, 34, 36, 37, 39, 40, 41, 42, 44, 45, 46, 47, 49, 52, 53, 56, 60, 61, 62, 64, 66, 70, 71, 77, 78, 80, 84, 89, 90, 91, 93, 94, 99, 100, 102, 103, 105, 106, 108, 109, 110, 111, 113, 114, 116, 118, 119, 121, 125][i.val]!)

def pointPosition (i : Fin 126) : Fin 63 ⊕ Fin 63 :=
  let j : ℕ := #[0, 63, 1, 2, 64, 3, 65, 66, 4, 5, 67, 68, 6, 69, 7, 70, 8, 71, 9, 72, 10, 11, 12, 73, 74, 75, 13, 76, 77, 14, 15, 16, 17, 18, 78, 19, 79, 80, 20, 81, 82, 83, 84, 21, 85, 86, 87, 88, 22, 89, 23, 24, 90, 91, 25, 26, 92, 27, 28, 29, 93, 94, 95, 30, 96, 31, 97, 32, 33, 34, 98, 99, 35, 36, 37, 38, 39, 100, 101, 40, 102, 41, 42, 43, 103, 44, 45, 46, 47, 104, 105, 106, 48, 107, 108, 49, 50, 51, 52, 109, 110, 53, 111, 112, 54, 113, 114, 55, 115, 116, 117, 118, 56, 119, 120, 57, 121, 58, 122, 123, 59, 124, 60, 61, 62, 125][i.val]!
  if j<63 then .inl (Fin.ofNat 63 j) else .inr (Fin.ofNat 63 (j-63))

def indexing : (Fin 63 ⊕ Fin 63) ≃ Fin 126 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 63,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*125)*(125-1)^62) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 62 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 62 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 62=(2*125)*(125-1)^62 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquares


namespace NonsplitNegative
def rawWords (i : ℕ) : ℕ := #[7567423954923939118, 6675961149429077265, 4110008236435497513, 2967341027955769589, 2321009455491588682, 4929695477970520205, 690105481975334296, 4801284944211234408, 888096150597964867, 1289276048587957396, 4008463676058467267, 4059936121548854432, 8784403981824003330, 6522040685213451797, 247635463653100711, 2796074190747078981, 5033737829506512395, 1675312513403693086, 4222279576857990299, 8372501698160206124, 6621512439643686984, 7196117179170494684, 7704379771946295600, 2195626557688541020, 3869433894713854624, 8052159994799328635, 8990055347091766246, 6455363923717696463, 4214866233306585885, 8141459009902768827, 2718657794035895706, 494650550871631040, 8931179210452276478, 6531292688568754663, 4329543165247507413, 8464912645782931251, 4003322036028057485, 45927532796444589, 1361542430326733947, 6206134440860554045, 955673826623709939, 4000411294643702247, 5136532952585848782, 4491076163248922220, 8188990542277259464, 913550663829665621, 3533920581585174067, 4762042684135632119, 2895385130349349366, 1925791533861398856, 3774494039684074011, 7026569901945376812, 5855392059173570896, 776643248563836602, 735227249387756320, 3758872312514197186, 7500840945533015629, 6657040238561911936, 7098851263051957538, 2549926924580567375, 7103965377081523718, 2129457281420270621, 1664243387814457507][i]!
def words (i : Fin 63) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 63 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 63 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 63, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 63, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-1386:ℤ) := by
  change cubicInteger (fun i : Fin 63 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-1386:ℤ) ∧
    87*(63:ℤ)^3+375*63*(4*63-3)+1000*((wordMatrix words-1)^3).trace-
      1110*125*(63-1)=(17648214:ℤ) ∧ 0≤(17648214:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 63 ⊕ Fin 63 → Fin 126
  | .inl i => Fin.ofNat 126 (#[0, 2, 3, 8, 11, 12, 13, 17, 18, 19, 22, 25, 28, 29, 30, 31, 32, 34, 35, 36, 39, 41, 42, 46, 47, 51, 56, 57, 58, 59, 60, 64, 66, 67, 68, 69, 72, 79, 83, 86, 87, 88, 89, 90, 91, 96, 97, 98, 99, 100, 101, 102, 108, 109, 113, 114, 115, 116, 119, 120, 121, 123, 124][i.val]!)
  | .inr i => Fin.ofNat 126 (#[1, 4, 5, 6, 7, 9, 10, 14, 15, 16, 20, 21, 23, 24, 26, 27, 33, 37, 38, 40, 43, 44, 45, 48, 49, 50, 52, 53, 54, 55, 61, 62, 63, 65, 70, 71, 73, 74, 75, 76, 77, 78, 80, 81, 82, 84, 85, 92, 93, 94, 95, 103, 104, 105, 106, 107, 110, 111, 112, 117, 118, 122, 125][i.val]!)

def pointPosition (i : Fin 126) : Fin 63 ⊕ Fin 63 :=
  let j : ℕ := #[0, 63, 1, 2, 64, 65, 66, 67, 3, 68, 69, 4, 5, 6, 70, 71, 72, 7, 8, 9, 73, 74, 10, 75, 76, 11, 77, 78, 12, 13, 14, 15, 16, 79, 17, 18, 19, 80, 81, 20, 82, 21, 22, 83, 84, 85, 23, 24, 86, 87, 88, 25, 89, 90, 91, 92, 26, 27, 28, 29, 30, 93, 94, 95, 31, 96, 32, 33, 34, 35, 97, 98, 36, 99, 100, 101, 102, 103, 104, 37, 105, 106, 107, 38, 108, 109, 39, 40, 41, 42, 43, 44, 110, 111, 112, 113, 45, 46, 47, 48, 49, 50, 51, 114, 115, 116, 117, 118, 52, 53, 119, 120, 121, 54, 55, 56, 57, 122, 123, 58, 59, 60, 124, 61, 62, 125][i.val]!
  if j<63 then .inl (Fin.ofNat 63 j) else .inr (Fin.ofNat 63 (j-63))

def indexing : (Fin 63 ⊕ Fin 63) ≃ Fin 126 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 63,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*125)*(125-1)^62) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 62 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 62 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 62=(2*125)*(125-1)^62 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegative


namespace SplitSquaresOpposite
def rawWords (i : ℕ) : ℕ := #[3322931203111606596, 2101872082337587880, 1055233732744348745, 1536042947892286502, 2320124551696370656, 2336654086484018394, 33719030943384885, 1372741199204464434, 469457309578337489, 2577087389551450258, 938938431873004012, 1418219015689822993, 4096311323731486601, 3237709507463945346, 836941144774351411, 1367787732555142406, 2551077949132793929, 396174248190206483, 2182168471504803933, 3855894280767173230, 2756131892400783916, 4124445635540769156, 4285262753408564776, 3823581572980411769, 1937853170468294374, 4370876525118007735, 3310687966057378123, 2076821681630155738, 4221205481047356605, 277570909882271484, 4453853570395884707, 3336331860058121203, 2223530598525192006, 4163334436195704673, 1853805963499285854, 4293080410677332380, 3961376457203159701, 1186456732829727004, 2328019717043459037, 775699260057710010, 2370050404432606790, 543027447136759400, 23346653370465977, 1658559709146759515, 2497606122537976254, 1081583206848488117, 1267091219937936871, 4325536816279859156, 2313955978092205931, 880635040941977426, 1252503631999233253, 2896679145410328739, 1885675898790924377, 2836723730450983030, 1487320322155197032, 2540122134333160196, 3937388584283885194, 986352750173735813, 1973326580199335183, 2745683462624408583, 384152042684061834, 696247436745191985, 0][i]!
def words (i : Fin 63) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 129, 249]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 63 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 63 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 63, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 63, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-3534:ℤ) := by
  change cubicInteger (fun i : Fin 63 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-3534:ℤ) ∧
    87*(63:ℤ)^3+375*63*(4*63-3)+1000*((wordMatrix words-1)^3).trace-
      1110*125*(63-1)=(15500214:ℤ) ∧ 0≤(15500214:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 63 ⊕ Fin 63 → Fin 126
  | .inl i => Fin.ofNat 126 (#[2, 3, 5, 8, 9, 12, 14, 16, 18, 20, 21, 22, 26, 29, 30, 31, 32, 33, 35, 38, 43, 48, 50, 51, 54, 55, 57, 58, 59, 63, 65, 67, 68, 69, 72, 73, 74, 75, 76, 79, 81, 82, 83, 85, 86, 87, 88, 92, 95, 96, 97, 98, 101, 104, 107, 112, 115, 117, 120, 122, 123, 124, 125][i.val]!)
  | .inr i => Fin.ofNat 126 (#[0, 1, 4, 6, 7, 10, 11, 13, 15, 17, 19, 23, 24, 25, 27, 28, 34, 36, 37, 39, 40, 41, 42, 44, 45, 46, 47, 49, 52, 53, 56, 60, 61, 62, 64, 66, 70, 71, 77, 78, 80, 84, 89, 90, 91, 93, 94, 99, 100, 102, 103, 105, 106, 108, 109, 110, 111, 113, 114, 116, 118, 119, 121][i.val]!)

def pointPosition (i : Fin 126) : Fin 63 ⊕ Fin 63 :=
  let j : ℕ := #[63, 64, 0, 1, 65, 2, 66, 67, 3, 4, 68, 69, 5, 70, 6, 71, 7, 72, 8, 73, 9, 10, 11, 74, 75, 76, 12, 77, 78, 13, 14, 15, 16, 17, 79, 18, 80, 81, 19, 82, 83, 84, 85, 20, 86, 87, 88, 89, 21, 90, 22, 23, 91, 92, 24, 25, 93, 26, 27, 28, 94, 95, 96, 29, 97, 30, 98, 31, 32, 33, 99, 100, 34, 35, 36, 37, 38, 101, 102, 39, 103, 40, 41, 42, 104, 43, 44, 45, 46, 105, 106, 107, 47, 108, 109, 48, 49, 50, 51, 110, 111, 52, 112, 113, 53, 114, 115, 54, 116, 117, 118, 119, 55, 120, 121, 56, 122, 57, 123, 124, 58, 125, 59, 60, 61, 62][i.val]!
  if j<63 then .inl (Fin.ofNat 63 j) else .inr (Fin.ofNat 63 (j-63))

def indexing : (Fin 63 ⊕ Fin 63) ≃ Fin 126 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 63,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*125)*(125-1)^62) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 62 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 62 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 62=(2*125)*(125-1)^62 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquaresOpposite


namespace SplitNonsquaresOpposite
def rawWords (i : ℕ) : ℕ := #[3247609001575561046, 3786061453776574953, 2956255792419244209, 1304344579011384882, 195232183072148173, 612051144116700878, 152822870158737715, 1676795291850792246, 1071957311906394819, 3145823926744657209, 956167772844413609, 2200129018917991062, 2438969129996578187, 1402710657887705857, 2589320147958371474, 3816171642390190115, 4105732365171303445, 1852155548569229934, 2840709667366350943, 3874203832986837592, 545867468422501876, 1108971328876972090, 4236186549918974181, 3179385687748762520, 4412181051916817120, 4194732175437903746, 1490087196426397477, 3778244945985719889, 3215299299269684470, 3733178988844046159, 1942069867178210620, 2087129316528934716, 1562103203519114986, 2259518598602066397, 2845227239709953507, 4274990151482616205, 4315191055799108430, 33309267058944925, 2719444203591295406, 714421051357658198, 1357019538498764129, 1531559999186961247, 3824347900777561800, 2459089928957423062, 3497624732694828861, 2882667509340651244, 9478265445662059, 3330205327494255711, 760232349957415065, 1466085209517154406, 3697879043036079348, 788992807640849002, 2418016760987103353, 1083336668450644784, 1805384619100337568, 1664381130735606546, 933378578177750661, 4084071200688729048, 4153029448536198531, 2839977626874089253, 488103018362546314, 1014642920391561735, 0][i]!
def words (i : Fin 63) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 125]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 63 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 63 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 63, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 63, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(3534:ℤ) := by
  change cubicInteger (fun i : Fin 63 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(3534:ℤ) ∧
    87*(63:ℤ)^3+375*63*(4*63-3)+1000*((wordMatrix words-1)^3).trace-
      1110*125*(63-1)=(22568214:ℤ) ∧ 0≤(22568214:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 63 ⊕ Fin 63 → Fin 126
  | .inl i => Fin.ofNat 126 (#[1, 4, 6, 7, 10, 11, 13, 15, 17, 19, 23, 24, 25, 27, 28, 34, 36, 37, 39, 40, 41, 42, 44, 45, 46, 47, 49, 52, 53, 56, 60, 61, 62, 64, 66, 70, 71, 77, 78, 80, 84, 89, 90, 91, 93, 94, 99, 100, 102, 103, 105, 106, 108, 109, 110, 111, 113, 114, 116, 118, 119, 121, 125][i.val]!)
  | .inr i => Fin.ofNat 126 (#[0, 2, 3, 5, 8, 9, 12, 14, 16, 18, 20, 21, 22, 26, 29, 30, 31, 32, 33, 35, 38, 43, 48, 50, 51, 54, 55, 57, 58, 59, 63, 65, 67, 68, 69, 72, 73, 74, 75, 76, 79, 81, 82, 83, 85, 86, 87, 88, 92, 95, 96, 97, 98, 101, 104, 107, 112, 115, 117, 120, 122, 123, 124][i.val]!)

def pointPosition (i : Fin 126) : Fin 63 ⊕ Fin 63 :=
  let j : ℕ := #[63, 0, 64, 65, 1, 66, 2, 3, 67, 68, 4, 5, 69, 6, 70, 7, 71, 8, 72, 9, 73, 74, 75, 10, 11, 12, 76, 13, 14, 77, 78, 79, 80, 81, 15, 82, 16, 17, 83, 18, 19, 20, 21, 84, 22, 23, 24, 25, 85, 26, 86, 87, 27, 28, 88, 89, 29, 90, 91, 92, 30, 31, 32, 93, 33, 94, 34, 95, 96, 97, 35, 36, 98, 99, 100, 101, 102, 37, 38, 103, 39, 104, 105, 106, 40, 107, 108, 109, 110, 41, 42, 43, 111, 44, 45, 112, 113, 114, 115, 46, 47, 116, 48, 49, 117, 50, 51, 118, 52, 53, 54, 55, 119, 56, 57, 120, 58, 121, 59, 60, 122, 61, 123, 124, 125, 62][i.val]!
  if j<63 then .inl (Fin.ofNat 63 j) else .inr (Fin.ofNat 63 (j-63))

def indexing : (Fin 63 ⊕ Fin 63) ≃ Fin 126 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 63,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*125)*(125-1)^62) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 62 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 62 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 62=(2*125)*(125-1)^62 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquaresOpposite


namespace NonsplitNegativeOpposite
def rawWords (i : ℕ) : ℕ := #[1153257912871786606, 2471454030153526577, 3195778880562403537, 1205732961415471585, 2329446701301962342, 160693598296442523, 3073105391720669469, 132007920571029548, 2711822248786080842, 813044589933390896, 2127281967049593650, 3607307501162263175, 4117254278752587157, 1893409557024262986, 3929159641185140224, 2679359782168046753, 1413129492281300337, 3942529595681087550, 315709209697142172, 2850275112552465108, 1963530663785956420, 3986592967392512425, 2085100009015748944, 3562571469701047108, 785195976429901449, 4085148096282647643, 715076949657023717, 4249195951980854766, 4384463622363950814, 3853227611903918893, 1674178076232349816, 1042447429747914038, 2083768617501671340, 2643052732111821649, 2096715705867743005, 3683429583144422970, 3406984999815885679, 2205833401279215421, 1293983583249592631, 198983279445538733, 407888491601981309, 177426946736295710, 1678384453545555182, 482276144871570654, 956565358389341659, 3397148880715643045, 1876627206559601138, 3541523245735259900, 740957887592160349, 3787763182336670008, 1164376674248944834, 415814679573137966, 757179150530445500, 685861351542133096, 3677495660814541462, 520739578001966536, 3812496493000628096, 58950010061679202, 687429203593708804, 2607989034832639556, 2397819826114624521, 1820193233924970838, 0][i]!
def words (i : Fin 63) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 63 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 63 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 63, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 63, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(1386:ℤ) := by
  change cubicInteger (fun i : Fin 63 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(1386:ℤ) ∧
    87*(63:ℤ)^3+375*63*(4*63-3)+1000*((wordMatrix words-1)^3).trace-
      1110*125*(63-1)=(20420214:ℤ) ∧ 0≤(20420214:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 63 ⊕ Fin 63 → Fin 126
  | .inl i => Fin.ofNat 126 (#[1, 4, 5, 6, 7, 9, 10, 14, 15, 16, 20, 21, 23, 24, 26, 27, 33, 37, 38, 40, 43, 44, 45, 48, 49, 50, 52, 53, 54, 55, 61, 62, 63, 65, 70, 71, 73, 74, 75, 76, 77, 78, 80, 81, 82, 84, 85, 92, 93, 94, 95, 103, 104, 105, 106, 107, 110, 111, 112, 117, 118, 122, 125][i.val]!)
  | .inr i => Fin.ofNat 126 (#[0, 2, 3, 8, 11, 12, 13, 17, 18, 19, 22, 25, 28, 29, 30, 31, 32, 34, 35, 36, 39, 41, 42, 46, 47, 51, 56, 57, 58, 59, 60, 64, 66, 67, 68, 69, 72, 79, 83, 86, 87, 88, 89, 90, 91, 96, 97, 98, 99, 100, 101, 102, 108, 109, 113, 114, 115, 116, 119, 120, 121, 123, 124][i.val]!)

def pointPosition (i : Fin 126) : Fin 63 ⊕ Fin 63 :=
  let j : ℕ := #[63, 0, 64, 65, 1, 2, 3, 4, 66, 5, 6, 67, 68, 69, 7, 8, 9, 70, 71, 72, 10, 11, 73, 12, 13, 74, 14, 15, 75, 76, 77, 78, 79, 16, 80, 81, 82, 17, 18, 83, 19, 84, 85, 20, 21, 22, 86, 87, 23, 24, 25, 88, 26, 27, 28, 29, 89, 90, 91, 92, 93, 30, 31, 32, 94, 33, 95, 96, 97, 98, 34, 35, 99, 36, 37, 38, 39, 40, 41, 100, 42, 43, 44, 101, 45, 46, 102, 103, 104, 105, 106, 107, 47, 48, 49, 50, 108, 109, 110, 111, 112, 113, 114, 51, 52, 53, 54, 55, 115, 116, 56, 57, 58, 117, 118, 119, 120, 59, 60, 121, 122, 123, 61, 124, 125, 62][i.val]!
  if j<63 then .inl (Fin.ofNat 63 j) else .inr (Fin.ofNat 63 (j-63))

def indexing : (Fin 63 ⊕ Fin 63) ≃ Fin 126 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 63,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*125)*(125-1)^62) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 62 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 62 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 62=(2*125)*(125-1)^62 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegativeOpposite

end PaleyBits125
