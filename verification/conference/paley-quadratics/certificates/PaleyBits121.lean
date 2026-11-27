import Quantum.Hadamard.ConferenceBitCompletion
open Hadamard.BitTrace Hadamard.DeterminantRatio Matrix
set_option maxHeartbeats 12000000
set_option maxRecDepth 60000
namespace PaleyBits121

def rawFull (i : ℕ) : ℕ := #[1406994169476867448173002724198979584, 155532981209203264617063287755651072, 309767888203772896113970237681463296, 618237702502397021391187838585858048, 1236475404695460074901506150841309184, 2471653369001435441283146189486929920, 2286148820338187833880494602203918336, 1915139089495877588496772049583136768, 1173119628120590991859213797070585856, 2344941815851848317139019423576457216, 2032725080523349596990308422379833344, 2416220218496753148663486592283837499, 2175282519638308184639532976851386487, 1692109047706935739198886078192812270, 725762737669188804728372036949246428, 1451524841822411389435954149225137080, 245891765980139730186110521680332656, 491782898134979420044479006251157217, 982267722055476175158329719247603139, 1963238003412284863394305534257529735, 1269318089469220572160677751979771662, 2537338105033292447235550356420167197, 1032407169893569514850662633856687941, 2064814339786987914009884652485197451, 1471172688313629091997489048301565207, 285187458962726177249638278631449135, 569077477226633751921510826230269022, 1138154320627967463515279615351029949, 2275010567041452335814867230429481338, 1891565142822406893702989875210230516, 1125971734773800570425183871658900968, 2251943469238116131029040266779063249, 1845431580731700630329138372915818402, 897370644014128497103848292749028123, 1794741287718772058137316598188629558, 931027217693012410830772326344735853, 1862053801870058675391702234416904411, 1066949052559619271519187314009108918, 2132600030904755951822682627745639276, 1606744070549165093908148697250387672, 555032783044464662029490773628003761, 1108768125699444615575126631311688547, 2217535617573589117071581311286546118, 1777913317791980121455722414856803725, 821988766181425715619946242573392563, 1643976898537702359101678475440928102, 630795879720055637362399912004905677, 1260294318741443714087527201791991194, 2519290563268404763244426110329271093, 2380125135276462716751635662417651306, 2101794912808242759869864835221472469, 1546431274745472376545874910737435051, 435704631826261778156881967509609302, 870111189437889923193607597189379756, 1740222378875628730695774579150581081, 630350475856370493430166475391736441, 1259402877807441247798041073188287730, 2518805755305548601502171314112588261, 2380452959739933017870012326129488842, 2102449928219368257813280066610245524, 1546444498694053841993153643606660905, 435731079723575750955921345819881043, 870164719057817909083399602486205607, 1740328804290486819743539071848984911, 822201617011293009406898268188009118, 1644403233713101082743416549066591548, 1606618642478373828288093130341992933, 554781926902882057002420945744794570, 1109563220289949009675457414843805588, 2217828999881230532428560925449934633, 1777202641708595539070315230027097683, 897247365752659145110244518660754599, 1794494097989503112176185851285510479, 931830278623808111700925116087351966, 1862362483342467452565097595397635388, 1066268975424588169107914934126441081, 2132537317024027266077615858547025138, 1844918223827730769996063806829046997, 1032677896784297281106867405925011883, 2064058353179260895634326641285309270, 1470958155487508574287857403809058476, 284757760104004005381860047912607065, 569514886692192832719416909789215411, 1137732332994901030705908817853054310, 2275464665989651019435313304882705101, 1892473974234619365201226490329032090, 1126492590724707024958592110625540917, 2251687107544114310854892343655896682, 726558378461706159319011069148966285, 1451819316224593789811221488676461339, 246480715093838424994509660817634870, 491663989798192141505164405690950765, 982030539207050690181885722228345051, 1962763638024616745630846442731313590, 1268369358384701558231289351891530604, 2536738716460069148581709177452654296, 2416319515255606290418078536933627313, 2175481113155863499995200034990304099, 1692506868257861400416634755041416902, 1914659802038268378878376223657716271, 1172161052896189720469022022542351454, 2344322105482894431116716568545964221, 2031486293301105887298565283126667642, 1405814669247013661945683979769666292, 154471420829495390860964425968236008, 308942208143175603641596886061376465, 617883782770384987262403847449397154, 1235766932024803828254965276626227013, 2471533863740273762416019720988466827, 2285909176609383265946779234243851543, 687008871814876683678223986425283, 75943838481056281551300433474439, 151253851661998484430649530117902, 301873878174998545601165936809501, 603747756198955114698001050215483, 1206861996582732149064036225335415, 1116283603680755778261960254982382, 935126508542908978758189477335516, 572812318418257320243756736850872, 1144991121021410311103036827918192, 992541543224291795405424034365153, 0][i]!
def fullRows (i : Fin 122) : ℕ := rawFull i.val

private theorem fullSymmetric : (wordMatrix fullRows).IsSymm := by
  have h : ∀ i j : Fin 122, sign (fullRows i) j.val=sign (fullRows j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem fullDiagonal : ∀ i : Fin 122, sign (fullRows i) i.val=1 := by decide +kernel
private theorem lower0 : (lowerRow 122 rawFull) 0=true := by decide +kernel
private theorem lower1 : (lowerRow 122 rawFull) 1=true := by decide +kernel
private theorem lower2 : (lowerRow 122 rawFull) 2=true := by decide +kernel
private theorem lower3 : (lowerRow 122 rawFull) 3=true := by decide +kernel
private theorem lower4 : (lowerRow 122 rawFull) 4=true := by decide +kernel
private theorem lower5 : (lowerRow 122 rawFull) 5=true := by decide +kernel
private theorem lower6 : (lowerRow 122 rawFull) 6=true := by decide +kernel
private theorem lower7 : (lowerRow 122 rawFull) 7=true := by decide +kernel
private theorem lower8 : (lowerRow 122 rawFull) 8=true := by decide +kernel
private theorem lower9 : (lowerRow 122 rawFull) 9=true := by decide +kernel
private theorem lower10 : (lowerRow 122 rawFull) 10=true := by decide +kernel
private theorem lower11 : (lowerRow 122 rawFull) 11=true := by decide +kernel
private theorem lower12 : (lowerRow 122 rawFull) 12=true := by decide +kernel
private theorem lower13 : (lowerRow 122 rawFull) 13=true := by decide +kernel
private theorem lower14 : (lowerRow 122 rawFull) 14=true := by decide +kernel
private theorem lower15 : (lowerRow 122 rawFull) 15=true := by decide +kernel
private theorem lower16 : (lowerRow 122 rawFull) 16=true := by decide +kernel
private theorem lower17 : (lowerRow 122 rawFull) 17=true := by decide +kernel
private theorem lower18 : (lowerRow 122 rawFull) 18=true := by decide +kernel
private theorem lower19 : (lowerRow 122 rawFull) 19=true := by decide +kernel
private theorem lower20 : (lowerRow 122 rawFull) 20=true := by decide +kernel
private theorem lower21 : (lowerRow 122 rawFull) 21=true := by decide +kernel
private theorem lower22 : (lowerRow 122 rawFull) 22=true := by decide +kernel
private theorem lower23 : (lowerRow 122 rawFull) 23=true := by decide +kernel
private theorem lower24 : (lowerRow 122 rawFull) 24=true := by decide +kernel
private theorem lower25 : (lowerRow 122 rawFull) 25=true := by decide +kernel
private theorem lower26 : (lowerRow 122 rawFull) 26=true := by decide +kernel
private theorem lower27 : (lowerRow 122 rawFull) 27=true := by decide +kernel
private theorem lower28 : (lowerRow 122 rawFull) 28=true := by decide +kernel
private theorem lower29 : (lowerRow 122 rawFull) 29=true := by decide +kernel
private theorem lower30 : (lowerRow 122 rawFull) 30=true := by decide +kernel
private theorem lower31 : (lowerRow 122 rawFull) 31=true := by decide +kernel
private theorem lower32 : (lowerRow 122 rawFull) 32=true := by decide +kernel
private theorem lower33 : (lowerRow 122 rawFull) 33=true := by decide +kernel
private theorem lower34 : (lowerRow 122 rawFull) 34=true := by decide +kernel
private theorem lower35 : (lowerRow 122 rawFull) 35=true := by decide +kernel
private theorem lower36 : (lowerRow 122 rawFull) 36=true := by decide +kernel
private theorem lower37 : (lowerRow 122 rawFull) 37=true := by decide +kernel
private theorem lower38 : (lowerRow 122 rawFull) 38=true := by decide +kernel
private theorem lower39 : (lowerRow 122 rawFull) 39=true := by decide +kernel
private theorem lower40 : (lowerRow 122 rawFull) 40=true := by decide +kernel
private theorem lower41 : (lowerRow 122 rawFull) 41=true := by decide +kernel
private theorem lower42 : (lowerRow 122 rawFull) 42=true := by decide +kernel
private theorem lower43 : (lowerRow 122 rawFull) 43=true := by decide +kernel
private theorem lower44 : (lowerRow 122 rawFull) 44=true := by decide +kernel
private theorem lower45 : (lowerRow 122 rawFull) 45=true := by decide +kernel
private theorem lower46 : (lowerRow 122 rawFull) 46=true := by decide +kernel
private theorem lower47 : (lowerRow 122 rawFull) 47=true := by decide +kernel
private theorem lower48 : (lowerRow 122 rawFull) 48=true := by decide +kernel
private theorem lower49 : (lowerRow 122 rawFull) 49=true := by decide +kernel
private theorem lower50 : (lowerRow 122 rawFull) 50=true := by decide +kernel
private theorem lower51 : (lowerRow 122 rawFull) 51=true := by decide +kernel
private theorem lower52 : (lowerRow 122 rawFull) 52=true := by decide +kernel
private theorem lower53 : (lowerRow 122 rawFull) 53=true := by decide +kernel
private theorem lower54 : (lowerRow 122 rawFull) 54=true := by decide +kernel
private theorem lower55 : (lowerRow 122 rawFull) 55=true := by decide +kernel
private theorem lower56 : (lowerRow 122 rawFull) 56=true := by decide +kernel
private theorem lower57 : (lowerRow 122 rawFull) 57=true := by decide +kernel
private theorem lower58 : (lowerRow 122 rawFull) 58=true := by decide +kernel
private theorem lower59 : (lowerRow 122 rawFull) 59=true := by decide +kernel
private theorem lower60 : (lowerRow 122 rawFull) 60=true := by decide +kernel
private theorem lower61 : (lowerRow 122 rawFull) 61=true := by decide +kernel
private theorem lower62 : (lowerRow 122 rawFull) 62=true := by decide +kernel
private theorem lower63 : (lowerRow 122 rawFull) 63=true := by decide +kernel
private theorem lower64 : (lowerRow 122 rawFull) 64=true := by decide +kernel
private theorem lower65 : (lowerRow 122 rawFull) 65=true := by decide +kernel
private theorem lower66 : (lowerRow 122 rawFull) 66=true := by decide +kernel
private theorem lower67 : (lowerRow 122 rawFull) 67=true := by decide +kernel
private theorem lower68 : (lowerRow 122 rawFull) 68=true := by decide +kernel
private theorem lower69 : (lowerRow 122 rawFull) 69=true := by decide +kernel
private theorem lower70 : (lowerRow 122 rawFull) 70=true := by decide +kernel
private theorem lower71 : (lowerRow 122 rawFull) 71=true := by decide +kernel
private theorem lower72 : (lowerRow 122 rawFull) 72=true := by decide +kernel
private theorem lower73 : (lowerRow 122 rawFull) 73=true := by decide +kernel
private theorem lower74 : (lowerRow 122 rawFull) 74=true := by decide +kernel
private theorem lower75 : (lowerRow 122 rawFull) 75=true := by decide +kernel
private theorem lower76 : (lowerRow 122 rawFull) 76=true := by decide +kernel
private theorem lower77 : (lowerRow 122 rawFull) 77=true := by decide +kernel
private theorem lower78 : (lowerRow 122 rawFull) 78=true := by decide +kernel
private theorem lower79 : (lowerRow 122 rawFull) 79=true := by decide +kernel
private theorem lower80 : (lowerRow 122 rawFull) 80=true := by decide +kernel
private theorem lower81 : (lowerRow 122 rawFull) 81=true := by decide +kernel
private theorem lower82 : (lowerRow 122 rawFull) 82=true := by decide +kernel
private theorem lower83 : (lowerRow 122 rawFull) 83=true := by decide +kernel
private theorem lower84 : (lowerRow 122 rawFull) 84=true := by decide +kernel
private theorem lower85 : (lowerRow 122 rawFull) 85=true := by decide +kernel
private theorem lower86 : (lowerRow 122 rawFull) 86=true := by decide +kernel
private theorem lower87 : (lowerRow 122 rawFull) 87=true := by decide +kernel
private theorem lower88 : (lowerRow 122 rawFull) 88=true := by decide +kernel
private theorem lower89 : (lowerRow 122 rawFull) 89=true := by decide +kernel
private theorem lower90 : (lowerRow 122 rawFull) 90=true := by decide +kernel
private theorem lower91 : (lowerRow 122 rawFull) 91=true := by decide +kernel
private theorem lower92 : (lowerRow 122 rawFull) 92=true := by decide +kernel
private theorem lower93 : (lowerRow 122 rawFull) 93=true := by decide +kernel
private theorem lower94 : (lowerRow 122 rawFull) 94=true := by decide +kernel
private theorem lower95 : (lowerRow 122 rawFull) 95=true := by decide +kernel
private theorem lower96 : (lowerRow 122 rawFull) 96=true := by decide +kernel
private theorem lower97 : (lowerRow 122 rawFull) 97=true := by decide +kernel
private theorem lower98 : (lowerRow 122 rawFull) 98=true := by decide +kernel
private theorem lower99 : (lowerRow 122 rawFull) 99=true := by decide +kernel
private theorem lower100 : (lowerRow 122 rawFull) 100=true := by decide +kernel
private theorem lower101 : (lowerRow 122 rawFull) 101=true := by decide +kernel
private theorem lower102 : (lowerRow 122 rawFull) 102=true := by decide +kernel
private theorem lower103 : (lowerRow 122 rawFull) 103=true := by decide +kernel
private theorem lower104 : (lowerRow 122 rawFull) 104=true := by decide +kernel
private theorem lower105 : (lowerRow 122 rawFull) 105=true := by decide +kernel
private theorem lower106 : (lowerRow 122 rawFull) 106=true := by decide +kernel
private theorem lower107 : (lowerRow 122 rawFull) 107=true := by decide +kernel
private theorem lower108 : (lowerRow 122 rawFull) 108=true := by decide +kernel
private theorem lower109 : (lowerRow 122 rawFull) 109=true := by decide +kernel
private theorem lower110 : (lowerRow 122 rawFull) 110=true := by decide +kernel
private theorem lower111 : (lowerRow 122 rawFull) 111=true := by decide +kernel
private theorem lower112 : (lowerRow 122 rawFull) 112=true := by decide +kernel
private theorem lower113 : (lowerRow 122 rawFull) 113=true := by decide +kernel
private theorem lower114 : (lowerRow 122 rawFull) 114=true := by decide +kernel
private theorem lower115 : (lowerRow 122 rawFull) 115=true := by decide +kernel
private theorem lower116 : (lowerRow 122 rawFull) 116=true := by decide +kernel
private theorem lower117 : (lowerRow 122 rawFull) 117=true := by decide +kernel
private theorem lower118 : (lowerRow 122 rawFull) 118=true := by decide +kernel
private theorem lower119 : (lowerRow 122 rawFull) 119=true := by decide +kernel
private theorem lower120 : (lowerRow 122 rawFull) 120=true := by decide +kernel
private theorem lower121 : (lowerRow 122 rawFull) 121=true := by decide +kernel
private theorem lowerChecked : allBelow 122 (lowerRow 122 rawFull)=true := by
  have h : allBelow 0 (lowerRow 122 rawFull)=true := rfl
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
  exact h

private theorem fullPairs : ∀ i j : Fin 122, i≠j →
    correlation 122 (fullRows i) (fullRows j)=2*sign (fullRows i) j.val :=
  correlations_of_lower rawFull fullSymmetric lowerChecked


namespace SplitSquares
def rawWords (i : ℕ) : ℕ := #[0, 260359224166680576, 517297055541336064, 1106536258744334336, 2034171203709005824, 1941594086318172160, 1621061745970731008, 1073709902919907328, 2148668625934544896, 1848558835287252992, 1283101116690186240, 671981816379867374, 1278491836082618844, 281742274265678776, 384412864666077040, 2201914998886434574, 965575184983585886, 1631745303879139706, 927396755295699700, 1885169698874625512, 951641730560606114, 858802813722138166, 1847949562640939446, 1321455716696554348, 516078486165026520, 1565443552523626182, 475856763392159078, 2186197035823150490, 1786402665849544298, 825902175036031830, 1544973669974904492, 2222578024806698226, 1789579557173933002, 1311404081879576468, 1324521736465996446, 459212406984029500, 881951274050413514, 1975661873487826836, 1708726869333658270, 929241277427031356, 1336557605003951346, 1293729888293792598, 251147033873667756, 1991647957112528230, 865395887347236250, 1670696015597495914, 367060658109132342, 1038141722138567094, 2222571079529548652, 2067214257898233560, 702605355516417734, 2090203733293839454, 1225900884233574778, 755323207627508, 217728238756392424, 1082847161485801378, 62045855140642574, 54515361376805102, 39389835740824028, 40418810741492664, 7647549423523696][i]!
def words (i : Fin 61) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[121, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 61 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 61 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 61, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 61, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(3540:ℤ) := by
  change cubicInteger (fun i : Fin 61 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(3540:ℤ) ∧
    87*(61:ℤ)^3+375*61*(4*61-3)+1000*((wordMatrix words-1)^3).trace-
      1110*121*(61-1)=(20741622:ℤ) ∧ 0≤(20741622:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 61 ⊕ Fin 61 → Fin 122
  | .inl i => Fin.ofNat 122 (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 15, 16, 20, 26, 28, 29, 30, 32, 34, 37, 38, 39, 42, 45, 47, 49, 52, 53, 56, 58, 59, 64, 65, 67, 68, 73, 74, 76, 79, 80, 83, 85, 87, 90, 93, 94, 95, 98, 100, 102, 103, 104, 106, 112, 116, 117, 118, 119][i.val]!)
  | .inr i => Fin.ofNat 122 (#[11, 12, 17, 18, 19, 21, 22, 23, 24, 25, 27, 31, 33, 35, 36, 40, 41, 43, 44, 46, 48, 50, 51, 54, 55, 57, 60, 61, 62, 63, 66, 69, 70, 71, 72, 75, 77, 78, 81, 82, 84, 86, 88, 89, 91, 92, 96, 97, 99, 101, 105, 107, 108, 109, 110, 111, 113, 114, 115, 120, 121][i.val]!)

def pointPosition (i : Fin 122) : Fin 61 ⊕ Fin 61 :=
  let j : ℕ := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 61, 62, 11, 12, 13, 14, 63, 64, 65, 15, 66, 67, 68, 69, 70, 16, 71, 17, 18, 19, 72, 20, 73, 21, 74, 75, 22, 23, 24, 76, 77, 25, 78, 79, 26, 80, 27, 81, 28, 82, 83, 29, 30, 84, 85, 31, 86, 32, 33, 87, 88, 89, 90, 34, 35, 91, 36, 37, 92, 93, 94, 95, 38, 39, 96, 40, 97, 98, 41, 42, 99, 100, 43, 101, 44, 102, 45, 103, 104, 46, 105, 106, 47, 48, 49, 107, 108, 50, 109, 51, 110, 52, 53, 54, 111, 55, 112, 113, 114, 115, 116, 56, 117, 118, 119, 57, 58, 59, 60, 120, 121][i.val]!
  if j<61 then .inl (Fin.ofNat 61 j) else .inr (Fin.ofNat 61 (j-61))

def indexing : (Fin 61 ⊕ Fin 61) ≃ Fin 122 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 61,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*121)*(121-1)^60) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 60 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 60 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 60=(2*121)*(121-1)^60 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquares


namespace SplitNonsquares
def rawWords (i : ℕ) : ℕ := #[2305843009213693950, 1203408521834062209, 1433433143409169281, 1110221875454357249, 887978180078929409, 1890333611051088897, 1825903495473428609, 550401411462930503, 2115660782589141007, 1922630883223715869, 563430668145844281, 750319340217196649, 1253537499520565349, 984751895040495083, 189086133564477287, 1673561210558612999, 848777052318335385, 368981563123176441, 1645033601546852085, 1053360958405391015, 645657175561192395, 1471246605100484405, 1557846463172914521, 1847934437242124915, 2182335154654345587, 634635261861328279, 1458413874026278555, 1847270856429010509, 278562013956445275, 517746054021073079, 2184470355880417709, 1501733184933116299, 1895721463149339965, 1624464522694843121, 978585003979627875, 1818833301245625039, 917394570221542933, 1343928698241891515, 562272717126388029, 552948894786548303, 961615407093161175, 1617038594372512661, 712624347245041419, 853997247269481179, 1672526448584627511, 1109577200180632785, 883276772315976171, 1202468167246605941, 1438904868584676515, 1261144457008079603, 1369148084254102341, 792925846526159657, 1009258339632072051, 2018095010178710191, 1765814857412975965, 19013814227658375, 4290071985632717, 8227522853326509, 13638165691540889, 33896969795087225, 29152639436755815][i]!
def words (i : Fin 61) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[241, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 61 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 61 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 61, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 61, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-3540:ℤ) := by
  change cubicInteger (fun i : Fin 61 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-3540:ℤ) ∧
    87*(61:ℤ)^3+375*61*(4*61-3)+1000*((wordMatrix words-1)^3).trace-
      1110*121*(61-1)=(13661622:ℤ) ∧ 0≤(13661622:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 61 ⊕ Fin 61 → Fin 122
  | .inl i => Fin.ofNat 122 (#[0, 11, 12, 17, 18, 19, 21, 22, 23, 24, 25, 27, 31, 33, 35, 36, 40, 41, 43, 44, 46, 48, 50, 51, 54, 55, 57, 60, 61, 62, 63, 66, 69, 70, 71, 72, 75, 77, 78, 81, 82, 84, 86, 88, 89, 91, 92, 96, 97, 99, 101, 105, 107, 108, 109, 110, 111, 113, 114, 115, 120][i.val]!)
  | .inr i => Fin.ofNat 122 (#[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 15, 16, 20, 26, 28, 29, 30, 32, 34, 37, 38, 39, 42, 45, 47, 49, 52, 53, 56, 58, 59, 64, 65, 67, 68, 73, 74, 76, 79, 80, 83, 85, 87, 90, 93, 94, 95, 98, 100, 102, 103, 104, 106, 112, 116, 117, 118, 119, 121][i.val]!)

def pointPosition (i : Fin 122) : Fin 61 ⊕ Fin 61 :=
  let j : ℕ := #[0, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 1, 2, 71, 72, 73, 74, 3, 4, 5, 75, 6, 7, 8, 9, 10, 76, 11, 77, 78, 79, 12, 80, 13, 81, 14, 15, 82, 83, 84, 16, 17, 85, 18, 19, 86, 20, 87, 21, 88, 22, 23, 89, 90, 24, 25, 91, 26, 92, 93, 27, 28, 29, 30, 94, 95, 31, 96, 97, 32, 33, 34, 35, 98, 99, 36, 100, 37, 38, 101, 102, 39, 40, 103, 41, 104, 42, 105, 43, 44, 106, 45, 46, 107, 108, 109, 47, 48, 110, 49, 111, 50, 112, 113, 114, 51, 115, 52, 53, 54, 55, 56, 116, 57, 58, 59, 117, 118, 119, 120, 60, 121][i.val]!
  if j<61 then .inl (Fin.ofNat 61 j) else .inr (Fin.ofNat 61 (j-61))

def indexing : (Fin 61 ⊕ Fin 61) ≃ Fin 122 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 61,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*121)*(121-1)^60) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 60 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 60 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 60=(2*121)*(121-1)^60 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquares


namespace NonsplitNegative
def rawWords (i : ℕ) : ℕ := #[1096994716163456000, 2276482526590858240, 1596057227422230528, 733927680554953216, 1801109604952867328, 1175613541086905856, 1579677816289301504, 401878622708242944, 849700338716540416, 681702271069516216, 1931347677953450339, 479818964804010381, 1037360269028885443, 1274214534079710991, 971332078016923438, 1923377457718496826, 1725828443313539305, 1223425319927593269, 980870686966866539, 1948848848629761000, 122845748273427942, 1902157440103837509, 1793178935549599963, 2129477476769536822, 1421951071354256101, 1681696361110517066, 213122325887345586, 410631901530418771, 664016203515339893, 280976279654030562, 1620870045822209451, 986536189695248215, 760254978730070055, 1836843850545086158, 2257339703079479580, 361242347808407266, 2262742157463889868, 175020269361714577, 1771757450672958891, 931150040680864599, 1070282226200604956, 671590529350968505, 101613494479210349, 2154132276660889897, 1262980975356006710, 809525459948321610, 1701238314561401501, 1599906480086871986, 2134739406654379659, 801659822575149470, 1180216826923333214, 1279134046027148633, 522667450305069747, 290390585745078877, 2025511208486131568, 1732014220080819666, 1737120751743230915, 1158235673667935503, 32028347618121927, 126993419345909531, 274113017357771894][i]!
def words (i : Fin 61) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 61 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 61 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 61, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 61, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(0:ℤ) := by
  change cubicInteger (fun i : Fin 61 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(0:ℤ) ∧
    87*(61:ℤ)^3+375*61*(4*61-3)+1000*((wordMatrix words-1)^3).trace-
      1110*121*(61-1)=(17201622:ℤ) ∧ 0≤(17201622:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 61 ⊕ Fin 61 → Fin 122
  | .inl i => Fin.ofNat 122 (#[0, 1, 2, 4, 5, 6, 7, 9, 10, 16, 18, 21, 23, 24, 26, 28, 31, 35, 36, 39, 42, 43, 44, 45, 46, 47, 49, 51, 57, 58, 61, 62, 63, 64, 65, 67, 68, 69, 70, 71, 74, 75, 77, 81, 83, 85, 86, 87, 89, 90, 93, 96, 97, 101, 104, 106, 108, 109, 111, 114, 116][i.val]!)
  | .inr i => Fin.ofNat 122 (#[3, 8, 11, 12, 13, 14, 15, 17, 19, 20, 22, 25, 27, 29, 30, 32, 33, 34, 37, 38, 40, 41, 48, 50, 52, 53, 54, 55, 56, 59, 60, 66, 72, 73, 76, 78, 79, 80, 82, 84, 88, 91, 92, 94, 95, 98, 99, 100, 102, 103, 105, 107, 110, 112, 113, 115, 117, 118, 119, 120, 121][i.val]!)

def pointPosition (i : Fin 122) : Fin 61 ⊕ Fin 61 :=
  let j : ℕ := #[0, 1, 2, 61, 3, 4, 5, 6, 62, 7, 8, 63, 64, 65, 66, 67, 9, 68, 10, 69, 70, 11, 71, 12, 13, 72, 14, 73, 15, 74, 75, 16, 76, 77, 78, 17, 18, 79, 80, 19, 81, 82, 20, 21, 22, 23, 24, 25, 83, 26, 84, 27, 85, 86, 87, 88, 89, 28, 29, 90, 91, 30, 31, 32, 33, 34, 92, 35, 36, 37, 38, 39, 93, 94, 40, 41, 95, 42, 96, 97, 98, 43, 99, 44, 100, 45, 46, 47, 101, 48, 49, 102, 103, 50, 104, 105, 51, 52, 106, 107, 108, 53, 109, 110, 54, 111, 55, 112, 56, 57, 113, 58, 114, 115, 59, 116, 60, 117, 118, 119, 120, 121][i.val]!
  if j<61 then .inl (Fin.ofNat 61 j) else .inr (Fin.ofNat 61 (j-61))

def indexing : (Fin 61 ⊕ Fin 61) ≃ Fin 122 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 61,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*121)*(121-1)^60) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 60 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 60 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 60=(2*121)*(121-1)^60 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegative


namespace SplitSquaresOpposite
def rawWords (i : ℕ) : ℕ := #[601704260917031104, 716716571704584640, 555110937727178624, 443989090039464704, 945166805525544448, 912951747736714304, 275200705731465251, 1057830391294570503, 961315441611857934, 281715334072922140, 375159670108598324, 626768749760282674, 492375947520247541, 94543066782238643, 836780605279306499, 424388526159167692, 184490781561588220, 822516800773426042, 526680479202695507, 322828587780596197, 735623302550242202, 778923231586457260, 923967218621062457, 1091167577327172793, 317317630930664139, 729206937013139277, 923635428214505254, 139281006978222637, 258873027010536539, 1092235177940208854, 750866592466558149, 947860731574669982, 812232261347421560, 489292501989813937, 909416650622812519, 458697285110771466, 671964349120945757, 281136358563194014, 276474447393274151, 480807703546580587, 808519297186256330, 356312173622520709, 426998623634740589, 836263224292313755, 554788600090316392, 441638386157988085, 601234083623302970, 719452434292338257, 630572228504039801, 684574042127051170, 396462923263079828, 504629169816036025, 1009047505089355095, 882907428706487982, 9506907113829187, 2145035992816358, 4113761426663254, 6819082845770444, 16948484897543612, 14576319718377907, 0][i]!
def words (i : Fin 61) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 121, 241]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 61 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 61 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 61, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 61, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-3540:ℤ) := by
  change cubicInteger (fun i : Fin 61 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-3540:ℤ) ∧
    87*(61:ℤ)^3+375*61*(4*61-3)+1000*((wordMatrix words-1)^3).trace-
      1110*121*(61-1)=(13661622:ℤ) ∧ 0≤(13661622:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 61 ⊕ Fin 61 → Fin 122
  | .inl i => Fin.ofNat 122 (#[11, 12, 17, 18, 19, 21, 22, 23, 24, 25, 27, 31, 33, 35, 36, 40, 41, 43, 44, 46, 48, 50, 51, 54, 55, 57, 60, 61, 62, 63, 66, 69, 70, 71, 72, 75, 77, 78, 81, 82, 84, 86, 88, 89, 91, 92, 96, 97, 99, 101, 105, 107, 108, 109, 110, 111, 113, 114, 115, 120, 121][i.val]!)
  | .inr i => Fin.ofNat 122 (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 15, 16, 20, 26, 28, 29, 30, 32, 34, 37, 38, 39, 42, 45, 47, 49, 52, 53, 56, 58, 59, 64, 65, 67, 68, 73, 74, 76, 79, 80, 83, 85, 87, 90, 93, 94, 95, 98, 100, 102, 103, 104, 106, 112, 116, 117, 118, 119][i.val]!)

def pointPosition (i : Fin 122) : Fin 61 ⊕ Fin 61 :=
  let j : ℕ := #[61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 0, 1, 72, 73, 74, 75, 2, 3, 4, 76, 5, 6, 7, 8, 9, 77, 10, 78, 79, 80, 11, 81, 12, 82, 13, 14, 83, 84, 85, 15, 16, 86, 17, 18, 87, 19, 88, 20, 89, 21, 22, 90, 91, 23, 24, 92, 25, 93, 94, 26, 27, 28, 29, 95, 96, 30, 97, 98, 31, 32, 33, 34, 99, 100, 35, 101, 36, 37, 102, 103, 38, 39, 104, 40, 105, 41, 106, 42, 43, 107, 44, 45, 108, 109, 110, 46, 47, 111, 48, 112, 49, 113, 114, 115, 50, 116, 51, 52, 53, 54, 55, 117, 56, 57, 58, 118, 119, 120, 121, 59, 60][i.val]!
  if j<61 then .inl (Fin.ofNat 61 j) else .inr (Fin.ofNat 61 (j-61))

def indexing : (Fin 61 ⊕ Fin 61) ≃ Fin 122 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 61,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*121)*(121-1)^60) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 60 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 60 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 60=(2*121)*(121-1)^60 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquaresOpposite


namespace SplitNonsquaresOpposite
def rawWords (i : ℕ) : ℕ := #[130179612083340288, 258648527770668032, 553268129372167168, 1017085601854502912, 970797043159086080, 810530872985365504, 536854951459953664, 1074334312967272448, 924279417643626496, 641550558345093120, 335990908189933687, 639245918041309422, 140871137132839388, 192206432333038520, 1100957499443217287, 482787592491792943, 815872651939569853, 463698377647849850, 942584849437312756, 475820865280303057, 429401406861069083, 923974781320469723, 660727858348277174, 258039243082513260, 782721776261813091, 237928381696079539, 1093098517911575245, 893201332924772149, 412951087518015915, 772486834987452246, 1111289012403349113, 894789778586966501, 655702040939788234, 662260868232998223, 229606203492014750, 440975637025206757, 987830936743913418, 854363434666829135, 464620638713515678, 668278802501975673, 646864944146896299, 125573516936833878, 995823978556264115, 432697943673618125, 835348007798747957, 183530329054566171, 519070861069283547, 1111285539764774326, 1033607128949116780, 351302677758208867, 1045101866646919727, 612950442116787389, 377661603813754, 108864119378196212, 541423580742900689, 31022927570321287, 27257680688402551, 19694917870412014, 20209405370746332, 3823774711761848, 0][i]!
def words (i : Fin 61) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 121]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 61 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 61 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 61, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 61, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(3540:ℤ) := by
  change cubicInteger (fun i : Fin 61 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(3540:ℤ) ∧
    87*(61:ℤ)^3+375*61*(4*61-3)+1000*((wordMatrix words-1)^3).trace-
      1110*121*(61-1)=(20741622:ℤ) ∧ 0≤(20741622:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 61 ⊕ Fin 61 → Fin 122
  | .inl i => Fin.ofNat 122 (#[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 15, 16, 20, 26, 28, 29, 30, 32, 34, 37, 38, 39, 42, 45, 47, 49, 52, 53, 56, 58, 59, 64, 65, 67, 68, 73, 74, 76, 79, 80, 83, 85, 87, 90, 93, 94, 95, 98, 100, 102, 103, 104, 106, 112, 116, 117, 118, 119, 121][i.val]!)
  | .inr i => Fin.ofNat 122 (#[0, 11, 12, 17, 18, 19, 21, 22, 23, 24, 25, 27, 31, 33, 35, 36, 40, 41, 43, 44, 46, 48, 50, 51, 54, 55, 57, 60, 61, 62, 63, 66, 69, 70, 71, 72, 75, 77, 78, 81, 82, 84, 86, 88, 89, 91, 92, 96, 97, 99, 101, 105, 107, 108, 109, 110, 111, 113, 114, 115, 120][i.val]!)

def pointPosition (i : Fin 122) : Fin 61 ⊕ Fin 61 :=
  let j : ℕ := #[61, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 62, 63, 10, 11, 12, 13, 64, 65, 66, 14, 67, 68, 69, 70, 71, 15, 72, 16, 17, 18, 73, 19, 74, 20, 75, 76, 21, 22, 23, 77, 78, 24, 79, 80, 25, 81, 26, 82, 27, 83, 84, 28, 29, 85, 86, 30, 87, 31, 32, 88, 89, 90, 91, 33, 34, 92, 35, 36, 93, 94, 95, 96, 37, 38, 97, 39, 98, 99, 40, 41, 100, 101, 42, 102, 43, 103, 44, 104, 105, 45, 106, 107, 46, 47, 48, 108, 109, 49, 110, 50, 111, 51, 52, 53, 112, 54, 113, 114, 115, 116, 117, 55, 118, 119, 120, 56, 57, 58, 59, 121, 60][i.val]!
  if j<61 then .inl (Fin.ofNat 61 j) else .inr (Fin.ofNat 61 (j-61))

def indexing : (Fin 61 ⊕ Fin 61) ≃ Fin 122 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 61,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*121)*(121-1)^60) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 60 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 60 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 60=(2*121)*(121-1)^60 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquaresOpposite


namespace NonsplitNegativeOpposite
def rawWords (i : ℕ) : ℕ := #[243721781696354932, 521583138673903456, 1025647964238636033, 960015261946504192, 735595089738188801, 358025917293825027, 606443977664404483, 200195820857145344, 850278988631865346, 510229169390735363, 455655036961357934, 97841581033587185, 496983494712296385, 835964994120319372, 476971951344845599, 828493887471944310, 402889196169109399, 767471110739465772, 484749542072285434, 921392712257687671, 274955660108555986, 445265575514498466, 1091823479419603290, 873109486889949920, 178796833709226894, 389356097860953753, 785502775370182967, 267528219394133581, 525169885648753048, 873522219073303382, 698854957308009131, 664636673550137062, 769304063577990863, 393837025343405085, 920042468734520688, 456993323340182443, 910679315699562322, 648420504183925541, 264882270014987292, 957188677568280185, 359373647792403671, 199073936371277361, 406380483110536677, 510455699810504091, 1121115431002385077, 735283240074261160, 797180087928202549, 517928990958321517, 896249842490783927, 635031987690130668, 135171138511950770, 558466014840154438, 1100795446947390, 1589291702980727, 4226170897341929, 3966442229690784, 3620429165079307, 2526991747577751, 2706577575204398, 968351460008284, 0][i]!
def words (i : Fin 61) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181, 181]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 61 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 61 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 61, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 61, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(0:ℤ) := by
  change cubicInteger (fun i : Fin 61 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(0:ℤ) ∧
    87*(61:ℤ)^3+375*61*(4*61-3)+1000*((wordMatrix words-1)^3).trace-
      1110*121*(61-1)=(17201622:ℤ) ∧ 0≤(17201622:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 61 ⊕ Fin 61 → Fin 122
  | .inl i => Fin.ofNat 122 (#[3, 8, 11, 12, 13, 14, 15, 17, 19, 20, 22, 25, 27, 29, 30, 32, 33, 34, 37, 38, 40, 41, 48, 50, 52, 53, 54, 55, 56, 59, 60, 66, 72, 73, 76, 78, 79, 80, 82, 84, 88, 91, 92, 94, 95, 98, 99, 100, 102, 103, 105, 107, 110, 112, 113, 115, 117, 118, 119, 120, 121][i.val]!)
  | .inr i => Fin.ofNat 122 (#[0, 1, 2, 4, 5, 6, 7, 9, 10, 16, 18, 21, 23, 24, 26, 28, 31, 35, 36, 39, 42, 43, 44, 45, 46, 47, 49, 51, 57, 58, 61, 62, 63, 64, 65, 67, 68, 69, 70, 71, 74, 75, 77, 81, 83, 85, 86, 87, 89, 90, 93, 96, 97, 101, 104, 106, 108, 109, 111, 114, 116][i.val]!)

def pointPosition (i : Fin 122) : Fin 61 ⊕ Fin 61 :=
  let j : ℕ := #[61, 62, 63, 0, 64, 65, 66, 67, 1, 68, 69, 2, 3, 4, 5, 6, 70, 7, 71, 8, 9, 72, 10, 73, 74, 11, 75, 12, 76, 13, 14, 77, 15, 16, 17, 78, 79, 18, 19, 80, 20, 21, 81, 82, 83, 84, 85, 86, 22, 87, 23, 88, 24, 25, 26, 27, 28, 89, 90, 29, 30, 91, 92, 93, 94, 95, 31, 96, 97, 98, 99, 100, 32, 33, 101, 102, 34, 103, 35, 36, 37, 104, 38, 105, 39, 106, 107, 108, 40, 109, 110, 41, 42, 111, 43, 44, 112, 113, 45, 46, 47, 114, 48, 49, 115, 50, 116, 51, 117, 118, 52, 119, 53, 54, 120, 55, 121, 56, 57, 58, 59, 60][i.val]!
  if j<61 then .inl (Fin.ofNat 61 j) else .inr (Fin.ofNat 61 (j-61))

def indexing : (Fin 61 ⊕ Fin 61) ≃ Fin 122 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 61,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*121)*(121-1)^60) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 60 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 60 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 60=(2*121)*(121-1)^60 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegativeOpposite

end PaleyBits121
