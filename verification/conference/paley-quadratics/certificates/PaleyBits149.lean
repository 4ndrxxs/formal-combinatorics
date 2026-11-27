import Quantum.Hadamard.ConferenceBitCompletion
open Hadamard.BitTrace Hadamard.DeterminantRatio Matrix
set_option maxHeartbeats 12000000
set_option maxRecDepth 60000
namespace PaleyBits149

def rawFull (i : ℕ) : ℕ := #[271771707175801987860979625893642796133580044, 543543414351603975721959251787285592267160088, 373462982350228010914775518849823616342946865, 33302118347476081300408052974899664494520419, 66604236694952162600816105949799328989040838, 133208473389904325201632211899598657978081676, 266416946779808650403264423799197315956163352, 532833893559617300806528847598394631912326704, 352043940766254661083914710472041695633280097, 704087881532509322167829420944083391266560194, 694551916712038703806515857163419214341747077, 675479987071097467083888729602090860492120843, 637336127789214993638634474479434152792868375, 561048409225450046748125964234120737394363439, 408472972097920152967108943743493906597353567, 103322097842860365405074902762240245003333823, 206644195685720730810149805524480490006667646, 413288391371441461620299611048960980013335292, 112952936389902982711456237373174391835297273, 225905872779805965422912474746348783670594546, 451811745559611930845824949492697567341189092, 189999644766243921162506914260647566491004873, 379999289532487842325013828521295132982009746, 46374732711995744120884672317842697772646181, 92749465423991488241769344635685395545292362, 185498930847982976483538689271370791090584724, 370997861695965952967077378542741582181169448, 28371877038951965405011772360735596170965585, 56743754077903930810023544721471192341931170, 113487508155807861620047089442942384683862340, 226975016311615723240094178885884769367724680, 453950032623231446480188357771769538735449360, 194276218893482952431233730818791509279525409, 388552437786965904862467461637583018559050818, 63481029220951869195791938550418468926728325, 126962058441903738391583877100836937853456650, 253924116883807476783167754201673875706913300, 507848233767614953566335508403347751413826600, 302072621182249966603528032081947934636279889, 604145242364499933207056064163895869272559778, 494666638376019925884969143603044170353746245, 275709430399059911240795302481340772516119179, 551418860798119822481590604962681545032238358, 389213875243259704434038225200615521873103405, 64803904133539468338933465676483475554833499, 129607808267078936677866931352966951109666998, 259215616534157873355733862705933902219333996, 518431233068315746711467725411867804438667992, 323238619783651552893792466098988040685962673, 646477239567303105787584932197976081371925346, 579330632781626271046026879671204594552477381, 445037419210272601562910774617661620913581451, 176450992067565262596678564510575673635789591, 352901984135130525193357129021151347271579182, 705803968270261050386714258042302694543158364, 697984090187542160244285531359857820894943417, 682344334022104379959428077994968073598513523, 651064821691228819389713171265188579005653735, 588505797029477698250283357805629589819934159, 463387747705975455971423730886511611448495007, 213151649058970971413704477048275654705616703, 426303298117941942827408954096551309411233406, 138982749882903945125674923468355050631093501, 277965499765807890251349846936710101262187002, 555930999531615780502699693873420202524374004, 398238152710251620476256403022092836857374697, 82852459067523300423369821319438105523376083, 165704918135046600846739642638876211046752166, 331409836270093201693479285277752422093504332, 662819672540186403386958570555504844187008664, 612015498727392866244774156386262120182644017, 510407151101805791960405328047776672173914723, 307190455850631643391667671370805776156456135, 614380911701263286783335342741611552312912270, 515137977049546633037527700758475536434451229, 316652107746113325545912416792203504677529147, 633304215492226651091824833584407009355058294, 552984584631473361654506682444066450518743277, 392345322909966782779870380163385332846113243, 71066799466953625030597775602023097500853175, 142133598933907250061195551204046195001706350, 284267197867814500122391102408092390003412700, 568534395735629000244782204816184780006825400, 423444945118278059960421424907621991822277489, 133266043883576179391699865090496415453181667, 266532087767152358783399730180992830906363334, 533064175534304717566799460361985661812726668, 352504504715629494604455935999223755434080025, 705009009431258989208911871998447510868160050, 696394172509538037888680759272147453544946789, 679164498666096135248218533819547338898520267, 644705150979212329967294082914347109605667223, 575786455605444719405445181103946651019961135, 437949064857909498281747377483145733848548959, 162274283362839056034351770241543899505724607, 324548566725678112068703540483087799011449214, 649097133451356224137407080966175598022898428, 584570420549732507745671177207603627854423545, 455516994746485074962199369690459687517473779, 197410143139990209395255754656171806843574247, 394820286279980418790511509312343613687148494, 76016726206980897051880033899939659182923677, 152033452413961794103760067799879318365847354, 304066904827923588207520135599758636731694708, 608133809655847176415040271199517273463389416, 502643772958714412300937557674286978735405521, 291663699564448884072732130623826389279437731, 583327399128897768145464261247652778558875462, 453030951904815595761785537770557988926377613, 192438057456651250994428090816368409661381915, 384876114913302501988856181632736819322763830, 56128383473625063448569378540726070454154349, 112256766947250126897138757081452140908308698, 224513533894500253794277514162904281816617396, 449027067789000507588555028325808563633234792, 184430289225021074647967071926869559075096273, 368860578450042149295934143853739118150192546, 24097310547104358062725302982730668109011781, 48194621094208716125450605965461336218023562, 96389242188417432250901211930922672436047124, 192778484376834864501802423861845344872094248, 385556968753669729003604847723690689744188496, 57490091154359517478066710722633811297003681, 114980182308719034956133421445267622594007362, 229960364617438069912266842890535245188014724, 459920729234876139824533685781070490376029448, 206217612116772339119924386837393412560685585, 412435224233544678239848773674786825121371170, 111246602114109415950554562624826082051369029, 222493204228218831901109125249652164102738058, 444986408456437663802218250499304328205476116, 176348970559895387075293516273861088219578921, 352697941119790774150587032547722176439157842, 705395882239581548301174065095444352878315684, 697167918126183156073205145466141137565258057, 680711989899386371617267306207534706939142803, 647800133445792802705391627690321845686912295, 581976420538605664881640270655896123182451279, 450328994724231389234137556587044678173529247, 187034143095482837939132128449341788155685183, 374068286190965675878264256898683576311370366, 34512726028951411227385529072619584431367421, 69025452057902822454771058145239168862734842, 138050904115805644909542116290478337725469684, 276101808231611289819084232580956675450939368, 552203616463222579638168465161913350901878736, 390783386573465218747193945599079133612384161, 67942926793950496965244906473410699033395011, 135885853587900993930489812946821398066790022, 0][i]!
def fullRows (i : Fin 150) : ℕ := rawFull i.val

private theorem fullSymmetric : (wordMatrix fullRows).IsSymm := by
  have h : ∀ i j : Fin 150, sign (fullRows i) j.val=sign (fullRows j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem fullDiagonal : ∀ i : Fin 150, sign (fullRows i) i.val=1 := by decide +kernel
private theorem lower0 : (lowerRow 150 rawFull) 0=true := by decide +kernel
private theorem lower1 : (lowerRow 150 rawFull) 1=true := by decide +kernel
private theorem lower2 : (lowerRow 150 rawFull) 2=true := by decide +kernel
private theorem lower3 : (lowerRow 150 rawFull) 3=true := by decide +kernel
private theorem lower4 : (lowerRow 150 rawFull) 4=true := by decide +kernel
private theorem lower5 : (lowerRow 150 rawFull) 5=true := by decide +kernel
private theorem lower6 : (lowerRow 150 rawFull) 6=true := by decide +kernel
private theorem lower7 : (lowerRow 150 rawFull) 7=true := by decide +kernel
private theorem lower8 : (lowerRow 150 rawFull) 8=true := by decide +kernel
private theorem lower9 : (lowerRow 150 rawFull) 9=true := by decide +kernel
private theorem lower10 : (lowerRow 150 rawFull) 10=true := by decide +kernel
private theorem lower11 : (lowerRow 150 rawFull) 11=true := by decide +kernel
private theorem lower12 : (lowerRow 150 rawFull) 12=true := by decide +kernel
private theorem lower13 : (lowerRow 150 rawFull) 13=true := by decide +kernel
private theorem lower14 : (lowerRow 150 rawFull) 14=true := by decide +kernel
private theorem lower15 : (lowerRow 150 rawFull) 15=true := by decide +kernel
private theorem lower16 : (lowerRow 150 rawFull) 16=true := by decide +kernel
private theorem lower17 : (lowerRow 150 rawFull) 17=true := by decide +kernel
private theorem lower18 : (lowerRow 150 rawFull) 18=true := by decide +kernel
private theorem lower19 : (lowerRow 150 rawFull) 19=true := by decide +kernel
private theorem lower20 : (lowerRow 150 rawFull) 20=true := by decide +kernel
private theorem lower21 : (lowerRow 150 rawFull) 21=true := by decide +kernel
private theorem lower22 : (lowerRow 150 rawFull) 22=true := by decide +kernel
private theorem lower23 : (lowerRow 150 rawFull) 23=true := by decide +kernel
private theorem lower24 : (lowerRow 150 rawFull) 24=true := by decide +kernel
private theorem lower25 : (lowerRow 150 rawFull) 25=true := by decide +kernel
private theorem lower26 : (lowerRow 150 rawFull) 26=true := by decide +kernel
private theorem lower27 : (lowerRow 150 rawFull) 27=true := by decide +kernel
private theorem lower28 : (lowerRow 150 rawFull) 28=true := by decide +kernel
private theorem lower29 : (lowerRow 150 rawFull) 29=true := by decide +kernel
private theorem lower30 : (lowerRow 150 rawFull) 30=true := by decide +kernel
private theorem lower31 : (lowerRow 150 rawFull) 31=true := by decide +kernel
private theorem lower32 : (lowerRow 150 rawFull) 32=true := by decide +kernel
private theorem lower33 : (lowerRow 150 rawFull) 33=true := by decide +kernel
private theorem lower34 : (lowerRow 150 rawFull) 34=true := by decide +kernel
private theorem lower35 : (lowerRow 150 rawFull) 35=true := by decide +kernel
private theorem lower36 : (lowerRow 150 rawFull) 36=true := by decide +kernel
private theorem lower37 : (lowerRow 150 rawFull) 37=true := by decide +kernel
private theorem lower38 : (lowerRow 150 rawFull) 38=true := by decide +kernel
private theorem lower39 : (lowerRow 150 rawFull) 39=true := by decide +kernel
private theorem lower40 : (lowerRow 150 rawFull) 40=true := by decide +kernel
private theorem lower41 : (lowerRow 150 rawFull) 41=true := by decide +kernel
private theorem lower42 : (lowerRow 150 rawFull) 42=true := by decide +kernel
private theorem lower43 : (lowerRow 150 rawFull) 43=true := by decide +kernel
private theorem lower44 : (lowerRow 150 rawFull) 44=true := by decide +kernel
private theorem lower45 : (lowerRow 150 rawFull) 45=true := by decide +kernel
private theorem lower46 : (lowerRow 150 rawFull) 46=true := by decide +kernel
private theorem lower47 : (lowerRow 150 rawFull) 47=true := by decide +kernel
private theorem lower48 : (lowerRow 150 rawFull) 48=true := by decide +kernel
private theorem lower49 : (lowerRow 150 rawFull) 49=true := by decide +kernel
private theorem lower50 : (lowerRow 150 rawFull) 50=true := by decide +kernel
private theorem lower51 : (lowerRow 150 rawFull) 51=true := by decide +kernel
private theorem lower52 : (lowerRow 150 rawFull) 52=true := by decide +kernel
private theorem lower53 : (lowerRow 150 rawFull) 53=true := by decide +kernel
private theorem lower54 : (lowerRow 150 rawFull) 54=true := by decide +kernel
private theorem lower55 : (lowerRow 150 rawFull) 55=true := by decide +kernel
private theorem lower56 : (lowerRow 150 rawFull) 56=true := by decide +kernel
private theorem lower57 : (lowerRow 150 rawFull) 57=true := by decide +kernel
private theorem lower58 : (lowerRow 150 rawFull) 58=true := by decide +kernel
private theorem lower59 : (lowerRow 150 rawFull) 59=true := by decide +kernel
private theorem lower60 : (lowerRow 150 rawFull) 60=true := by decide +kernel
private theorem lower61 : (lowerRow 150 rawFull) 61=true := by decide +kernel
private theorem lower62 : (lowerRow 150 rawFull) 62=true := by decide +kernel
private theorem lower63 : (lowerRow 150 rawFull) 63=true := by decide +kernel
private theorem lower64 : (lowerRow 150 rawFull) 64=true := by decide +kernel
private theorem lower65 : (lowerRow 150 rawFull) 65=true := by decide +kernel
private theorem lower66 : (lowerRow 150 rawFull) 66=true := by decide +kernel
private theorem lower67 : (lowerRow 150 rawFull) 67=true := by decide +kernel
private theorem lower68 : (lowerRow 150 rawFull) 68=true := by decide +kernel
private theorem lower69 : (lowerRow 150 rawFull) 69=true := by decide +kernel
private theorem lower70 : (lowerRow 150 rawFull) 70=true := by decide +kernel
private theorem lower71 : (lowerRow 150 rawFull) 71=true := by decide +kernel
private theorem lower72 : (lowerRow 150 rawFull) 72=true := by decide +kernel
private theorem lower73 : (lowerRow 150 rawFull) 73=true := by decide +kernel
private theorem lower74 : (lowerRow 150 rawFull) 74=true := by decide +kernel
private theorem lower75 : (lowerRow 150 rawFull) 75=true := by decide +kernel
private theorem lower76 : (lowerRow 150 rawFull) 76=true := by decide +kernel
private theorem lower77 : (lowerRow 150 rawFull) 77=true := by decide +kernel
private theorem lower78 : (lowerRow 150 rawFull) 78=true := by decide +kernel
private theorem lower79 : (lowerRow 150 rawFull) 79=true := by decide +kernel
private theorem lower80 : (lowerRow 150 rawFull) 80=true := by decide +kernel
private theorem lower81 : (lowerRow 150 rawFull) 81=true := by decide +kernel
private theorem lower82 : (lowerRow 150 rawFull) 82=true := by decide +kernel
private theorem lower83 : (lowerRow 150 rawFull) 83=true := by decide +kernel
private theorem lower84 : (lowerRow 150 rawFull) 84=true := by decide +kernel
private theorem lower85 : (lowerRow 150 rawFull) 85=true := by decide +kernel
private theorem lower86 : (lowerRow 150 rawFull) 86=true := by decide +kernel
private theorem lower87 : (lowerRow 150 rawFull) 87=true := by decide +kernel
private theorem lower88 : (lowerRow 150 rawFull) 88=true := by decide +kernel
private theorem lower89 : (lowerRow 150 rawFull) 89=true := by decide +kernel
private theorem lower90 : (lowerRow 150 rawFull) 90=true := by decide +kernel
private theorem lower91 : (lowerRow 150 rawFull) 91=true := by decide +kernel
private theorem lower92 : (lowerRow 150 rawFull) 92=true := by decide +kernel
private theorem lower93 : (lowerRow 150 rawFull) 93=true := by decide +kernel
private theorem lower94 : (lowerRow 150 rawFull) 94=true := by decide +kernel
private theorem lower95 : (lowerRow 150 rawFull) 95=true := by decide +kernel
private theorem lower96 : (lowerRow 150 rawFull) 96=true := by decide +kernel
private theorem lower97 : (lowerRow 150 rawFull) 97=true := by decide +kernel
private theorem lower98 : (lowerRow 150 rawFull) 98=true := by decide +kernel
private theorem lower99 : (lowerRow 150 rawFull) 99=true := by decide +kernel
private theorem lower100 : (lowerRow 150 rawFull) 100=true := by decide +kernel
private theorem lower101 : (lowerRow 150 rawFull) 101=true := by decide +kernel
private theorem lower102 : (lowerRow 150 rawFull) 102=true := by decide +kernel
private theorem lower103 : (lowerRow 150 rawFull) 103=true := by decide +kernel
private theorem lower104 : (lowerRow 150 rawFull) 104=true := by decide +kernel
private theorem lower105 : (lowerRow 150 rawFull) 105=true := by decide +kernel
private theorem lower106 : (lowerRow 150 rawFull) 106=true := by decide +kernel
private theorem lower107 : (lowerRow 150 rawFull) 107=true := by decide +kernel
private theorem lower108 : (lowerRow 150 rawFull) 108=true := by decide +kernel
private theorem lower109 : (lowerRow 150 rawFull) 109=true := by decide +kernel
private theorem lower110 : (lowerRow 150 rawFull) 110=true := by decide +kernel
private theorem lower111 : (lowerRow 150 rawFull) 111=true := by decide +kernel
private theorem lower112 : (lowerRow 150 rawFull) 112=true := by decide +kernel
private theorem lower113 : (lowerRow 150 rawFull) 113=true := by decide +kernel
private theorem lower114 : (lowerRow 150 rawFull) 114=true := by decide +kernel
private theorem lower115 : (lowerRow 150 rawFull) 115=true := by decide +kernel
private theorem lower116 : (lowerRow 150 rawFull) 116=true := by decide +kernel
private theorem lower117 : (lowerRow 150 rawFull) 117=true := by decide +kernel
private theorem lower118 : (lowerRow 150 rawFull) 118=true := by decide +kernel
private theorem lower119 : (lowerRow 150 rawFull) 119=true := by decide +kernel
private theorem lower120 : (lowerRow 150 rawFull) 120=true := by decide +kernel
private theorem lower121 : (lowerRow 150 rawFull) 121=true := by decide +kernel
private theorem lower122 : (lowerRow 150 rawFull) 122=true := by decide +kernel
private theorem lower123 : (lowerRow 150 rawFull) 123=true := by decide +kernel
private theorem lower124 : (lowerRow 150 rawFull) 124=true := by decide +kernel
private theorem lower125 : (lowerRow 150 rawFull) 125=true := by decide +kernel
private theorem lower126 : (lowerRow 150 rawFull) 126=true := by decide +kernel
private theorem lower127 : (lowerRow 150 rawFull) 127=true := by decide +kernel
private theorem lower128 : (lowerRow 150 rawFull) 128=true := by decide +kernel
private theorem lower129 : (lowerRow 150 rawFull) 129=true := by decide +kernel
private theorem lower130 : (lowerRow 150 rawFull) 130=true := by decide +kernel
private theorem lower131 : (lowerRow 150 rawFull) 131=true := by decide +kernel
private theorem lower132 : (lowerRow 150 rawFull) 132=true := by decide +kernel
private theorem lower133 : (lowerRow 150 rawFull) 133=true := by decide +kernel
private theorem lower134 : (lowerRow 150 rawFull) 134=true := by decide +kernel
private theorem lower135 : (lowerRow 150 rawFull) 135=true := by decide +kernel
private theorem lower136 : (lowerRow 150 rawFull) 136=true := by decide +kernel
private theorem lower137 : (lowerRow 150 rawFull) 137=true := by decide +kernel
private theorem lower138 : (lowerRow 150 rawFull) 138=true := by decide +kernel
private theorem lower139 : (lowerRow 150 rawFull) 139=true := by decide +kernel
private theorem lower140 : (lowerRow 150 rawFull) 140=true := by decide +kernel
private theorem lower141 : (lowerRow 150 rawFull) 141=true := by decide +kernel
private theorem lower142 : (lowerRow 150 rawFull) 142=true := by decide +kernel
private theorem lower143 : (lowerRow 150 rawFull) 143=true := by decide +kernel
private theorem lower144 : (lowerRow 150 rawFull) 144=true := by decide +kernel
private theorem lower145 : (lowerRow 150 rawFull) 145=true := by decide +kernel
private theorem lower146 : (lowerRow 150 rawFull) 146=true := by decide +kernel
private theorem lower147 : (lowerRow 150 rawFull) 147=true := by decide +kernel
private theorem lower148 : (lowerRow 150 rawFull) 148=true := by decide +kernel
private theorem lower149 : (lowerRow 150 rawFull) 149=true := by decide +kernel
private theorem lowerChecked : allBelow 150 (lowerRow 150 rawFull)=true := by
  have h : allBelow 0 (lowerRow 150 rawFull)=true := rfl
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
  have h := allBelow_step h lower138
  have h := allBelow_step h lower139
  have h := allBelow_step h lower140
  have h := allBelow_step h lower141
  have h := allBelow_step h lower142
  have h := allBelow_step h lower143
  have h := allBelow_step h lower144
  have h := allBelow_step h lower145
  have h := allBelow_step h lower146
  have h := allBelow_step h lower147
  have h := allBelow_step h lower148
  have h := allBelow_step h lower149
  exact h

private theorem fullPairs : ∀ i j : Fin 150, i≠j →
    correlation 150 (fullRows i) (fullRows j)=2*sign (fullRows i) j.val :=
  correlations_of_lower rawFull fullSymmetric lowerChecked


namespace SplitSquares
def rawWords (i : ℕ) : ℕ := #[0, 20865805806129156496068, 13799638215441552518066, 9168740966302071441312, 18450252067533052516292, 36935237869700041060172, 36013420561736958877490, 6231602300027138462238, 30854745655783726753404, 9551626823551859755518, 20117831225545955641720, 24003672836217050379878, 566357889497055643858, 2147291506114041514276, 21433916086961265807496, 12167801720308475782570, 5409466812856124326800, 9509066323097545117664, 20936663655047731185540, 25049038637588179987986, 8186245023682326445314, 15784421302072372688964, 32011562355246836578952, 34202845309585269846186, 22331940238051944927750, 8456472066349665753134, 17542504383601700545048, 33736099793898533639284, 23491679896134009276762, 18555584330412130976330, 35912204798386963745940, 34112597905156507501918, 2116677796610596744766, 22550977229760753718524, 15862333187262449800170, 13981416506290329531856, 26634538783235911312228, 35988573362165575788962, 20536815710702187116446, 11445820258015066176602, 3446390135236001233652, 25911443255997021715884, 18643038796263825598002, 36732821333963338929376, 36193089403078394759630, 12156645858393009632670, 24278553218783763659644, 26733003474083844975090, 13625943699159991628366, 7163371725109523773148, 34265379169626342778168, 28419376718005885703634, 25105616140280065181646, 5126507555806816874038, 10070846934391243103916, 19106298423744386186712, 21384876464374404447018, 9999945357377265858402, 2343964930438017051652, 2880158107301166697032, 25279414730930296167572, 5028499167473117919506, 10792638390151742907104, 22156916696663900084096, 30230026500172458740362, 9022151554286478595106, 37650897422395544254980, 18416660190810265637142, 35505240094835955775656, 22717472090078261354590, 15040155185230048404670, 10598304041176216420732, 1737468151410185537784, 22970973913261508035444, 10432902903064578248034][i]!
def words (i : Fin 75) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[149, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 75 rawWords i=rowTotals i)

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
private theorem row69 : rowAgrees 69=true := by decide +kernel
private theorem row70 : rowAgrees 70=true := by decide +kernel
private theorem row71 : rowAgrees 71=true := by decide +kernel
private theorem row72 : rowAgrees 72=true := by decide +kernel
private theorem row73 : rowAgrees 73=true := by decide +kernel
private theorem row74 : rowAgrees 74=true := by decide +kernel
private theorem rowChecked : allBelow 75 rowAgrees=true := by
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
  have h := allBelow_step h row69
  have h := allBelow_step h row70
  have h := allBelow_step h row71
  have h := allBelow_step h row72
  have h := allBelow_step h row73
  have h := allBelow_step h row74
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 75, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 75, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-1998:ℤ) := by
  change cubicInteger (fun i : Fin 75 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-1998:ℤ) ∧
    87*(75:ℤ)^3+375*75*(4*75-3)+1000*((wordMatrix words-1)^3).trace-
      1110*149*(75-1)=(30819390:ℤ) ∧ 0≤(30819390:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 75 ⊕ Fin 75 → Fin 150
  | .inl i => Fin.ofNat 150 (#[0, 1, 4, 5, 6, 7, 9, 16, 17, 19, 20, 22, 24, 25, 26, 28, 29, 30, 31, 33, 35, 36, 37, 39, 42, 45, 46, 47, 49, 53, 54, 61, 63, 64, 67, 68, 69, 73, 76, 80, 81, 82, 85, 86, 88, 95, 96, 100, 102, 103, 104, 107, 110, 112, 113, 114, 116, 118, 119, 120, 121, 123, 124, 125, 127, 129, 130, 132, 133, 140, 142, 143, 144, 145, 148][i.val]!)
  | .inr i => Fin.ofNat 150 (#[2, 3, 8, 10, 11, 12, 13, 14, 15, 18, 21, 23, 27, 32, 34, 38, 40, 41, 43, 44, 48, 50, 51, 52, 55, 56, 57, 58, 59, 60, 62, 65, 66, 70, 71, 72, 74, 75, 77, 78, 79, 83, 84, 87, 89, 90, 91, 92, 93, 94, 97, 98, 99, 101, 105, 106, 108, 109, 111, 115, 117, 122, 126, 128, 131, 134, 135, 136, 137, 138, 139, 141, 146, 147, 149][i.val]!)

def pointPosition (i : Fin 150) : Fin 75 ⊕ Fin 75 :=
  let j : ℕ := #[0, 1, 75, 76, 2, 3, 4, 5, 77, 6, 78, 79, 80, 81, 82, 83, 7, 8, 84, 9, 10, 85, 11, 86, 12, 13, 14, 87, 15, 16, 17, 18, 88, 19, 89, 20, 21, 22, 90, 23, 91, 92, 24, 93, 94, 25, 26, 27, 95, 28, 96, 97, 98, 29, 30, 99, 100, 101, 102, 103, 104, 31, 105, 32, 33, 106, 107, 34, 35, 36, 108, 109, 110, 37, 111, 112, 38, 113, 114, 115, 39, 40, 41, 116, 117, 42, 43, 118, 44, 119, 120, 121, 122, 123, 124, 45, 46, 125, 126, 127, 47, 128, 48, 49, 50, 129, 130, 51, 131, 132, 52, 133, 53, 54, 55, 134, 56, 135, 57, 58, 59, 60, 136, 61, 62, 63, 137, 64, 138, 65, 66, 139, 67, 68, 140, 141, 142, 143, 144, 145, 69, 146, 70, 71, 72, 73, 147, 148, 74, 149][i.val]!
  if j<75 then .inl (Fin.ofNat 75 j) else .inr (Fin.ofNat 75 (j-75))

def indexing : (Fin 75 ⊕ Fin 75) ≃ Fin 150 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 75,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*149)*(149-1)^74) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 74 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 74 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 74=(2*149)*(149-1)^74 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquares


namespace SplitNonsquares
def rawWords (i : ℕ) : ℕ := #[37778931862957161709566, 9171087394386821682129, 8966148752693413023649, 31067053404571222285361, 34534497658002675342539, 31320757722972687030669, 29591883415343850337043, 26144335364473747585591, 338660464594285518951, 14767174668324924634311, 9606055121454096468509, 20380964563582551381181, 1317887839343868218107, 1654008676321958757313, 25435546502075342556449, 2576754768749154818211, 31792251388289815556641, 18414010166899362062475, 32154511168943498540293, 5846966710644548976679, 7071256332226280085589, 37387204721487619795225, 26661874653330862732371, 6160016152134142591165, 17025048669438227219819, 31963141547014370548581, 30987876375465566209737, 33636978227282500424067, 24667291873591923705631, 11625784185575617949231, 23297829368528849862751, 17512986907905298271607, 3439716829195114982301, 6860248372489287685945, 24087559620040531208185, 15123778057545058368481, 30240059873664971295699, 12229275182058149418831, 33915785327214355871381, 22380229068636337778279, 2319742208685487930573, 9415410011570648201611, 8535176555986554617065, 17068479631581295601105, 32669397793110639536861, 36008074149389157136243, 34373981727293431858917, 35676428109217681820107, 19342673413455000039311, 5719337558752680066839, 11468653327722695217719, 25569395244208130323869, 18005121196273771182889, 21894864533294386424411, 7256214062887457273215, 12427489474104930250729, 29517535327989322413001, 9643728544045749342007, 23914581411409010738813, 1268680422545810714071, 20395239124334962236689, 1385065254569307255915, 1107840555074279004577, 28133204659194416393761, 18053653108271823040675, 16622978426384219099397, 29270949537194501345357, 30112169821752941978753, 31983489050548603791643, 21485894193518873362983, 14641606682384516151383, 24561907497740722995375, 3606652291555631186583, 1752698791278292698745, 3478736272637999532281][i]!
def words (i : Fin 75) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[297, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 75 rawWords i=rowTotals i)

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
private theorem row69 : rowAgrees 69=true := by decide +kernel
private theorem row70 : rowAgrees 70=true := by decide +kernel
private theorem row71 : rowAgrees 71=true := by decide +kernel
private theorem row72 : rowAgrees 72=true := by decide +kernel
private theorem row73 : rowAgrees 73=true := by decide +kernel
private theorem row74 : rowAgrees 74=true := by decide +kernel
private theorem rowChecked : allBelow 75 rowAgrees=true := by
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
  have h := allBelow_step h row69
  have h := allBelow_step h row70
  have h := allBelow_step h row71
  have h := allBelow_step h row72
  have h := allBelow_step h row73
  have h := allBelow_step h row74
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 75, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 75, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(1998:ℤ) := by
  change cubicInteger (fun i : Fin 75 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(1998:ℤ) ∧
    87*(75:ℤ)^3+375*75*(4*75-3)+1000*((wordMatrix words-1)^3).trace-
      1110*149*(75-1)=(34815390:ℤ) ∧ 0≤(34815390:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 75 ⊕ Fin 75 → Fin 150
  | .inl i => Fin.ofNat 150 (#[0, 2, 3, 8, 10, 11, 12, 13, 14, 15, 18, 21, 23, 27, 32, 34, 38, 40, 41, 43, 44, 48, 50, 51, 52, 55, 56, 57, 58, 59, 60, 62, 65, 66, 70, 71, 72, 74, 75, 77, 78, 79, 83, 84, 87, 89, 90, 91, 92, 93, 94, 97, 98, 99, 101, 105, 106, 108, 109, 111, 115, 117, 122, 126, 128, 131, 134, 135, 136, 137, 138, 139, 141, 146, 147][i.val]!)
  | .inr i => Fin.ofNat 150 (#[1, 4, 5, 6, 7, 9, 16, 17, 19, 20, 22, 24, 25, 26, 28, 29, 30, 31, 33, 35, 36, 37, 39, 42, 45, 46, 47, 49, 53, 54, 61, 63, 64, 67, 68, 69, 73, 76, 80, 81, 82, 85, 86, 88, 95, 96, 100, 102, 103, 104, 107, 110, 112, 113, 114, 116, 118, 119, 120, 121, 123, 124, 125, 127, 129, 130, 132, 133, 140, 142, 143, 144, 145, 148, 149][i.val]!)

def pointPosition (i : Fin 150) : Fin 75 ⊕ Fin 75 :=
  let j : ℕ := #[0, 75, 1, 2, 76, 77, 78, 79, 3, 80, 4, 5, 6, 7, 8, 9, 81, 82, 10, 83, 84, 11, 85, 12, 86, 87, 88, 13, 89, 90, 91, 92, 14, 93, 15, 94, 95, 96, 16, 97, 17, 18, 98, 19, 20, 99, 100, 101, 21, 102, 22, 23, 24, 103, 104, 25, 26, 27, 28, 29, 30, 105, 31, 106, 107, 32, 33, 108, 109, 110, 34, 35, 36, 111, 37, 38, 112, 39, 40, 41, 113, 114, 115, 42, 43, 116, 117, 44, 118, 45, 46, 47, 48, 49, 50, 119, 120, 51, 52, 53, 121, 54, 122, 123, 124, 55, 56, 125, 57, 58, 126, 59, 127, 128, 129, 60, 130, 61, 131, 132, 133, 134, 62, 135, 136, 137, 63, 138, 64, 139, 140, 65, 141, 142, 66, 67, 68, 69, 70, 71, 143, 72, 144, 145, 146, 147, 73, 74, 148, 149][i.val]!
  if j<75 then .inl (Fin.ofNat 75 j) else .inr (Fin.ofNat 75 (j-75))

def indexing : (Fin 75 ⊕ Fin 75) ≃ Fin 150 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 75,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*149)*(149-1)^74) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 74 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 74 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 74=(2*149)*(149-1)^74 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquares


namespace NonsplitNegative
def rawWords (i : ℕ) : ℕ := #[20597158141654342079394, 4625688526149972471693, 13890444986818834378258, 9335874701229509857058, 37292599279446389267556, 35936792892423616550041, 36013708567940738357264, 34403606185504880079139, 25102870170641974359691, 3567804927661570648335, 23654688383579666497854, 12206410881178685383262, 21418748189466471367153, 19746641321377858620294, 3642054025504059623208, 4940218280230009253717, 5400075736487440080434, 1069675909896935644580, 23066638316993625790537, 6299226936109240038032, 12763308998595208172803, 26444827341928014080533, 11057008035512883472691, 19918865840856718098497, 6772168573946499638347, 13257852743846232807573, 23536387577410955135608, 18385889432576153094561, 36668194947813750769046, 33481618922014707554829, 29734978561139558992563, 2624617400712584017511, 11803470262248463667359, 20784637114495835251516, 22956510582803957831038, 8125483398549994126329, 31708618489685385194994, 13183721941644608182105, 7942837716960586814773, 23525404081780542895830, 9404760647817855099353, 37384784573087813854130, 17935721540411429475938, 35722126534309055021029, 30230923384887894222609, 22821228948744646393127, 14268753614871912058511, 31176527876740207950910, 1641866795080225706621, 8949323810465274494450, 12132161742027901032245, 24244728303664926003049, 594713800483024879299, 22606073315373042003621, 11906234752208335575451, 19085896692795791801557, 2744249716350577928872, 5340957373989738046579, 11133303221655562353088, 22573499377293449744968, 12678133011062455221513, 6161858261866562677296, 28870408751619296388930, 4575910649438531717395, 36088633921146707434132, 36750276092645067760650, 33231323751997359351857, 24035288303841658974379, 20231828444678419253551, 2390157734419010887774, 7427994936621946127263, 11282014344871484349054, 20349211573420307351032, 21385848603931059423476, 14744184154616114722289][i]!
def words (i : Fin 75) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 75 rawWords i=rowTotals i)

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
private theorem row69 : rowAgrees 69=true := by decide +kernel
private theorem row70 : rowAgrees 70=true := by decide +kernel
private theorem row71 : rowAgrees 71=true := by decide +kernel
private theorem row72 : rowAgrees 72=true := by decide +kernel
private theorem row73 : rowAgrees 73=true := by decide +kernel
private theorem row74 : rowAgrees 74=true := by decide +kernel
private theorem rowChecked : allBelow 75 rowAgrees=true := by
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
  have h := allBelow_step h row69
  have h := allBelow_step h row70
  have h := allBelow_step h row71
  have h := allBelow_step h row72
  have h := allBelow_step h row73
  have h := allBelow_step h row74
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 75, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 75, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-5250:ℤ) := by
  change cubicInteger (fun i : Fin 75 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-5250:ℤ) ∧
    87*(75:ℤ)^3+375*75*(4*75-3)+1000*((wordMatrix words-1)^3).trace-
      1110*149*(75-1)=(27567390:ℤ) ∧ 0≤(27567390:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 75 ⊕ Fin 75 → Fin 150
  | .inl i => Fin.ofNat 150 (#[0, 2, 4, 5, 6, 8, 9, 10, 13, 15, 16, 17, 21, 25, 26, 27, 29, 31, 32, 33, 34, 38, 40, 41, 43, 44, 49, 51, 54, 55, 58, 59, 62, 63, 64, 65, 68, 71, 78, 81, 84, 85, 86, 87, 90, 91, 94, 95, 98, 100, 105, 106, 108, 109, 111, 115, 116, 117, 118, 120, 122, 123, 124, 128, 132, 133, 134, 136, 139, 140, 141, 143, 144, 145, 147][i.val]!)
  | .inr i => Fin.ofNat 150 (#[1, 3, 7, 11, 12, 14, 18, 19, 20, 22, 23, 24, 28, 30, 35, 36, 37, 39, 42, 45, 46, 47, 48, 50, 52, 53, 56, 57, 60, 61, 66, 67, 69, 70, 72, 73, 74, 75, 76, 77, 79, 80, 82, 83, 88, 89, 92, 93, 96, 97, 99, 101, 102, 103, 104, 107, 110, 112, 113, 114, 119, 121, 125, 126, 127, 129, 130, 131, 135, 137, 138, 142, 146, 148, 149][i.val]!)

def pointPosition (i : Fin 150) : Fin 75 ⊕ Fin 75 :=
  let j : ℕ := #[0, 75, 1, 76, 2, 3, 4, 77, 5, 6, 7, 78, 79, 8, 80, 9, 10, 11, 81, 82, 83, 12, 84, 85, 86, 13, 14, 15, 87, 16, 88, 17, 18, 19, 20, 89, 90, 91, 21, 92, 22, 23, 93, 24, 25, 94, 95, 96, 97, 26, 98, 27, 99, 100, 28, 29, 101, 102, 30, 31, 103, 104, 32, 33, 34, 35, 105, 106, 36, 107, 108, 37, 109, 110, 111, 112, 113, 114, 38, 115, 116, 39, 117, 118, 40, 41, 42, 43, 119, 120, 44, 45, 121, 122, 46, 47, 123, 124, 48, 125, 49, 126, 127, 128, 129, 50, 51, 130, 52, 53, 131, 54, 132, 133, 134, 55, 56, 57, 58, 135, 59, 136, 60, 61, 62, 137, 138, 139, 63, 140, 141, 142, 64, 65, 66, 143, 67, 144, 145, 68, 69, 70, 146, 71, 72, 73, 147, 74, 148, 149][i.val]!
  if j<75 then .inl (Fin.ofNat 75 j) else .inr (Fin.ofNat 75 (j-75))

def indexing : (Fin 75 ⊕ Fin 75) ≃ Fin 150 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 75,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*149)*(149-1)^74) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 74 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 74 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 74=(2*149)*(149-1)^74 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegative


namespace SplitSquaresOpposite
def rawWords (i : ℕ) : ℕ := #[4585543697193410841064, 4483074376346706511824, 15533526702285611142680, 17267248829001337671269, 15660378861486343515334, 14795941707671925168521, 13072167682236873792795, 169330232297142759475, 7383587334162462317155, 4803027560727048234254, 10190482281791275690590, 658943919671934109053, 827004338160979378656, 12717773251037671278224, 1288377384374577409105, 15896125694144907778320, 9207005083449681031237, 16077255584471749270146, 2923483355322274488339, 3535628166113140042794, 18693602360743809897612, 13330937326665431366185, 3080008076067071295582, 8512524334719113609909, 15981570773507185274290, 15493938187732783104868, 16818489113641250212033, 12333645936795961852815, 5812892092787808974615, 11648914684264424931375, 8756493453952649135803, 1719858414597557491150, 3430124186244643842972, 12043779810020265604092, 7561889028772529184240, 15120029936832485647849, 6114637591029074709415, 16957892663607177935690, 11190114534318168889139, 1159871104342743965286, 4707705005785324100805, 4267588277993277308532, 8534239815790647800552, 16334698896555319768430, 18004037074694578568121, 17186990863646715929458, 17838214054608840910053, 9671336706727500019655, 2859668779376340033419, 5734326663861347608859, 12784697622104065161934, 9002560598136885591444, 10947432266647193212205, 3628107031443728636607, 6213744737052465125364, 14758767663994661206500, 4821864272022874671003, 11957290705704505369406, 634340211272905357035, 10197619562167481118344, 692532627284653627957, 553920277537139502288, 14066602329597208196880, 9026826554135911520337, 8311489213192109549698, 14635474768597250672678, 15056084910876470989376, 15991744525274301895821, 10742947096759436681491, 7320803341192258075691, 12280953748870361497687, 1803326145777815593291, 876349395639146349372, 1739368136318999766140, 0][i]!
def words (i : Fin 75) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 297]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 75 rawWords i=rowTotals i)

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
private theorem row69 : rowAgrees 69=true := by decide +kernel
private theorem row70 : rowAgrees 70=true := by decide +kernel
private theorem row71 : rowAgrees 71=true := by decide +kernel
private theorem row72 : rowAgrees 72=true := by decide +kernel
private theorem row73 : rowAgrees 73=true := by decide +kernel
private theorem row74 : rowAgrees 74=true := by decide +kernel
private theorem rowChecked : allBelow 75 rowAgrees=true := by
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
  have h := allBelow_step h row69
  have h := allBelow_step h row70
  have h := allBelow_step h row71
  have h := allBelow_step h row72
  have h := allBelow_step h row73
  have h := allBelow_step h row74
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 75, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 75, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(1998:ℤ) := by
  change cubicInteger (fun i : Fin 75 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(1998:ℤ) ∧
    87*(75:ℤ)^3+375*75*(4*75-3)+1000*((wordMatrix words-1)^3).trace-
      1110*149*(75-1)=(34815390:ℤ) ∧ 0≤(34815390:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 75 ⊕ Fin 75 → Fin 150
  | .inl i => Fin.ofNat 150 (#[2, 3, 8, 10, 11, 12, 13, 14, 15, 18, 21, 23, 27, 32, 34, 38, 40, 41, 43, 44, 48, 50, 51, 52, 55, 56, 57, 58, 59, 60, 62, 65, 66, 70, 71, 72, 74, 75, 77, 78, 79, 83, 84, 87, 89, 90, 91, 92, 93, 94, 97, 98, 99, 101, 105, 106, 108, 109, 111, 115, 117, 122, 126, 128, 131, 134, 135, 136, 137, 138, 139, 141, 146, 147, 149][i.val]!)
  | .inr i => Fin.ofNat 150 (#[0, 1, 4, 5, 6, 7, 9, 16, 17, 19, 20, 22, 24, 25, 26, 28, 29, 30, 31, 33, 35, 36, 37, 39, 42, 45, 46, 47, 49, 53, 54, 61, 63, 64, 67, 68, 69, 73, 76, 80, 81, 82, 85, 86, 88, 95, 96, 100, 102, 103, 104, 107, 110, 112, 113, 114, 116, 118, 119, 120, 121, 123, 124, 125, 127, 129, 130, 132, 133, 140, 142, 143, 144, 145, 148][i.val]!)

def pointPosition (i : Fin 150) : Fin 75 ⊕ Fin 75 :=
  let j : ℕ := #[75, 76, 0, 1, 77, 78, 79, 80, 2, 81, 3, 4, 5, 6, 7, 8, 82, 83, 9, 84, 85, 10, 86, 11, 87, 88, 89, 12, 90, 91, 92, 93, 13, 94, 14, 95, 96, 97, 15, 98, 16, 17, 99, 18, 19, 100, 101, 102, 20, 103, 21, 22, 23, 104, 105, 24, 25, 26, 27, 28, 29, 106, 30, 107, 108, 31, 32, 109, 110, 111, 33, 34, 35, 112, 36, 37, 113, 38, 39, 40, 114, 115, 116, 41, 42, 117, 118, 43, 119, 44, 45, 46, 47, 48, 49, 120, 121, 50, 51, 52, 122, 53, 123, 124, 125, 54, 55, 126, 56, 57, 127, 58, 128, 129, 130, 59, 131, 60, 132, 133, 134, 135, 61, 136, 137, 138, 62, 139, 63, 140, 141, 64, 142, 143, 65, 66, 67, 68, 69, 70, 144, 71, 145, 146, 147, 148, 72, 73, 149, 74][i.val]!
  if j<75 then .inl (Fin.ofNat 75 j) else .inr (Fin.ofNat 75 (j-75))

def indexing : (Fin 75 ⊕ Fin 75) ≃ Fin 150 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 75,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*149)*(149-1)^74) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 74 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 74 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 74=(2*149)*(149-1)^74 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquaresOpposite


namespace SplitNonsquaresOpposite
def rawWords (i : ℕ) : ℕ := #[10432902903064578248034, 6899819107720776259033, 4584370483151035720656, 9225126033766526258146, 18467618934850020530086, 18006710280868479438745, 3115801150013569231119, 15427372827891863376702, 4775813411775929877759, 10058915612772977820860, 12001836418108525189939, 283178944748527821929, 1073645753057020757138, 10716958043480632903748, 6083900860154237891285, 2704733406428062163400, 4754533161548772558832, 10468331827523865592770, 12524519318794089993993, 4093122511841163222657, 7892210651036186344482, 16005781177623418289476, 17101422654792634923093, 11165970119025972463875, 4228236033174832876567, 8771252191800850272524, 16868049896949266819642, 11745839948067004638381, 9277792165206065488165, 17956102399193481872970, 17056298952578253750959, 1058338898305298372383, 11275488614880376859262, 7931166593631224900085, 6990708253145164765928, 13317269391617955656114, 17994286681082787894481, 10268407855351093558223, 5722910129007533088301, 1723195067618000616826, 12955721627998510857942, 9321519398131912799001, 18366410666981669464688, 18096544701539197379815, 6078322929196504816335, 12139276609391881829822, 13366501737041922487545, 6812971849579995814183, 3581685862554761886574, 17132689584813171389084, 14209688359002942851817, 12552808070140032590823, 2563253777903408437019, 5035423467195621551958, 9553149211872193093356, 10692438232187202223509, 4999972678688632929201, 1171982465219008525826, 1440079053650583348516, 12639707365465148083786, 2514249583736558959753, 5396319195075871453552, 11078458348331950042048, 15115013250086229370181, 4511075777143239297553, 18825448711197772127490, 9208330095405132818571, 17752620047417977887828, 11358736045039130677295, 7520077592615024202335, 5299152020588108210366, 868734075705092768892, 11485486956630754017722, 5216451451532289124017, 0][i]!
def words (i : Fin 75) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 197, 149]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 75 rawWords i=rowTotals i)

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
private theorem row69 : rowAgrees 69=true := by decide +kernel
private theorem row70 : rowAgrees 70=true := by decide +kernel
private theorem row71 : rowAgrees 71=true := by decide +kernel
private theorem row72 : rowAgrees 72=true := by decide +kernel
private theorem row73 : rowAgrees 73=true := by decide +kernel
private theorem row74 : rowAgrees 74=true := by decide +kernel
private theorem rowChecked : allBelow 75 rowAgrees=true := by
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
  have h := allBelow_step h row69
  have h := allBelow_step h row70
  have h := allBelow_step h row71
  have h := allBelow_step h row72
  have h := allBelow_step h row73
  have h := allBelow_step h row74
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 75, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 75, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-1998:ℤ) := by
  change cubicInteger (fun i : Fin 75 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-1998:ℤ) ∧
    87*(75:ℤ)^3+375*75*(4*75-3)+1000*((wordMatrix words-1)^3).trace-
      1110*149*(75-1)=(30819390:ℤ) ∧ 0≤(30819390:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 75 ⊕ Fin 75 → Fin 150
  | .inl i => Fin.ofNat 150 (#[1, 4, 5, 6, 7, 9, 16, 17, 19, 20, 22, 24, 25, 26, 28, 29, 30, 31, 33, 35, 36, 37, 39, 42, 45, 46, 47, 49, 53, 54, 61, 63, 64, 67, 68, 69, 73, 76, 80, 81, 82, 85, 86, 88, 95, 96, 100, 102, 103, 104, 107, 110, 112, 113, 114, 116, 118, 119, 120, 121, 123, 124, 125, 127, 129, 130, 132, 133, 140, 142, 143, 144, 145, 148, 149][i.val]!)
  | .inr i => Fin.ofNat 150 (#[0, 2, 3, 8, 10, 11, 12, 13, 14, 15, 18, 21, 23, 27, 32, 34, 38, 40, 41, 43, 44, 48, 50, 51, 52, 55, 56, 57, 58, 59, 60, 62, 65, 66, 70, 71, 72, 74, 75, 77, 78, 79, 83, 84, 87, 89, 90, 91, 92, 93, 94, 97, 98, 99, 101, 105, 106, 108, 109, 111, 115, 117, 122, 126, 128, 131, 134, 135, 136, 137, 138, 139, 141, 146, 147][i.val]!)

def pointPosition (i : Fin 150) : Fin 75 ⊕ Fin 75 :=
  let j : ℕ := #[75, 0, 76, 77, 1, 2, 3, 4, 78, 5, 79, 80, 81, 82, 83, 84, 6, 7, 85, 8, 9, 86, 10, 87, 11, 12, 13, 88, 14, 15, 16, 17, 89, 18, 90, 19, 20, 21, 91, 22, 92, 93, 23, 94, 95, 24, 25, 26, 96, 27, 97, 98, 99, 28, 29, 100, 101, 102, 103, 104, 105, 30, 106, 31, 32, 107, 108, 33, 34, 35, 109, 110, 111, 36, 112, 113, 37, 114, 115, 116, 38, 39, 40, 117, 118, 41, 42, 119, 43, 120, 121, 122, 123, 124, 125, 44, 45, 126, 127, 128, 46, 129, 47, 48, 49, 130, 131, 50, 132, 133, 51, 134, 52, 53, 54, 135, 55, 136, 56, 57, 58, 59, 137, 60, 61, 62, 138, 63, 139, 64, 65, 140, 66, 67, 141, 142, 143, 144, 145, 146, 68, 147, 69, 70, 71, 72, 148, 149, 73, 74][i.val]!
  if j<75 then .inl (Fin.ofNat 75 j) else .inr (Fin.ofNat 75 (j-75))

def indexing : (Fin 75 ⊕ Fin 75) ≃ Fin 150 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 75,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*149)*(149-1)^74) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 74 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 74 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 74=(2*149)*(149-1)^74 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquaresOpposite


namespace NonsplitNegativeOpposite
def rawWords (i : ℕ) : ℕ := #[13927549839194467490490, 4321896207928435763305, 18041370292281848509376, 17129204810569596014243, 15405732665928562405153, 11996646733733598157339, 5083490991172739576070, 97364342836687086093, 17616633351097219577428, 10279308479086237182397, 1368489325771843813656, 5136030323595430314555, 663124816554819494245, 1683038376274005070806, 4793814623563091087155, 3391722192341713428032, 18293024944726955675298, 11484057223392548722773, 9942713654834019055745, 9187774382003326380621, 2183812103760787854514, 16177143238317124077830, 9331595073161434619940, 12458728899072861127764, 7665482844019754467705, 7919952479409148944531, 14714649089751889234513, 14667362147520336536741, 2302629770310857986963, 11099633730476353520971, 1935305026390324811373, 8924876857241479695517, 14683007421029845127422, 12247292225381524874232, 9131662016293544401717, 11186545465906097710703, 14439912442773442440946, 5862935098088134626755, 18181078474521619782121, 12753635825017038799838, 2344182967312877019045, 9374019938665906028387, 13665012199483087662878, 13459298956136334384216, 15541399055349408446057, 14889116050419282029816, 12185655267658379420515, 10206303219859239851747, 14833039015908894026454, 11695489120041344911334, 3109400922023392647957, 2658521226518292524670, 7126155027070708464859, 5693993603436239198648, 13159057029353988563262, 9526682683552937409889, 12551178462093552305625, 5124258180941638621167, 182250615491420155828, 15121897901705971363586, 7952909187136344617832, 12287089845339809988368, 16252721085586072721826, 1808799960292336849224, 13989423622922466095825, 3130763466870752279927, 13006297039645541894784, 7124282139147577534242, 15964083634149523302725, 9810868762896450097931, 14568334743975893869591, 280257965525880635695, 11074545475443501910364, 6888256752506380944189, 0][i]!
def words (i : Fin 75) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293, 293]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 75 rawWords i=rowTotals i)

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
private theorem row69 : rowAgrees 69=true := by decide +kernel
private theorem row70 : rowAgrees 70=true := by decide +kernel
private theorem row71 : rowAgrees 71=true := by decide +kernel
private theorem row72 : rowAgrees 72=true := by decide +kernel
private theorem row73 : rowAgrees 73=true := by decide +kernel
private theorem row74 : rowAgrees 74=true := by decide +kernel
private theorem rowChecked : allBelow 75 rowAgrees=true := by
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
  have h := allBelow_step h row69
  have h := allBelow_step h row70
  have h := allBelow_step h row71
  have h := allBelow_step h row72
  have h := allBelow_step h row73
  have h := allBelow_step h row74
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 75, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 75, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(5250:ℤ) := by
  change cubicInteger (fun i : Fin 75 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(5250:ℤ) ∧
    87*(75:ℤ)^3+375*75*(4*75-3)+1000*((wordMatrix words-1)^3).trace-
      1110*149*(75-1)=(38067390:ℤ) ∧ 0≤(38067390:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 75 ⊕ Fin 75 → Fin 150
  | .inl i => Fin.ofNat 150 (#[1, 3, 7, 11, 12, 14, 18, 19, 20, 22, 23, 24, 28, 30, 35, 36, 37, 39, 42, 45, 46, 47, 48, 50, 52, 53, 56, 57, 60, 61, 66, 67, 69, 70, 72, 73, 74, 75, 76, 77, 79, 80, 82, 83, 88, 89, 92, 93, 96, 97, 99, 101, 102, 103, 104, 107, 110, 112, 113, 114, 119, 121, 125, 126, 127, 129, 130, 131, 135, 137, 138, 142, 146, 148, 149][i.val]!)
  | .inr i => Fin.ofNat 150 (#[0, 2, 4, 5, 6, 8, 9, 10, 13, 15, 16, 17, 21, 25, 26, 27, 29, 31, 32, 33, 34, 38, 40, 41, 43, 44, 49, 51, 54, 55, 58, 59, 62, 63, 64, 65, 68, 71, 78, 81, 84, 85, 86, 87, 90, 91, 94, 95, 98, 100, 105, 106, 108, 109, 111, 115, 116, 117, 118, 120, 122, 123, 124, 128, 132, 133, 134, 136, 139, 140, 141, 143, 144, 145, 147][i.val]!)

def pointPosition (i : Fin 150) : Fin 75 ⊕ Fin 75 :=
  let j : ℕ := #[75, 0, 76, 1, 77, 78, 79, 2, 80, 81, 82, 3, 4, 83, 5, 84, 85, 86, 6, 7, 8, 87, 9, 10, 11, 88, 89, 90, 12, 91, 13, 92, 93, 94, 95, 14, 15, 16, 96, 17, 97, 98, 18, 99, 100, 19, 20, 21, 22, 101, 23, 102, 24, 25, 103, 104, 26, 27, 105, 106, 28, 29, 107, 108, 109, 110, 30, 31, 111, 32, 33, 112, 34, 35, 36, 37, 38, 39, 113, 40, 41, 114, 42, 43, 115, 116, 117, 118, 44, 45, 119, 120, 46, 47, 121, 122, 48, 49, 123, 50, 124, 51, 52, 53, 54, 125, 126, 55, 127, 128, 56, 129, 57, 58, 59, 130, 131, 132, 133, 60, 134, 61, 135, 136, 137, 62, 63, 64, 138, 65, 66, 67, 139, 140, 141, 68, 142, 69, 70, 143, 144, 145, 71, 146, 147, 148, 72, 149, 73, 74][i.val]!
  if j<75 then .inl (Fin.ofNat 75 j) else .inr (Fin.ofNat 75 (j-75))

def indexing : (Fin 75 ⊕ Fin 75) ≃ Fin 150 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 75,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*149)*(149-1)^74) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 74 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 74 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 74=(2*149)*(149-1)^74 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegativeOpposite

end PaleyBits149
