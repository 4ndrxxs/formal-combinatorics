import Quantum.Hadamard.ConferenceBitCompletion
open Hadamard.BitTrace Hadamard.DeterminantRatio Matrix
set_option maxHeartbeats 12000000
set_option maxRecDepth 60000
namespace PaleyBits109

def rawFull (i : ℕ) : ℕ := #[176014145500707040523653282164036, 352028291001414081047306564328072, 55019474685974708528301087503633, 110038949371949417056602175007266, 220077898743898834113204350014532, 440155797487797668226408700029064, 231274487658741882886505358905617, 462548975317483765773010717811234, 276060843318114077979709394469957, 552121686636228155959418788939914, 455206265955602858352525536727317, 261375424594352263138739032302123, 522750849188704526277478064604246, 396464591060555598988644088055981, 143892074804257744410976134959451, 287784149608515488821952269918902, 575568299217030977643904539837804, 502099491117208501721497038523097, 355161874917563549876682035893683, 61286642518273646187052030634855, 122573285036547292374104061269710, 245146570073094584748208122539420, 490293140146189169496416245078840, 331549172975524885426520449005169, 14061238634196317286728856857827, 28122477268392634573457713715654, 56244954536785269146915427431308, 112489909073570538293830854862616, 224979818147141076587661709725232, 449959636294282153175323419450464, 250882165271710852784334797748417, 501764330543421705568669595496834, 354491553769989957571027149841157, 59946000223126461575742258529803, 119892000446252923151484517059606, 239784000892505846302969034119212, 479568001785011692605938068238424, 310098896253169931645564095324337, 620197792506339863291128190648674, 591358477695826273015944340144837, 533679848074799092465576639137163, 418322588832744731364841237121815, 187608070348636009163370433091119, 375216140697272018326740866182238, 101395174077690583087169691211965, 202790348155381166174339382423930, 405580696310762332348678764847860, 162124285304671211131045488543209, 324248570609342422262090977086418, 648497141218684844524181954172836, 647957175120516235482051867193161, 646877242924179017397791693233811, 644717378531504581229271345315111, 640397649746155708892230649477711, 631758192175457964218149257802911, 614479277034062474869986474453311, 579921446751271496173660907754111, 510805786185689538781009774355711, 372574465054525623995707507558911, 96111822792197794425102973965311, 192223645584395588850205947930622, 384447291168791177700411895861244, 119857475020728901834511750569977, 239714950041457803669023501139954, 479429900082915607338047002279908, 309822692848977761109781963407305, 619645385697955522219563926814610, 590253664079057590872815812476709, 531470220841261728179319583800907, 413903334365670002792327126449303, 178769561414486552018342211746095, 357539122828973104036684423492190, 66041138341092754507056805831869, 132082276682185509014113611663738, 264164553364371018028227223327476, 528329106728742036056454446654952, 407621106140630618546596852157393, 166205104964407783526881663162275, 332410209928815567053763326324550, 15783312540777680541214611496589, 31566625081555361082429222993178, 63133250163110722164858445986356, 126266500326221444329716891972712, 252533000652442888659433783945424, 505066001304885777318867567890848, 361094895292918101071423094629185, 73152683268982748576534148105859, 146305366537965497153068296211718, 292610733075930994306136592423436, 585221466151861988612273184846872, 521405824986870523658234328541233, 393774542656887593750156615929955, 138511977996921733934001190707399, 277023955993843467868002381414798, 554047911987686935736004762829596, 459058716658520417905697484506681, 269080326000187382245082927860851, 538160652000374764490165855721702, 427284196683896075414019670290893, 205531286050938697261727299429275, 411062572101877394523454598858550, 173088036886901335480597156564589, 346176073773802670961194313129178, 43315040230751888356076585105845, 86630080461503776712153170211690, 173260160923007553424306340423380, 346520321846015106848612680846760, 44003536375176760130913320541009, 88007072750353520261826641082018, 0][i]!
def fullRows (i : Fin 110) : ℕ := rawFull i.val

private theorem fullSymmetric : (wordMatrix fullRows).IsSymm := by
  have h : ∀ i j : Fin 110, sign (fullRows i) j.val=sign (fullRows j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem fullDiagonal : ∀ i : Fin 110, sign (fullRows i) i.val=1 := by decide +kernel
private theorem lower0 : (lowerRow 110 rawFull) 0=true := by decide +kernel
private theorem lower1 : (lowerRow 110 rawFull) 1=true := by decide +kernel
private theorem lower2 : (lowerRow 110 rawFull) 2=true := by decide +kernel
private theorem lower3 : (lowerRow 110 rawFull) 3=true := by decide +kernel
private theorem lower4 : (lowerRow 110 rawFull) 4=true := by decide +kernel
private theorem lower5 : (lowerRow 110 rawFull) 5=true := by decide +kernel
private theorem lower6 : (lowerRow 110 rawFull) 6=true := by decide +kernel
private theorem lower7 : (lowerRow 110 rawFull) 7=true := by decide +kernel
private theorem lower8 : (lowerRow 110 rawFull) 8=true := by decide +kernel
private theorem lower9 : (lowerRow 110 rawFull) 9=true := by decide +kernel
private theorem lower10 : (lowerRow 110 rawFull) 10=true := by decide +kernel
private theorem lower11 : (lowerRow 110 rawFull) 11=true := by decide +kernel
private theorem lower12 : (lowerRow 110 rawFull) 12=true := by decide +kernel
private theorem lower13 : (lowerRow 110 rawFull) 13=true := by decide +kernel
private theorem lower14 : (lowerRow 110 rawFull) 14=true := by decide +kernel
private theorem lower15 : (lowerRow 110 rawFull) 15=true := by decide +kernel
private theorem lower16 : (lowerRow 110 rawFull) 16=true := by decide +kernel
private theorem lower17 : (lowerRow 110 rawFull) 17=true := by decide +kernel
private theorem lower18 : (lowerRow 110 rawFull) 18=true := by decide +kernel
private theorem lower19 : (lowerRow 110 rawFull) 19=true := by decide +kernel
private theorem lower20 : (lowerRow 110 rawFull) 20=true := by decide +kernel
private theorem lower21 : (lowerRow 110 rawFull) 21=true := by decide +kernel
private theorem lower22 : (lowerRow 110 rawFull) 22=true := by decide +kernel
private theorem lower23 : (lowerRow 110 rawFull) 23=true := by decide +kernel
private theorem lower24 : (lowerRow 110 rawFull) 24=true := by decide +kernel
private theorem lower25 : (lowerRow 110 rawFull) 25=true := by decide +kernel
private theorem lower26 : (lowerRow 110 rawFull) 26=true := by decide +kernel
private theorem lower27 : (lowerRow 110 rawFull) 27=true := by decide +kernel
private theorem lower28 : (lowerRow 110 rawFull) 28=true := by decide +kernel
private theorem lower29 : (lowerRow 110 rawFull) 29=true := by decide +kernel
private theorem lower30 : (lowerRow 110 rawFull) 30=true := by decide +kernel
private theorem lower31 : (lowerRow 110 rawFull) 31=true := by decide +kernel
private theorem lower32 : (lowerRow 110 rawFull) 32=true := by decide +kernel
private theorem lower33 : (lowerRow 110 rawFull) 33=true := by decide +kernel
private theorem lower34 : (lowerRow 110 rawFull) 34=true := by decide +kernel
private theorem lower35 : (lowerRow 110 rawFull) 35=true := by decide +kernel
private theorem lower36 : (lowerRow 110 rawFull) 36=true := by decide +kernel
private theorem lower37 : (lowerRow 110 rawFull) 37=true := by decide +kernel
private theorem lower38 : (lowerRow 110 rawFull) 38=true := by decide +kernel
private theorem lower39 : (lowerRow 110 rawFull) 39=true := by decide +kernel
private theorem lower40 : (lowerRow 110 rawFull) 40=true := by decide +kernel
private theorem lower41 : (lowerRow 110 rawFull) 41=true := by decide +kernel
private theorem lower42 : (lowerRow 110 rawFull) 42=true := by decide +kernel
private theorem lower43 : (lowerRow 110 rawFull) 43=true := by decide +kernel
private theorem lower44 : (lowerRow 110 rawFull) 44=true := by decide +kernel
private theorem lower45 : (lowerRow 110 rawFull) 45=true := by decide +kernel
private theorem lower46 : (lowerRow 110 rawFull) 46=true := by decide +kernel
private theorem lower47 : (lowerRow 110 rawFull) 47=true := by decide +kernel
private theorem lower48 : (lowerRow 110 rawFull) 48=true := by decide +kernel
private theorem lower49 : (lowerRow 110 rawFull) 49=true := by decide +kernel
private theorem lower50 : (lowerRow 110 rawFull) 50=true := by decide +kernel
private theorem lower51 : (lowerRow 110 rawFull) 51=true := by decide +kernel
private theorem lower52 : (lowerRow 110 rawFull) 52=true := by decide +kernel
private theorem lower53 : (lowerRow 110 rawFull) 53=true := by decide +kernel
private theorem lower54 : (lowerRow 110 rawFull) 54=true := by decide +kernel
private theorem lower55 : (lowerRow 110 rawFull) 55=true := by decide +kernel
private theorem lower56 : (lowerRow 110 rawFull) 56=true := by decide +kernel
private theorem lower57 : (lowerRow 110 rawFull) 57=true := by decide +kernel
private theorem lower58 : (lowerRow 110 rawFull) 58=true := by decide +kernel
private theorem lower59 : (lowerRow 110 rawFull) 59=true := by decide +kernel
private theorem lower60 : (lowerRow 110 rawFull) 60=true := by decide +kernel
private theorem lower61 : (lowerRow 110 rawFull) 61=true := by decide +kernel
private theorem lower62 : (lowerRow 110 rawFull) 62=true := by decide +kernel
private theorem lower63 : (lowerRow 110 rawFull) 63=true := by decide +kernel
private theorem lower64 : (lowerRow 110 rawFull) 64=true := by decide +kernel
private theorem lower65 : (lowerRow 110 rawFull) 65=true := by decide +kernel
private theorem lower66 : (lowerRow 110 rawFull) 66=true := by decide +kernel
private theorem lower67 : (lowerRow 110 rawFull) 67=true := by decide +kernel
private theorem lower68 : (lowerRow 110 rawFull) 68=true := by decide +kernel
private theorem lower69 : (lowerRow 110 rawFull) 69=true := by decide +kernel
private theorem lower70 : (lowerRow 110 rawFull) 70=true := by decide +kernel
private theorem lower71 : (lowerRow 110 rawFull) 71=true := by decide +kernel
private theorem lower72 : (lowerRow 110 rawFull) 72=true := by decide +kernel
private theorem lower73 : (lowerRow 110 rawFull) 73=true := by decide +kernel
private theorem lower74 : (lowerRow 110 rawFull) 74=true := by decide +kernel
private theorem lower75 : (lowerRow 110 rawFull) 75=true := by decide +kernel
private theorem lower76 : (lowerRow 110 rawFull) 76=true := by decide +kernel
private theorem lower77 : (lowerRow 110 rawFull) 77=true := by decide +kernel
private theorem lower78 : (lowerRow 110 rawFull) 78=true := by decide +kernel
private theorem lower79 : (lowerRow 110 rawFull) 79=true := by decide +kernel
private theorem lower80 : (lowerRow 110 rawFull) 80=true := by decide +kernel
private theorem lower81 : (lowerRow 110 rawFull) 81=true := by decide +kernel
private theorem lower82 : (lowerRow 110 rawFull) 82=true := by decide +kernel
private theorem lower83 : (lowerRow 110 rawFull) 83=true := by decide +kernel
private theorem lower84 : (lowerRow 110 rawFull) 84=true := by decide +kernel
private theorem lower85 : (lowerRow 110 rawFull) 85=true := by decide +kernel
private theorem lower86 : (lowerRow 110 rawFull) 86=true := by decide +kernel
private theorem lower87 : (lowerRow 110 rawFull) 87=true := by decide +kernel
private theorem lower88 : (lowerRow 110 rawFull) 88=true := by decide +kernel
private theorem lower89 : (lowerRow 110 rawFull) 89=true := by decide +kernel
private theorem lower90 : (lowerRow 110 rawFull) 90=true := by decide +kernel
private theorem lower91 : (lowerRow 110 rawFull) 91=true := by decide +kernel
private theorem lower92 : (lowerRow 110 rawFull) 92=true := by decide +kernel
private theorem lower93 : (lowerRow 110 rawFull) 93=true := by decide +kernel
private theorem lower94 : (lowerRow 110 rawFull) 94=true := by decide +kernel
private theorem lower95 : (lowerRow 110 rawFull) 95=true := by decide +kernel
private theorem lower96 : (lowerRow 110 rawFull) 96=true := by decide +kernel
private theorem lower97 : (lowerRow 110 rawFull) 97=true := by decide +kernel
private theorem lower98 : (lowerRow 110 rawFull) 98=true := by decide +kernel
private theorem lower99 : (lowerRow 110 rawFull) 99=true := by decide +kernel
private theorem lower100 : (lowerRow 110 rawFull) 100=true := by decide +kernel
private theorem lower101 : (lowerRow 110 rawFull) 101=true := by decide +kernel
private theorem lower102 : (lowerRow 110 rawFull) 102=true := by decide +kernel
private theorem lower103 : (lowerRow 110 rawFull) 103=true := by decide +kernel
private theorem lower104 : (lowerRow 110 rawFull) 104=true := by decide +kernel
private theorem lower105 : (lowerRow 110 rawFull) 105=true := by decide +kernel
private theorem lower106 : (lowerRow 110 rawFull) 106=true := by decide +kernel
private theorem lower107 : (lowerRow 110 rawFull) 107=true := by decide +kernel
private theorem lower108 : (lowerRow 110 rawFull) 108=true := by decide +kernel
private theorem lower109 : (lowerRow 110 rawFull) 109=true := by decide +kernel
private theorem lowerChecked : allBelow 110 (lowerRow 110 rawFull)=true := by
  have h : allBelow 0 (lowerRow 110 rawFull)=true := rfl
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
  exact h

private theorem fullPairs : ∀ i j : Fin 110, i≠j →
    correlation 110 (fullRows i) (fullRows j)=2*sign (fullRows i) j.val :=
  correlations_of_lower rawFull fullSymmetric lowerChecked


namespace SplitSquares
def rawWords (i : ℕ) : ℕ := #[0, 22316131818415588, 12650251478425170, 6371461437168000, 30123994297602852, 33009649724976466, 25491816279299366, 21732722577142794, 14231318389549178, 28242877588623380, 13855215275823334, 9977511578337580, 18204604947826396, 3887811056140706, 5866879317510116, 11725104275925580, 7687717444408664, 31982350062881680, 18717772100021410, 12522060989419274, 8999606012787348, 34052378064416908, 32635095024250130, 24716287910503438, 4271812063910302, 26839219837309560, 17513996741387114, 35590664468325104, 4299292506427006, 24422877416070268, 8525399135116026, 34229691104408816, 31567290699543530, 20465778814783438, 13808295574658846, 11643011827539960, 22784649604185652, 19479225953025602, 2763250506922382, 7505364284076760, 14166429026215316, 11224457106942760, 19563813087998896, 16713181388813570, 14779062165589700, 29003686742891660, 11271473716881958, 26483741710020940, 22569042008321202, 28336066059897178, 21029398972490414, 10353872815628502, 450344214807912, 20964446397173556, 11158065909207794][i]!
def words (i : Fin 55) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[109, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 55 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 55 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 55, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 55, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-2538:ℤ) := by
  change cubicInteger (fun i : Fin 55 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-2538:ℤ) ∧
    87*(55:ℤ)^3+375*55*(4*55-3)+1000*((wordMatrix words-1)^3).trace-
      1110*109*(55-1)=(9878790:ℤ) ∧ 0≤(9878790:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 55 ⊕ Fin 55 → Fin 110
  | .inl i => Fin.ofNat 110 (#[0, 1, 3, 4, 5, 7, 9, 12, 15, 16, 20, 21, 22, 25, 26, 27, 28, 29, 31, 34, 35, 36, 38, 43, 45, 46, 48, 49, 60, 61, 63, 64, 66, 71, 73, 74, 75, 78, 80, 81, 82, 83, 84, 87, 88, 89, 93, 94, 97, 100, 102, 104, 105, 106, 108][i.val]!)
  | .inr i => Fin.ofNat 110 (#[2, 6, 8, 10, 11, 13, 14, 17, 18, 19, 23, 24, 30, 32, 33, 37, 39, 40, 41, 42, 44, 47, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 62, 65, 67, 68, 69, 70, 72, 76, 77, 79, 85, 86, 90, 91, 92, 95, 96, 98, 99, 101, 103, 107, 109][i.val]!)

def pointPosition (i : Fin 110) : Fin 55 ⊕ Fin 55 :=
  let j : ℕ := #[0, 1, 55, 2, 3, 4, 56, 5, 57, 6, 58, 59, 7, 60, 61, 8, 9, 62, 63, 64, 10, 11, 12, 65, 66, 13, 14, 15, 16, 17, 67, 18, 68, 69, 19, 20, 21, 70, 22, 71, 72, 73, 74, 23, 75, 24, 25, 76, 26, 27, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 28, 29, 87, 30, 31, 88, 32, 89, 90, 91, 92, 33, 93, 34, 35, 36, 94, 95, 37, 96, 38, 39, 40, 41, 42, 97, 98, 43, 44, 45, 99, 100, 101, 46, 47, 102, 103, 48, 104, 105, 49, 106, 50, 107, 51, 52, 53, 108, 54, 109][i.val]!
  if j<55 then .inl (Fin.ofNat 55 j) else .inr (Fin.ofNat 55 (j-55))

def indexing : (Fin 55 ⊕ Fin 55) ≃ Fin 110 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 55,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*109)*(109-1)^54) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 54 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 54 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 54=(2*109)*(109-1)^54 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquares


namespace SplitNonsquares
def rawWords (i : ℕ) : ℕ := #[36028797018963966, 14782839316431961, 24427952456482185, 30411733877933719, 5373031129324043, 32129372985505089, 12570700846038051, 2381528183197709, 27617506907401253, 9354609790898201, 2062553405579631, 2796393955426645, 14310231485539061, 21843903228171621, 6893552190895819, 15193895162481809, 21365058084937409, 24758402979299335, 22490243212011801, 13449250310634283, 26903422655815187, 17833094426960035, 16983352217942429, 31771731235947389, 33179375122630321, 30057789749101691, 27509544994613479, 24579162105524691, 21265329124100843, 29014370391678343, 26495331418411863, 3768782848657327, 17666868095223567, 16217591074941501, 19427311138429693, 20400499478047227, 23887177232421877, 6920367851661299, 27023330368663531, 976656707020755, 2586428334890925, 23481348771921433, 10883198830991795, 13306951516089165, 11964585631479697, 33363068751170273, 6767054035082373, 10190493205903431, 13523472210701841, 19209024238982453, 752160065102927, 22616042886752457, 29662844978122807, 4992071222465387, 7356130067423533][i]!
def words (i : Fin 55) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[217, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 55 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 55 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 55, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 55, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(2538:ℤ) := by
  change cubicInteger (fun i : Fin 55 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(2538:ℤ) ∧
    87*(55:ℤ)^3+375*55*(4*55-3)+1000*((wordMatrix words-1)^3).trace-
      1110*109*(55-1)=(14954790:ℤ) ∧ 0≤(14954790:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 55 ⊕ Fin 55 → Fin 110
  | .inl i => Fin.ofNat 110 (#[0, 2, 6, 8, 10, 11, 13, 14, 17, 18, 19, 23, 24, 30, 32, 33, 37, 39, 40, 41, 42, 44, 47, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 62, 65, 67, 68, 69, 70, 72, 76, 77, 79, 85, 86, 90, 91, 92, 95, 96, 98, 99, 101, 103, 107][i.val]!)
  | .inr i => Fin.ofNat 110 (#[1, 3, 4, 5, 7, 9, 12, 15, 16, 20, 21, 22, 25, 26, 27, 28, 29, 31, 34, 35, 36, 38, 43, 45, 46, 48, 49, 60, 61, 63, 64, 66, 71, 73, 74, 75, 78, 80, 81, 82, 83, 84, 87, 88, 89, 93, 94, 97, 100, 102, 104, 105, 106, 108, 109][i.val]!)

def pointPosition (i : Fin 110) : Fin 55 ⊕ Fin 55 :=
  let j : ℕ := #[0, 55, 1, 56, 57, 58, 2, 59, 3, 60, 4, 5, 61, 6, 7, 62, 63, 8, 9, 10, 64, 65, 66, 11, 12, 67, 68, 69, 70, 71, 13, 72, 14, 15, 73, 74, 75, 16, 76, 17, 18, 19, 20, 77, 21, 78, 79, 22, 80, 81, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 82, 83, 33, 84, 85, 34, 86, 35, 36, 37, 38, 87, 39, 88, 89, 90, 40, 41, 91, 42, 92, 93, 94, 95, 96, 43, 44, 97, 98, 99, 45, 46, 47, 100, 101, 48, 49, 102, 50, 51, 103, 52, 104, 53, 105, 106, 107, 54, 108, 109][i.val]!
  if j<55 then .inl (Fin.ofNat 55 j) else .inr (Fin.ofNat 55 (j-55))

def indexing : (Fin 55 ⊕ Fin 55) ≃ Fin 110 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 55,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*109)*(109-1)^54) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 54 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 54 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 54=(2*109)*(109-1)^54 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquares


namespace NonsplitNegative
def rawWords (i : ℕ) : ℕ := #[19631020927253922, 10917246268745381, 30176908227959426, 6321614062216464, 11763043380761672, 23504062135806083, 33516841485922576, 13003717286674983, 21503801458799689, 24982998190213254, 13947921747304731, 14363057364042277, 20303854187635029, 13708148025791851, 3129145684465357, 32360342722451916, 10664810940490632, 8802947884395619, 34426169353900810, 14811342905079300, 34125977374518301, 29833977623957681, 1118959994982759, 24764475582964427, 13498231075317126, 35920537548292468, 35075685012909013, 34102472524277675, 24177861348824223, 12337957304580415, 13089329573378558, 27484398400647156, 23441400319500267, 28863420200492993, 3671000555962263, 15822663321042079, 9129249364212012, 22738496738718302, 19760447137538809, 5002974726834084, 14522432105869134, 14470255930751185, 24392501032832269, 11970615271244819, 10204877325656269, 24917513048535437, 27323624996700954, 5116727548028467, 28221739334061173, 2409319413237998, 18318165835186635, 5110583451341716, 2436144618712680, 18396044727266518, 10524953165468517][i]!
def words (i : Fin 55) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133, 133]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 55 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 55 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 55, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 55, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-1650:ℤ) := by
  change cubicInteger (fun i : Fin 55 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-1650:ℤ) ∧
    87*(55:ℤ)^3+375*55*(4*55-3)+1000*((wordMatrix words-1)^3).trace-
      1110*109*(55-1)=(10766790:ℤ) ∧ 0≤(10766790:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 55 ⊕ Fin 55 → Fin 110
  | .inl i => Fin.ofNat 110 (#[0, 2, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 17, 19, 23, 28, 29, 32, 35, 36, 37, 40, 41, 42, 43, 48, 51, 52, 57, 58, 61, 66, 67, 68, 69, 72, 73, 74, 77, 80, 81, 86, 90, 92, 95, 96, 97, 98, 99, 100, 101, 102, 104, 105, 107][i.val]!)
  | .inr i => Fin.ofNat 110 (#[1, 3, 6, 15, 16, 18, 20, 21, 22, 24, 25, 26, 27, 30, 31, 33, 34, 38, 39, 44, 45, 46, 47, 49, 50, 53, 54, 55, 56, 59, 60, 62, 63, 64, 65, 70, 71, 75, 76, 78, 79, 82, 83, 84, 85, 87, 88, 89, 91, 93, 94, 103, 106, 108, 109][i.val]!)

def pointPosition (i : Fin 110) : Fin 55 ⊕ Fin 55 :=
  let j : ℕ := #[0, 55, 1, 56, 2, 3, 57, 4, 5, 6, 7, 8, 9, 10, 11, 58, 59, 12, 60, 13, 61, 62, 63, 14, 64, 65, 66, 67, 15, 16, 68, 69, 17, 70, 71, 18, 19, 20, 72, 73, 21, 22, 23, 24, 74, 75, 76, 77, 25, 78, 79, 26, 27, 80, 81, 82, 83, 28, 29, 84, 85, 30, 86, 87, 88, 89, 31, 32, 33, 34, 90, 91, 35, 36, 37, 92, 93, 38, 94, 95, 39, 40, 96, 97, 98, 99, 41, 100, 101, 102, 42, 103, 43, 104, 105, 44, 45, 46, 47, 48, 49, 50, 51, 106, 52, 53, 107, 54, 108, 109][i.val]!
  if j<55 then .inl (Fin.ofNat 55 j) else .inr (Fin.ofNat 55 (j-55))

def indexing : (Fin 55 ⊕ Fin 55) ≃ Fin 110 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 55,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*109)*(109-1)^54) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 54 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 54 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 54=(2*109)*(109-1)^54 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegative


namespace SplitSquaresOpposite
def rawWords (i : ℕ) : ℕ := #[7391419658215980, 12213976228241092, 15205866938966859, 2686515564662021, 16064686492752544, 6285350423019025, 1190764091598854, 13808753453700626, 4677304895449100, 1031276702789815, 1398196977713322, 7155115742769530, 10921951614085810, 3446776095447909, 7596947581240904, 10682529042468704, 12379201489649667, 11245121606005900, 6724625155317141, 13451711327907593, 8916547213480017, 8491676108971214, 15885865617973694, 16589687561315160, 15028894874550845, 13754772497306739, 12289581052762345, 10632664562050421, 14507185195839171, 13247665709205931, 1884391424328663, 8833434047611783, 8108795537470750, 9713655569214846, 10200249739023613, 11943588616210938, 3460183925830649, 13511665184331765, 488328353510377, 1293214167445462, 11740674385960716, 5441599415495897, 6653475758044582, 5982292815739848, 16681534375585136, 3383527017541186, 5095246602951715, 6761736105350920, 9604512119491226, 376080032551463, 11308021443376228, 14831422489061403, 2496035611232693, 3678065033711766, 0][i]!
def words (i : Fin 55) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 209, 217]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 55 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 55 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 55, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 55, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(2538:ℤ) := by
  change cubicInteger (fun i : Fin 55 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(2538:ℤ) ∧
    87*(55:ℤ)^3+375*55*(4*55-3)+1000*((wordMatrix words-1)^3).trace-
      1110*109*(55-1)=(14954790:ℤ) ∧ 0≤(14954790:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 55 ⊕ Fin 55 → Fin 110
  | .inl i => Fin.ofNat 110 (#[2, 6, 8, 10, 11, 13, 14, 17, 18, 19, 23, 24, 30, 32, 33, 37, 39, 40, 41, 42, 44, 47, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 62, 65, 67, 68, 69, 70, 72, 76, 77, 79, 85, 86, 90, 91, 92, 95, 96, 98, 99, 101, 103, 107, 109][i.val]!)
  | .inr i => Fin.ofNat 110 (#[0, 1, 3, 4, 5, 7, 9, 12, 15, 16, 20, 21, 22, 25, 26, 27, 28, 29, 31, 34, 35, 36, 38, 43, 45, 46, 48, 49, 60, 61, 63, 64, 66, 71, 73, 74, 75, 78, 80, 81, 82, 83, 84, 87, 88, 89, 93, 94, 97, 100, 102, 104, 105, 106, 108][i.val]!)

def pointPosition (i : Fin 110) : Fin 55 ⊕ Fin 55 :=
  let j : ℕ := #[55, 56, 0, 57, 58, 59, 1, 60, 2, 61, 3, 4, 62, 5, 6, 63, 64, 7, 8, 9, 65, 66, 67, 10, 11, 68, 69, 70, 71, 72, 12, 73, 13, 14, 74, 75, 76, 15, 77, 16, 17, 18, 19, 78, 20, 79, 80, 21, 81, 82, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 83, 84, 32, 85, 86, 33, 87, 34, 35, 36, 37, 88, 38, 89, 90, 91, 39, 40, 92, 41, 93, 94, 95, 96, 97, 42, 43, 98, 99, 100, 44, 45, 46, 101, 102, 47, 48, 103, 49, 50, 104, 51, 105, 52, 106, 107, 108, 53, 109, 54][i.val]!
  if j<55 then .inl (Fin.ofNat 55 j) else .inr (Fin.ofNat 55 (j-55))

def indexing : (Fin 55 ⊕ Fin 55) ≃ Fin 110 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 55,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*109)*(109-1)^54) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 54 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 54 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 54=(2*109)*(109-1)^54 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquaresOpposite


namespace SplitNonsquaresOpposite
def rawWords (i : ℕ) : ℕ := #[11158065909207794, 6325125739212585, 3185730718584000, 15061997148801426, 16504824862488233, 12745908139649683, 10866361288571397, 7115659194774589, 14121438794311690, 6927607637911667, 4988755789168790, 9102302473913198, 1943905528070353, 2933439658755058, 5862552137962790, 3843858722204332, 15991175031440840, 9358886050010705, 6261030494709637, 4499803006393674, 17026189032208454, 16317547512125065, 12358143955251719, 2135906031955151, 13419609918654780, 8756998370693557, 17795332234162552, 2149646253213503, 12211438708035134, 4262699567558013, 17114845552204408, 15783645349771765, 10232889407391719, 6904147787329423, 5821505913769980, 11392324802092826, 9739612976512801, 1381625253461191, 3752682142038380, 7083214513107658, 5612228553471380, 9781906543999448, 8356590694406785, 7389531082794850, 14501843371445830, 5635736858440979, 13241870855010470, 11284521004160601, 14168033029948589, 10514699486245207, 5176936407814251, 225172107403956, 10482223198586778, 5579032954603897, 0][i]!
def words (i : Fin 55) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 117, 109]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 55 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 55 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 55, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 55, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-2538:ℤ) := by
  change cubicInteger (fun i : Fin 55 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-2538:ℤ) ∧
    87*(55:ℤ)^3+375*55*(4*55-3)+1000*((wordMatrix words-1)^3).trace-
      1110*109*(55-1)=(9878790:ℤ) ∧ 0≤(9878790:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 55 ⊕ Fin 55 → Fin 110
  | .inl i => Fin.ofNat 110 (#[1, 3, 4, 5, 7, 9, 12, 15, 16, 20, 21, 22, 25, 26, 27, 28, 29, 31, 34, 35, 36, 38, 43, 45, 46, 48, 49, 60, 61, 63, 64, 66, 71, 73, 74, 75, 78, 80, 81, 82, 83, 84, 87, 88, 89, 93, 94, 97, 100, 102, 104, 105, 106, 108, 109][i.val]!)
  | .inr i => Fin.ofNat 110 (#[0, 2, 6, 8, 10, 11, 13, 14, 17, 18, 19, 23, 24, 30, 32, 33, 37, 39, 40, 41, 42, 44, 47, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 62, 65, 67, 68, 69, 70, 72, 76, 77, 79, 85, 86, 90, 91, 92, 95, 96, 98, 99, 101, 103, 107][i.val]!)

def pointPosition (i : Fin 110) : Fin 55 ⊕ Fin 55 :=
  let j : ℕ := #[55, 0, 56, 1, 2, 3, 57, 4, 58, 5, 59, 60, 6, 61, 62, 7, 8, 63, 64, 65, 9, 10, 11, 66, 67, 12, 13, 14, 15, 16, 68, 17, 69, 70, 18, 19, 20, 71, 21, 72, 73, 74, 75, 22, 76, 23, 24, 77, 25, 26, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 27, 28, 88, 29, 30, 89, 31, 90, 91, 92, 93, 32, 94, 33, 34, 35, 95, 96, 36, 97, 37, 38, 39, 40, 41, 98, 99, 42, 43, 44, 100, 101, 102, 45, 46, 103, 104, 47, 105, 106, 48, 107, 49, 108, 50, 51, 52, 109, 53, 54][i.val]!
  if j<55 then .inl (Fin.ofNat 55 j) else .inr (Fin.ofNat 55 (j-55))

def indexing : (Fin 55 ⊕ Fin 55) ≃ Fin 110 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 55,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*109)*(109-1)^54) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 54 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 54 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 54=(2*109)*(109-1)^54 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquaresOpposite


namespace NonsplitNegativeOpposite
def rawWords (i : ℕ) : ℕ := #[9887467802183274, 6407116237085137, 306729174050384, 5979267650784385, 14175699995048742, 12512978809145937, 4771858504214823, 5565683939102730, 10601369450095186, 4371619917277493, 1741517040308237, 4327459555967610, 8056750393164946, 4782986290135892, 12102028362548449, 2810545286436187, 7873542676286169, 17965713321375437, 15628258893680092, 8264210935184578, 2457012181227919, 11951482887377172, 8419090634220046, 16821436585241616, 17352506737481830, 17473830307307735, 15525751921599371, 14761514881402171, 16537937016949279, 7185085194312047, 577898685673719, 7900447731754478, 2852494136634261, 17001372883965764, 4732234365963950, 4200971708328059, 12625714675675903, 10929173767112694, 15387174030348260, 9508913380024277, 3008353351901122, 5146088643395150, 6632453371133628, 12388044038077720, 12144314406402172, 5226301114934633, 5632515019368690, 16085838770729922, 9733427319245709, 7097799982665363, 9091288528723754, 731294216215072, 9823340748288218, 6079140191420721, 0][i]!
def words (i : Fin 55) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 55 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 55 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 55, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 55, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(1650:ℤ) := by
  change cubicInteger (fun i : Fin 55 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(1650:ℤ) ∧
    87*(55:ℤ)^3+375*55*(4*55-3)+1000*((wordMatrix words-1)^3).trace-
      1110*109*(55-1)=(14066790:ℤ) ∧ 0≤(14066790:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 55 ⊕ Fin 55 → Fin 110
  | .inl i => Fin.ofNat 110 (#[1, 3, 6, 15, 16, 18, 20, 21, 22, 24, 25, 26, 27, 30, 31, 33, 34, 38, 39, 44, 45, 46, 47, 49, 50, 53, 54, 55, 56, 59, 60, 62, 63, 64, 65, 70, 71, 75, 76, 78, 79, 82, 83, 84, 85, 87, 88, 89, 91, 93, 94, 103, 106, 108, 109][i.val]!)
  | .inr i => Fin.ofNat 110 (#[0, 2, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 17, 19, 23, 28, 29, 32, 35, 36, 37, 40, 41, 42, 43, 48, 51, 52, 57, 58, 61, 66, 67, 68, 69, 72, 73, 74, 77, 80, 81, 86, 90, 92, 95, 96, 97, 98, 99, 100, 101, 102, 104, 105, 107][i.val]!)

def pointPosition (i : Fin 110) : Fin 55 ⊕ Fin 55 :=
  let j : ℕ := #[55, 0, 56, 1, 57, 58, 2, 59, 60, 61, 62, 63, 64, 65, 66, 3, 4, 67, 5, 68, 6, 7, 8, 69, 9, 10, 11, 12, 70, 71, 13, 14, 72, 15, 16, 73, 74, 75, 17, 18, 76, 77, 78, 79, 19, 20, 21, 22, 80, 23, 24, 81, 82, 25, 26, 27, 28, 83, 84, 29, 30, 85, 31, 32, 33, 34, 86, 87, 88, 89, 35, 36, 90, 91, 92, 37, 38, 93, 39, 40, 94, 95, 41, 42, 43, 44, 96, 45, 46, 47, 97, 48, 98, 49, 50, 99, 100, 101, 102, 103, 104, 105, 106, 51, 107, 108, 52, 109, 53, 54][i.val]!
  if j<55 then .inl (Fin.ofNat 55 j) else .inr (Fin.ofNat 55 (j-55))

def indexing : (Fin 55 ⊕ Fin 55) ≃ Fin 110 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 55,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*109)*(109-1)^54) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 54 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 54 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 54=(2*109)*(109-1)^54 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegativeOpposite

end PaleyBits109
