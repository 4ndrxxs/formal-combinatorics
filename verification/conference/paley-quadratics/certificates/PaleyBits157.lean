import Quantum.Hadamard.ConferenceBitCompletion
open Hadamard.BitTrace Hadamard.DeterminantRatio Matrix
set_option maxHeartbeats 12000000
set_option maxRecDepth 60000
namespace PaleyBits157

def rawFull (i : ℕ) : ℕ := #[56382897303629494179631795089211348116942651876, 112765794607258988359263590178422696233885303752, 42843884548155111943066576267310015010779039633, 85687769096310223886133152534620030021558079266, 171375538192620447772266305069240060043116158532, 160063371718878030769072006048944742629240749193, 137439038771393196762683408008354107801489930515, 92190372876423528749906211927172838145988293159, 1693041086484192724351819764810298834985018447, 3386082172968385448703639529620597669970036894, 6772164345936770897407279059241195339940073788, 13544328691873541794814558118482390679880147576, 27088657383747083589629116236964781359760295152, 54177314767494167179258232473929562719520590304, 108354629534988334358516464947859125439041180608, 34021554403613803941572325806182873421090793345, 68043108807227607883144651612365746842181586690, 136086217614455215766289303224731493684363173380, 89484730562547566757118002359927609911734778889, 178969461125095133514236004719855219823469557778, 175251217583827402253011405350175062189947547685, 167814730501291939730562206610814746922903527499, 152941756336221014685663809132094116388815487127, 123195808006079164595867014174652855320639406383, 63703911345795464416273424259770333184287244895, 127407822691590928832546848519540666368574489790, 72127940716818992889633092949545955280157411709, 144255881433637985779266185899091910560314823418, 105824058200913106783071767708648443663638078965, 28960411735463348790682931327761509870284590059, 57920823470926697581365862655523019740569180118, 115841646941853395162731725311046039481138360236, 48995589217343925550002846532556701505285152601, 97991178434687851100005693065113403010570305202, 13294652203012837424550782040691428564149042533, 26589304406025674849101564081382857128298085066, 53178608812051349698203128162765714256596170132, 106357217624102699396406256325531428513192340264, 30026730581842534017351908561527479569393112657, 60053461163685068034703817123054959138786225314, 120106922327370136069407634246109918277572450628, 57526139988377407363354664402684459098153333385, 115052279976754814726709328805368918196306666770, 47416855287146764677958053521202458935621765669, 94833710574293529355916107042404917871243531338, 6979716482224193936371609995274458285495494805, 13959432964448387872743219990548916570990989610, 27918865928896775745486439981097833141981979220, 55837731857793551490972879962195666283963958440, 111675463715587102981945759924391332567927916880, 40663222764811341188430915759247287678864265889, 81326445529622682376861831518494575357728531778, 162652891059245364753723663036989150715457063556, 142618077452127864731986721984442923973922559241, 102548450237892864688512839879350470490853550611, 22409195809422864601565075669165563524715533351, 44818391618845729203130151338331127049431066702, 89636783237691458406260302676662254098862133404, 179273566475382916812520605353324508197724266808, 175859428284402968849580606617113638938456965745, 169031151902443072923700609144691900419922363619, 155374599138523281071940614199848423382853159367, 128061493610683697368420624310161469308714750863, 73435282555004529961380644530787561160437933855, 146870565110009059922761289061575122320875867710, 111053425553655255070061974033614867184760167549, 39419146440947645364663343977694356912528767227, 78838292881895290729326687955388713825057534454, 157676585763790581458653375910777427650115068908, 132665466861218298141846147732019477843238569945, 82643229056073731508231691374503578229485572019, 165286458112147463016463382749007156458971144038, 147885211557932061257466161408478935460950720205, 113082718449501257739471718727422493464909872539, 43477732232639650703482833365309609472828177207, 86955464465279301406965666730619218945656354414, 173910928930558602813931333461238437891312708828, 165134153194754340852402062832941498325633849785, 147580601723145816929343521576347619194276131699, 112473498779928769083226439063159860931560695527, 42259292893494673390992274036784344406129823183, 84518585786989346781984548073568688812259646366, 169037171573978693563969096147137377624519292732, 155386638481594522352477588204739377792047017593, 128085572296826179929494572319943378127102467315, 73483439927289495083528540550351378797213366759, 146966879854578990167057081100702757594426733518, 111246055042795115558653558111870137731861899165, 39804405419227366341846512134204898006732230459, 79608810838454732683693024268409796013464460918, 159217621676909465367386048536819592026928921836, 135747538687456065959311492984103806596866275801, 88807372708549267143162381878672235736740983731, 177614745417098534286324763757344471473481967462, 172541786167834203797188923425153565489972367053, 162395867669305542818917242760771753522953166235, 142104030672248220862373881432008129588914764599, 101520356678133576949287158774480881720837961327, 20353008689904289123113713459426385984684354783, 40706017379808578246227426918852771969368709566, 81412034759617156492454853837705543938737419132, 162824069519234312984909707675411087877474838264, 142960434372105761194358811261286798297958108657, 103233164077848657613257018433038219138924649443, 23778623489334450451053432776541060820857731015, 47557246978668900902106865553082121641715462030, 95114493957337801804213731106164243283430924060, 7541283248312738832966858122793109109870280249, 15082566496625477665933716245586218219740560498, 30165132993250955331867432491172436439481120996, 60330265986501910663734864982344872878962241992, 120660531973003821327469729964689745757924483984, 58633359279644777879478855839844114058857400097, 117266718559289555758957711679688228117714800194, 51845732452216246742454819269841078778438032517, 103691464904432493484909638539682157556876065034, 24695225142502122194358672989828937656760562197, 49390450285004244388717345979657875313521124394, 98780900570008488777434691959315750627042248788, 14874096473654112779408779829096123797092929705, 29748192947308225558817559658192247594185859410, 59496385894616451117635119316384495188371718820, 118992771789232902235270238632768990376743437640, 55297838912102939695079873176002603296495307409, 110595677824205879390159746352005206592990614818, 38503650982048894004858888614475035728989661765, 77007301964097788009717777228950071457979323530, 154014603928195576019435554457900142915958647060, 125341503190028287263410504826264908374925726249, 67995301713693709751360405562994439292859884627, 135990603427387419502720811125988878585719769254, 89293502188411974229981018162442379714447970637, 178587004376823948459962036324884759428895941274, 174486304087285032144463468560234141400800314677, 166284903508207199513466333030932905344609061483, 149882102350051534251472061972330433232226555095, 117076500033740203727483519855125489007461542319, 51465295401117542679506435620715600557931516767, 102930590802235085359012871241431201115863033534, 23173476938107305942565138393327024774734499197, 46346953876214611885130276786654049549468998394, 92693907752429223770260553573308099098937996788, 2700110838495582765060503057080820740884425705, 5400221676991165530121006114161641481768851410, 10800443353982331060242012228323282963537702820, 21600886707964662120484024456646565927075405640, 43201773415929324240968048913293131854150811280, 86403546831858648481936097826586263708301622560, 172807093663717296963872195653172527416603245120, 162926482661071729152283787216809677376214922369, 143165260655780593529106970344083977295438276867, 103642816645198322282753336598632577133884985863, 24597928624033779790046069107729776810778403855, 49195857248067559580092138215459553621556807710, 98391714496135119160184276430919107243113615420, 14095724325907373544907948772302837029235662969, 28191448651814747089815897544605674058471325938, 0][i]!
def fullRows (i : Fin 158) : ℕ := rawFull i.val

private theorem fullSymmetric : (wordMatrix fullRows).IsSymm := by
  have h : ∀ i j : Fin 158, sign (fullRows i) j.val=sign (fullRows j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem fullDiagonal : ∀ i : Fin 158, sign (fullRows i) i.val=1 := by decide +kernel
private theorem lower0 : (lowerRow 158 rawFull) 0=true := by decide +kernel
private theorem lower1 : (lowerRow 158 rawFull) 1=true := by decide +kernel
private theorem lower2 : (lowerRow 158 rawFull) 2=true := by decide +kernel
private theorem lower3 : (lowerRow 158 rawFull) 3=true := by decide +kernel
private theorem lower4 : (lowerRow 158 rawFull) 4=true := by decide +kernel
private theorem lower5 : (lowerRow 158 rawFull) 5=true := by decide +kernel
private theorem lower6 : (lowerRow 158 rawFull) 6=true := by decide +kernel
private theorem lower7 : (lowerRow 158 rawFull) 7=true := by decide +kernel
private theorem lower8 : (lowerRow 158 rawFull) 8=true := by decide +kernel
private theorem lower9 : (lowerRow 158 rawFull) 9=true := by decide +kernel
private theorem lower10 : (lowerRow 158 rawFull) 10=true := by decide +kernel
private theorem lower11 : (lowerRow 158 rawFull) 11=true := by decide +kernel
private theorem lower12 : (lowerRow 158 rawFull) 12=true := by decide +kernel
private theorem lower13 : (lowerRow 158 rawFull) 13=true := by decide +kernel
private theorem lower14 : (lowerRow 158 rawFull) 14=true := by decide +kernel
private theorem lower15 : (lowerRow 158 rawFull) 15=true := by decide +kernel
private theorem lower16 : (lowerRow 158 rawFull) 16=true := by decide +kernel
private theorem lower17 : (lowerRow 158 rawFull) 17=true := by decide +kernel
private theorem lower18 : (lowerRow 158 rawFull) 18=true := by decide +kernel
private theorem lower19 : (lowerRow 158 rawFull) 19=true := by decide +kernel
private theorem lower20 : (lowerRow 158 rawFull) 20=true := by decide +kernel
private theorem lower21 : (lowerRow 158 rawFull) 21=true := by decide +kernel
private theorem lower22 : (lowerRow 158 rawFull) 22=true := by decide +kernel
private theorem lower23 : (lowerRow 158 rawFull) 23=true := by decide +kernel
private theorem lower24 : (lowerRow 158 rawFull) 24=true := by decide +kernel
private theorem lower25 : (lowerRow 158 rawFull) 25=true := by decide +kernel
private theorem lower26 : (lowerRow 158 rawFull) 26=true := by decide +kernel
private theorem lower27 : (lowerRow 158 rawFull) 27=true := by decide +kernel
private theorem lower28 : (lowerRow 158 rawFull) 28=true := by decide +kernel
private theorem lower29 : (lowerRow 158 rawFull) 29=true := by decide +kernel
private theorem lower30 : (lowerRow 158 rawFull) 30=true := by decide +kernel
private theorem lower31 : (lowerRow 158 rawFull) 31=true := by decide +kernel
private theorem lower32 : (lowerRow 158 rawFull) 32=true := by decide +kernel
private theorem lower33 : (lowerRow 158 rawFull) 33=true := by decide +kernel
private theorem lower34 : (lowerRow 158 rawFull) 34=true := by decide +kernel
private theorem lower35 : (lowerRow 158 rawFull) 35=true := by decide +kernel
private theorem lower36 : (lowerRow 158 rawFull) 36=true := by decide +kernel
private theorem lower37 : (lowerRow 158 rawFull) 37=true := by decide +kernel
private theorem lower38 : (lowerRow 158 rawFull) 38=true := by decide +kernel
private theorem lower39 : (lowerRow 158 rawFull) 39=true := by decide +kernel
private theorem lower40 : (lowerRow 158 rawFull) 40=true := by decide +kernel
private theorem lower41 : (lowerRow 158 rawFull) 41=true := by decide +kernel
private theorem lower42 : (lowerRow 158 rawFull) 42=true := by decide +kernel
private theorem lower43 : (lowerRow 158 rawFull) 43=true := by decide +kernel
private theorem lower44 : (lowerRow 158 rawFull) 44=true := by decide +kernel
private theorem lower45 : (lowerRow 158 rawFull) 45=true := by decide +kernel
private theorem lower46 : (lowerRow 158 rawFull) 46=true := by decide +kernel
private theorem lower47 : (lowerRow 158 rawFull) 47=true := by decide +kernel
private theorem lower48 : (lowerRow 158 rawFull) 48=true := by decide +kernel
private theorem lower49 : (lowerRow 158 rawFull) 49=true := by decide +kernel
private theorem lower50 : (lowerRow 158 rawFull) 50=true := by decide +kernel
private theorem lower51 : (lowerRow 158 rawFull) 51=true := by decide +kernel
private theorem lower52 : (lowerRow 158 rawFull) 52=true := by decide +kernel
private theorem lower53 : (lowerRow 158 rawFull) 53=true := by decide +kernel
private theorem lower54 : (lowerRow 158 rawFull) 54=true := by decide +kernel
private theorem lower55 : (lowerRow 158 rawFull) 55=true := by decide +kernel
private theorem lower56 : (lowerRow 158 rawFull) 56=true := by decide +kernel
private theorem lower57 : (lowerRow 158 rawFull) 57=true := by decide +kernel
private theorem lower58 : (lowerRow 158 rawFull) 58=true := by decide +kernel
private theorem lower59 : (lowerRow 158 rawFull) 59=true := by decide +kernel
private theorem lower60 : (lowerRow 158 rawFull) 60=true := by decide +kernel
private theorem lower61 : (lowerRow 158 rawFull) 61=true := by decide +kernel
private theorem lower62 : (lowerRow 158 rawFull) 62=true := by decide +kernel
private theorem lower63 : (lowerRow 158 rawFull) 63=true := by decide +kernel
private theorem lower64 : (lowerRow 158 rawFull) 64=true := by decide +kernel
private theorem lower65 : (lowerRow 158 rawFull) 65=true := by decide +kernel
private theorem lower66 : (lowerRow 158 rawFull) 66=true := by decide +kernel
private theorem lower67 : (lowerRow 158 rawFull) 67=true := by decide +kernel
private theorem lower68 : (lowerRow 158 rawFull) 68=true := by decide +kernel
private theorem lower69 : (lowerRow 158 rawFull) 69=true := by decide +kernel
private theorem lower70 : (lowerRow 158 rawFull) 70=true := by decide +kernel
private theorem lower71 : (lowerRow 158 rawFull) 71=true := by decide +kernel
private theorem lower72 : (lowerRow 158 rawFull) 72=true := by decide +kernel
private theorem lower73 : (lowerRow 158 rawFull) 73=true := by decide +kernel
private theorem lower74 : (lowerRow 158 rawFull) 74=true := by decide +kernel
private theorem lower75 : (lowerRow 158 rawFull) 75=true := by decide +kernel
private theorem lower76 : (lowerRow 158 rawFull) 76=true := by decide +kernel
private theorem lower77 : (lowerRow 158 rawFull) 77=true := by decide +kernel
private theorem lower78 : (lowerRow 158 rawFull) 78=true := by decide +kernel
private theorem lower79 : (lowerRow 158 rawFull) 79=true := by decide +kernel
private theorem lower80 : (lowerRow 158 rawFull) 80=true := by decide +kernel
private theorem lower81 : (lowerRow 158 rawFull) 81=true := by decide +kernel
private theorem lower82 : (lowerRow 158 rawFull) 82=true := by decide +kernel
private theorem lower83 : (lowerRow 158 rawFull) 83=true := by decide +kernel
private theorem lower84 : (lowerRow 158 rawFull) 84=true := by decide +kernel
private theorem lower85 : (lowerRow 158 rawFull) 85=true := by decide +kernel
private theorem lower86 : (lowerRow 158 rawFull) 86=true := by decide +kernel
private theorem lower87 : (lowerRow 158 rawFull) 87=true := by decide +kernel
private theorem lower88 : (lowerRow 158 rawFull) 88=true := by decide +kernel
private theorem lower89 : (lowerRow 158 rawFull) 89=true := by decide +kernel
private theorem lower90 : (lowerRow 158 rawFull) 90=true := by decide +kernel
private theorem lower91 : (lowerRow 158 rawFull) 91=true := by decide +kernel
private theorem lower92 : (lowerRow 158 rawFull) 92=true := by decide +kernel
private theorem lower93 : (lowerRow 158 rawFull) 93=true := by decide +kernel
private theorem lower94 : (lowerRow 158 rawFull) 94=true := by decide +kernel
private theorem lower95 : (lowerRow 158 rawFull) 95=true := by decide +kernel
private theorem lower96 : (lowerRow 158 rawFull) 96=true := by decide +kernel
private theorem lower97 : (lowerRow 158 rawFull) 97=true := by decide +kernel
private theorem lower98 : (lowerRow 158 rawFull) 98=true := by decide +kernel
private theorem lower99 : (lowerRow 158 rawFull) 99=true := by decide +kernel
private theorem lower100 : (lowerRow 158 rawFull) 100=true := by decide +kernel
private theorem lower101 : (lowerRow 158 rawFull) 101=true := by decide +kernel
private theorem lower102 : (lowerRow 158 rawFull) 102=true := by decide +kernel
private theorem lower103 : (lowerRow 158 rawFull) 103=true := by decide +kernel
private theorem lower104 : (lowerRow 158 rawFull) 104=true := by decide +kernel
private theorem lower105 : (lowerRow 158 rawFull) 105=true := by decide +kernel
private theorem lower106 : (lowerRow 158 rawFull) 106=true := by decide +kernel
private theorem lower107 : (lowerRow 158 rawFull) 107=true := by decide +kernel
private theorem lower108 : (lowerRow 158 rawFull) 108=true := by decide +kernel
private theorem lower109 : (lowerRow 158 rawFull) 109=true := by decide +kernel
private theorem lower110 : (lowerRow 158 rawFull) 110=true := by decide +kernel
private theorem lower111 : (lowerRow 158 rawFull) 111=true := by decide +kernel
private theorem lower112 : (lowerRow 158 rawFull) 112=true := by decide +kernel
private theorem lower113 : (lowerRow 158 rawFull) 113=true := by decide +kernel
private theorem lower114 : (lowerRow 158 rawFull) 114=true := by decide +kernel
private theorem lower115 : (lowerRow 158 rawFull) 115=true := by decide +kernel
private theorem lower116 : (lowerRow 158 rawFull) 116=true := by decide +kernel
private theorem lower117 : (lowerRow 158 rawFull) 117=true := by decide +kernel
private theorem lower118 : (lowerRow 158 rawFull) 118=true := by decide +kernel
private theorem lower119 : (lowerRow 158 rawFull) 119=true := by decide +kernel
private theorem lower120 : (lowerRow 158 rawFull) 120=true := by decide +kernel
private theorem lower121 : (lowerRow 158 rawFull) 121=true := by decide +kernel
private theorem lower122 : (lowerRow 158 rawFull) 122=true := by decide +kernel
private theorem lower123 : (lowerRow 158 rawFull) 123=true := by decide +kernel
private theorem lower124 : (lowerRow 158 rawFull) 124=true := by decide +kernel
private theorem lower125 : (lowerRow 158 rawFull) 125=true := by decide +kernel
private theorem lower126 : (lowerRow 158 rawFull) 126=true := by decide +kernel
private theorem lower127 : (lowerRow 158 rawFull) 127=true := by decide +kernel
private theorem lower128 : (lowerRow 158 rawFull) 128=true := by decide +kernel
private theorem lower129 : (lowerRow 158 rawFull) 129=true := by decide +kernel
private theorem lower130 : (lowerRow 158 rawFull) 130=true := by decide +kernel
private theorem lower131 : (lowerRow 158 rawFull) 131=true := by decide +kernel
private theorem lower132 : (lowerRow 158 rawFull) 132=true := by decide +kernel
private theorem lower133 : (lowerRow 158 rawFull) 133=true := by decide +kernel
private theorem lower134 : (lowerRow 158 rawFull) 134=true := by decide +kernel
private theorem lower135 : (lowerRow 158 rawFull) 135=true := by decide +kernel
private theorem lower136 : (lowerRow 158 rawFull) 136=true := by decide +kernel
private theorem lower137 : (lowerRow 158 rawFull) 137=true := by decide +kernel
private theorem lower138 : (lowerRow 158 rawFull) 138=true := by decide +kernel
private theorem lower139 : (lowerRow 158 rawFull) 139=true := by decide +kernel
private theorem lower140 : (lowerRow 158 rawFull) 140=true := by decide +kernel
private theorem lower141 : (lowerRow 158 rawFull) 141=true := by decide +kernel
private theorem lower142 : (lowerRow 158 rawFull) 142=true := by decide +kernel
private theorem lower143 : (lowerRow 158 rawFull) 143=true := by decide +kernel
private theorem lower144 : (lowerRow 158 rawFull) 144=true := by decide +kernel
private theorem lower145 : (lowerRow 158 rawFull) 145=true := by decide +kernel
private theorem lower146 : (lowerRow 158 rawFull) 146=true := by decide +kernel
private theorem lower147 : (lowerRow 158 rawFull) 147=true := by decide +kernel
private theorem lower148 : (lowerRow 158 rawFull) 148=true := by decide +kernel
private theorem lower149 : (lowerRow 158 rawFull) 149=true := by decide +kernel
private theorem lower150 : (lowerRow 158 rawFull) 150=true := by decide +kernel
private theorem lower151 : (lowerRow 158 rawFull) 151=true := by decide +kernel
private theorem lower152 : (lowerRow 158 rawFull) 152=true := by decide +kernel
private theorem lower153 : (lowerRow 158 rawFull) 153=true := by decide +kernel
private theorem lower154 : (lowerRow 158 rawFull) 154=true := by decide +kernel
private theorem lower155 : (lowerRow 158 rawFull) 155=true := by decide +kernel
private theorem lower156 : (lowerRow 158 rawFull) 156=true := by decide +kernel
private theorem lower157 : (lowerRow 158 rawFull) 157=true := by decide +kernel
private theorem lowerChecked : allBelow 158 (lowerRow 158 rawFull)=true := by
  have h : allBelow 0 (lowerRow 158 rawFull)=true := rfl
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
  have h := allBelow_step h lower150
  have h := allBelow_step h lower151
  have h := allBelow_step h lower152
  have h := allBelow_step h lower153
  have h := allBelow_step h lower154
  have h := allBelow_step h lower155
  have h := allBelow_step h lower156
  have h := allBelow_step h lower157
  exact h

private theorem fullPairs : ∀ i j : Fin 158, i≠j →
    correlation 158 (fullRows i) (fullRows j)=2*sign (fullRows i) j.val :=
  correlations_of_lower rawFull fullSymmetric lowerChecked


namespace SplitSquares
def rawWords (i : ℕ) : ℕ := #[0, 379537979227950169912340, 231924223097349508259954, 540656508644870295580912, 56005524135721064451662, 37352535337113999879308, 149105437207375222611228, 224031184280918837615144, 69305244940933521150016, 440408412513071173211280, 102232786212638363812466, 581152700241488817434864, 588095163673157957610442, 569731922504027283380270, 313492428799492506398878, 87473863943769651159226, 478317551411220929193332, 326200613719170047369722, 170294404304544931695574, 39537839539905571686312, 381118628529327044927316, 86845459502130135244130, 476023903089407711133376, 470386878901818008295210, 369478391158906646168742, 117963280374498666293894, 160262627683081436295448, 18110017017781120333348, 415378412598767413979208, 298880697695648950778146, 523425770364353687683664, 287819320601171498811718, 272489421911049239475852, 545126564208729055332620, 363249110085110302806654, 187561461947736823040906, 449716980612898908332820, 500401373049609612594418, 291496355484311604996022, 581636373089363685740396, 259451272079732315346142, 518962858616683389541820, 373976408247549555339158, 192567286267655364599034, 386355879506927505239524, 596368520888691697375026, 229352550416501272409806, 233406440570658229702044, 465216517238084214804284, 48432566309408878848886, 324068997916661804323580, 85417767134981610385386, 172057628144957558467520, 115956740499922721961860, 459628773343252261855000, 477551422268494341651570, 400999553996367192775110, 16461516940535363973926, 333974329451541248329288, 202944557867668218981642, 103329546678539810175504, 509190881532725903618084, 451108647214070359574690, 220260775636375483814566, 439257911703442356674888, 571634712122602023700034, 548306588330924032435486, 395905116987405405851966, 71060194307335031228638, 369536675123930237789608, 43243442793547668472506, 9610548004722148685168, 96134252143022121881332, 267863876795213855902200, 232389025065625991976928, 540487881599215771073488, 71118046594157992001102, 368467430891741476370572, 189768989613975084956170][i]!
def words (i : Fin 79) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[157, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 79 rawWords i=rowTotals i)

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
private theorem row75 : rowAgrees 75=true := by decide +kernel
private theorem row76 : rowAgrees 76=true := by decide +kernel
private theorem row77 : rowAgrees 77=true := by decide +kernel
private theorem row78 : rowAgrees 78=true := by decide +kernel
private theorem rowChecked : allBelow 79 rowAgrees=true := by
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
  have h := allBelow_step h row75
  have h := allBelow_step h row76
  have h := allBelow_step h row77
  have h := allBelow_step h row78
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 79, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 79, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(3198:ℤ) := by
  change cubicInteger (fun i : Fin 79 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(3198:ℤ) ∧
    87*(79:ℤ)^3+375*79*(4*79-3)+1000*((wordMatrix words-1)^3).trace-
      1110*157*(79-1)=(41771958:ℤ) ∧ 0≤(41771958:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 79 ⊕ Fin 79 → Fin 158
  | .inl i => Fin.ofNat 158 (#[0, 1, 3, 4, 9, 10, 11, 12, 13, 14, 16, 17, 19, 25, 27, 30, 31, 33, 35, 36, 37, 39, 40, 42, 44, 46, 47, 48, 49, 51, 52, 56, 57, 58, 64, 67, 68, 71, 75, 76, 81, 82, 86, 89, 90, 93, 99, 100, 101, 105, 106, 108, 109, 110, 111, 113, 115, 117, 118, 120, 121, 122, 124, 126, 127, 130, 132, 138, 140, 141, 143, 144, 145, 146, 147, 148, 153, 154, 156][i.val]!)
  | .inr i => Fin.ofNat 158 (#[2, 5, 6, 7, 8, 15, 18, 20, 21, 22, 23, 24, 26, 28, 29, 32, 34, 38, 41, 43, 45, 50, 53, 54, 55, 59, 60, 61, 62, 63, 65, 66, 69, 70, 72, 73, 74, 77, 78, 79, 80, 83, 84, 85, 87, 88, 91, 92, 94, 95, 96, 97, 98, 102, 103, 104, 107, 112, 114, 116, 119, 123, 125, 128, 129, 131, 133, 134, 135, 136, 137, 139, 142, 149, 150, 151, 152, 155, 157][i.val]!)

def pointPosition (i : Fin 158) : Fin 79 ⊕ Fin 79 :=
  let j : ℕ := #[0, 1, 79, 2, 3, 80, 81, 82, 83, 4, 5, 6, 7, 8, 9, 84, 10, 11, 85, 12, 86, 87, 88, 89, 90, 13, 91, 14, 92, 93, 15, 16, 94, 17, 95, 18, 19, 20, 96, 21, 22, 97, 23, 98, 24, 99, 25, 26, 27, 28, 100, 29, 30, 101, 102, 103, 31, 32, 33, 104, 105, 106, 107, 108, 34, 109, 110, 35, 36, 111, 112, 37, 113, 114, 115, 38, 39, 116, 117, 118, 119, 40, 41, 120, 121, 122, 42, 123, 124, 43, 44, 125, 126, 45, 127, 128, 129, 130, 131, 46, 47, 48, 132, 133, 134, 49, 50, 135, 51, 52, 53, 54, 136, 55, 137, 56, 138, 57, 58, 139, 59, 60, 61, 140, 62, 141, 63, 64, 142, 143, 65, 144, 66, 145, 146, 147, 148, 149, 67, 150, 68, 69, 151, 70, 71, 72, 73, 74, 75, 152, 153, 154, 155, 76, 77, 156, 78, 157][i.val]!
  if j<79 then .inl (Fin.ofNat 79 j) else .inr (Fin.ofNat 79 (j-79))

def indexing : (Fin 79 ⊕ Fin 79) ≃ Fin 158 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 79,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*157)*(157-1)^78) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 78 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 78 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 78=(2*157)*(157-1)^78 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquares


namespace SplitNonsquares
def rawWords (i : ℕ) : ℕ := #[604462909807314587353086, 235760430455695476948273, 318043113946710283577617, 319765225495678591431201, 30112717602405233509447, 55709585360083524773963, 283750620686223937376049, 550462155621044451031297, 402883786450786655691975, 513150744896424415651913, 417094308732976724234579, 243804481777154758853351, 473513507232510315177099, 406331740878326138098607, 85684437985908537569087, 152533742033616863632957, 384641525108822111563817, 41462488601392369492015, 200605437477967340046793, 311301186227006048709585, 348077808707603434065735, 187933925622940869860883, 164018469674362462140053, 438239202889770882929249, 300414096313373067273473, 298608410384819927886343, 433566314718160715776653, 536484974480177886618717, 478072251747508827294139, 73009225712732012958259, 429363034471004416673187, 225301655953208824567119, 138861552044258876672541, 185194841223417315225721, 375110031457843059458421, 598495473425856115147931, 280858190379300162193841, 236028756275964017677159, 452240428689980784844021, 574015939501815079393517, 260209975190768552161695, 222999078470012003951611, 485389726480201303777165, 64094888047316766990045, 420907034129535212797311, 219621334454915874125555, 141931306491891219360997, 265982177440420615546553, 541451007915143350038005, 328819863067114995439451, 360273040865156733316849, 441868255277720910052519, 274614789063175415749007, 232580118813870929605595, 454929215324890381016317, 3076011558870921951741, 29692662453018281587515, 195674720816578144689477, 342227100107223588131813, 467259921824341016882579, 55861942546261081446275, 92391471524611892141653, 547934075911756278260497, 94675885273658958990987, 285560447006919964176901, 590079823571247153751113, 556258311511441788817515, 383203943904612908311079, 487644023463436963087821, 352020267361803339385371, 85429133883901515633975, 468219332478562125613739, 2881306807900487354671, 61099728553718107629629, 387672237887693327971281, 463439144788004227647073, 20362915889308514741699, 40569754471138391792323, 60178777804978559465357][i]!
def words (i : Fin 79) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[313, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 79 rawWords i=rowTotals i)

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
private theorem row75 : rowAgrees 75=true := by decide +kernel
private theorem row76 : rowAgrees 76=true := by decide +kernel
private theorem row77 : rowAgrees 77=true := by decide +kernel
private theorem row78 : rowAgrees 78=true := by decide +kernel
private theorem rowChecked : allBelow 79 rowAgrees=true := by
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
  have h := allBelow_step h row75
  have h := allBelow_step h row76
  have h := allBelow_step h row77
  have h := allBelow_step h row78
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 79, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 79, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-3198:ℤ) := by
  change cubicInteger (fun i : Fin 79 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-3198:ℤ) ∧
    87*(79:ℤ)^3+375*79*(4*79-3)+1000*((wordMatrix words-1)^3).trace-
      1110*157*(79-1)=(35375958:ℤ) ∧ 0≤(35375958:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 79 ⊕ Fin 79 → Fin 158
  | .inl i => Fin.ofNat 158 (#[0, 2, 5, 6, 7, 8, 15, 18, 20, 21, 22, 23, 24, 26, 28, 29, 32, 34, 38, 41, 43, 45, 50, 53, 54, 55, 59, 60, 61, 62, 63, 65, 66, 69, 70, 72, 73, 74, 77, 78, 79, 80, 83, 84, 85, 87, 88, 91, 92, 94, 95, 96, 97, 98, 102, 103, 104, 107, 112, 114, 116, 119, 123, 125, 128, 129, 131, 133, 134, 135, 136, 137, 139, 142, 149, 150, 151, 152, 155][i.val]!)
  | .inr i => Fin.ofNat 158 (#[1, 3, 4, 9, 10, 11, 12, 13, 14, 16, 17, 19, 25, 27, 30, 31, 33, 35, 36, 37, 39, 40, 42, 44, 46, 47, 48, 49, 51, 52, 56, 57, 58, 64, 67, 68, 71, 75, 76, 81, 82, 86, 89, 90, 93, 99, 100, 101, 105, 106, 108, 109, 110, 111, 113, 115, 117, 118, 120, 121, 122, 124, 126, 127, 130, 132, 138, 140, 141, 143, 144, 145, 146, 147, 148, 153, 154, 156, 157][i.val]!)

def pointPosition (i : Fin 158) : Fin 79 ⊕ Fin 79 :=
  let j : ℕ := #[0, 79, 1, 80, 81, 2, 3, 4, 5, 82, 83, 84, 85, 86, 87, 6, 88, 89, 7, 90, 8, 9, 10, 11, 12, 91, 13, 92, 14, 15, 93, 94, 16, 95, 17, 96, 97, 98, 18, 99, 100, 19, 101, 20, 102, 21, 103, 104, 105, 106, 22, 107, 108, 23, 24, 25, 109, 110, 111, 26, 27, 28, 29, 30, 112, 31, 32, 113, 114, 33, 34, 115, 35, 36, 37, 116, 117, 38, 39, 40, 41, 118, 119, 42, 43, 44, 120, 45, 46, 121, 122, 47, 48, 123, 49, 50, 51, 52, 53, 124, 125, 126, 54, 55, 56, 127, 128, 57, 129, 130, 131, 132, 58, 133, 59, 134, 60, 135, 136, 61, 137, 138, 139, 62, 140, 63, 141, 142, 64, 65, 143, 66, 144, 67, 68, 69, 70, 71, 145, 72, 146, 147, 73, 148, 149, 150, 151, 152, 153, 74, 75, 76, 77, 154, 155, 78, 156, 157][i.val]!
  if j<79 then .inl (Fin.ofNat 79 j) else .inr (Fin.ofNat 79 (j-79))

def indexing : (Fin 79 ⊕ Fin 79) ≃ Fin 158 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 79,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*157)*(157-1)^78) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 78 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 78 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 78=(2*157)*(157-1)^78 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquares


namespace NonsplitNegative
def rawWords (i : ℕ) : ℕ := #[435264348348529004893242, 265035043873930265968865, 530959771733625853153768, 459206858535676633564037, 313927886138631715128097, 7000570279667271732375, 51475418414988930125062, 103237332255240747621934, 18466964378625188313180, 225827499347260661592216, 295221979771299128459489, 440811099787924742443488, 592995150430515943918469, 543746437013444672848640, 520812214276803287717387, 550206125417739525041173, 401496156234697879074903, 161048134086166057611406, 237628497900920667996541, 351985456568587401757685, 12238833114253248703419, 387472605852689990196898, 228774027124543446343377, 232124306783897090947890, 55440364290482628845204, 109720885263770503588099, 29341454727446419165740, 419884047229517664839820, 490780087483001901293744, 146373441775278478739777, 279093994136399538361622, 597140372449747130526214, 552358921119835560428588, 179329825812191550480999, 575462701412255453741626, 434285695028707347010686, 521006693248233216449530, 281195487068269213771627, 563569979434603074211550, 430305923235361774059129, 143972345022947337402587, 582978806749312951577326, 410396640430326859289053, 452627784671127258516086, 595761662670485159505882, 435650044502659933133726, 482964548882136555233189, 246204012224954771107630, 454904493404101857562238, 494236560430231198734556, 12144601051460621795193, 61471821064677409732582, 231815703873098783627034, 246942211372125345377376, 304994073320036400880873, 195897948262890407902672, 363001546825485067936908, 54198111158364161150477, 328078410254576503959626, 443094613904809805146433, 225507629080755408507219, 295176478730012134705741, 533886927166312575031364, 501090883152301913317547, 189856538209476295868719, 379712658685957739025015, 3574730310630985770190, 159726295278539894311359, 35594133521359474924218, 33112374715696562577789, 118319695714116394306548, 274417891840008782387136, 550014937511778735700904, 456606636795620384204624, 496738331467622165634689, 22463201217018952441411, 159424269996605340761223, 111158977482102028039694, 33108249673326356199453][i]!
def words (i : Fin 79) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301, 301]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 79 rawWords i=rowTotals i)

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
private theorem row75 : rowAgrees 75=true := by decide +kernel
private theorem row76 : rowAgrees 76=true := by decide +kernel
private theorem row77 : rowAgrees 77=true := by decide +kernel
private theorem row78 : rowAgrees 78=true := by decide +kernel
private theorem rowChecked : allBelow 79 rowAgrees=true := by
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
  have h := allBelow_step h row75
  have h := allBelow_step h row76
  have h := allBelow_step h row77
  have h := allBelow_step h row78
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 79, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 79, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(5214:ℤ) := by
  change cubicInteger (fun i : Fin 79 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(5214:ℤ) ∧
    87*(79:ℤ)^3+375*79*(4*79-3)+1000*((wordMatrix words-1)^3).trace-
      1110*157*(79-1)=(43787958:ℤ) ∧ 0≤(43787958:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 79 ⊕ Fin 79 → Fin 158
  | .inl i => Fin.ofNat 158 (#[0, 2, 3, 5, 6, 8, 9, 10, 11, 12, 15, 16, 18, 19, 20, 21, 24, 25, 29, 32, 34, 36, 38, 40, 44, 45, 46, 48, 51, 54, 56, 57, 58, 62, 67, 68, 71, 74, 75, 78, 79, 82, 83, 86, 89, 90, 95, 99, 100, 101, 103, 106, 109, 111, 112, 113, 117, 119, 121, 123, 125, 128, 132, 133, 136, 137, 138, 139, 141, 142, 145, 146, 147, 148, 149, 151, 152, 154, 155][i.val]!)
  | .inr i => Fin.ofNat 158 (#[1, 4, 7, 13, 14, 17, 22, 23, 26, 27, 28, 30, 31, 33, 35, 37, 39, 41, 42, 43, 47, 49, 50, 52, 53, 55, 59, 60, 61, 63, 64, 65, 66, 69, 70, 72, 73, 76, 77, 80, 81, 84, 85, 87, 88, 91, 92, 93, 94, 96, 97, 98, 102, 104, 105, 107, 108, 110, 114, 115, 116, 118, 120, 122, 124, 126, 127, 129, 130, 131, 134, 135, 140, 143, 144, 150, 153, 156, 157][i.val]!)

def pointPosition (i : Fin 158) : Fin 79 ⊕ Fin 79 :=
  let j : ℕ := #[0, 79, 1, 2, 80, 3, 4, 81, 5, 6, 7, 8, 9, 82, 83, 10, 11, 84, 12, 13, 14, 15, 85, 86, 16, 17, 87, 88, 89, 18, 90, 91, 19, 92, 20, 93, 21, 94, 22, 95, 23, 96, 97, 98, 24, 25, 26, 99, 27, 100, 101, 28, 102, 103, 29, 104, 30, 31, 32, 105, 106, 107, 33, 108, 109, 110, 111, 34, 35, 112, 113, 36, 114, 115, 37, 38, 116, 117, 39, 40, 118, 119, 41, 42, 120, 121, 43, 122, 123, 44, 45, 124, 125, 126, 127, 46, 128, 129, 130, 47, 48, 49, 131, 50, 132, 133, 51, 134, 135, 52, 136, 53, 54, 55, 137, 138, 139, 56, 140, 57, 141, 58, 142, 59, 143, 60, 144, 145, 61, 146, 147, 148, 62, 63, 149, 150, 64, 65, 66, 67, 151, 68, 69, 152, 153, 70, 71, 72, 73, 74, 154, 75, 76, 155, 77, 78, 156, 157][i.val]!
  if j<79 then .inl (Fin.ofNat 79 j) else .inr (Fin.ofNat 79 (j-79))

def indexing : (Fin 79 ⊕ Fin 79) ≃ Fin 158 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 79,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*157)*(157-1)^78) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 78 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 78 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 78=(2*157)*(157-1)^78 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegative


namespace SplitSquaresOpposite
def rawWords (i : ℕ) : ℕ := #[117880215227847738474136, 159021556973355141788808, 159882612747839295715600, 15056358801202616754723, 27854792680041762386981, 141875310343111968688024, 275231077810522225515648, 201441893225393327845987, 256575372448212207825956, 208547154366488362117289, 121902240888577379426675, 236756753616255157588549, 203165870439163069049303, 42842218992954268784543, 76266871016808431816478, 192320762554411055781908, 20731244300696184746007, 100302718738983670023396, 155650593113503024354792, 174038904353801717032867, 93966962811470434930441, 82009234837181231070026, 219119601444885441464624, 150207048156686533636736, 149304205192409963943171, 216783157359080357888326, 268242487240088943309358, 239036125873754413647069, 36504612856366006479129, 214681517235502208336593, 112650827976604412283559, 69430776022129438336270, 92597420611708657612860, 187555015728921529729210, 299247736712928057573965, 140429095189650081096920, 118014378137982008838579, 226120214344990392422010, 287007969750907539696758, 130104987595384276080847, 111499539235006001975805, 242694863240100651888582, 32047444023658383495022, 210453517064767606398655, 109810667227457937062777, 70965653245945609680498, 132991088720210307773276, 270725503957571675019002, 164409931533557497719725, 180136520432578366658424, 220934127638860455026259, 137307394531587707874503, 116290059406935464802797, 227464607662445190508158, 1538005779435460975870, 14846331226509140793757, 97837360408289072344738, 171113550053611794065906, 233629960912170508441289, 27930971273130540723137, 46195735762305946070826, 273967037955878139130248, 47337942636829479495493, 142780223503459982088450, 295039911785623576875556, 278129155755720894408757, 191601971952306454155539, 243822011731718481543910, 176010133680901669692685, 42714566941950757816987, 234109666239281062806869, 1440653403950243677335, 30549864276859053814814, 193836118943846663985640, 231719572394002113823536, 10181457944654257370849, 20284877235569195896161, 30089388902489279732678, 0][i]!
def words (i : Fin 79) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 193, 313]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 79 rawWords i=rowTotals i)

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
private theorem row75 : rowAgrees 75=true := by decide +kernel
private theorem row76 : rowAgrees 76=true := by decide +kernel
private theorem row77 : rowAgrees 77=true := by decide +kernel
private theorem row78 : rowAgrees 78=true := by decide +kernel
private theorem rowChecked : allBelow 79 rowAgrees=true := by
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
  have h := allBelow_step h row75
  have h := allBelow_step h row76
  have h := allBelow_step h row77
  have h := allBelow_step h row78
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 79, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 79, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-3198:ℤ) := by
  change cubicInteger (fun i : Fin 79 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-3198:ℤ) ∧
    87*(79:ℤ)^3+375*79*(4*79-3)+1000*((wordMatrix words-1)^3).trace-
      1110*157*(79-1)=(35375958:ℤ) ∧ 0≤(35375958:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 79 ⊕ Fin 79 → Fin 158
  | .inl i => Fin.ofNat 158 (#[2, 5, 6, 7, 8, 15, 18, 20, 21, 22, 23, 24, 26, 28, 29, 32, 34, 38, 41, 43, 45, 50, 53, 54, 55, 59, 60, 61, 62, 63, 65, 66, 69, 70, 72, 73, 74, 77, 78, 79, 80, 83, 84, 85, 87, 88, 91, 92, 94, 95, 96, 97, 98, 102, 103, 104, 107, 112, 114, 116, 119, 123, 125, 128, 129, 131, 133, 134, 135, 136, 137, 139, 142, 149, 150, 151, 152, 155, 157][i.val]!)
  | .inr i => Fin.ofNat 158 (#[0, 1, 3, 4, 9, 10, 11, 12, 13, 14, 16, 17, 19, 25, 27, 30, 31, 33, 35, 36, 37, 39, 40, 42, 44, 46, 47, 48, 49, 51, 52, 56, 57, 58, 64, 67, 68, 71, 75, 76, 81, 82, 86, 89, 90, 93, 99, 100, 101, 105, 106, 108, 109, 110, 111, 113, 115, 117, 118, 120, 121, 122, 124, 126, 127, 130, 132, 138, 140, 141, 143, 144, 145, 146, 147, 148, 153, 154, 156][i.val]!)

def pointPosition (i : Fin 158) : Fin 79 ⊕ Fin 79 :=
  let j : ℕ := #[79, 80, 0, 81, 82, 1, 2, 3, 4, 83, 84, 85, 86, 87, 88, 5, 89, 90, 6, 91, 7, 8, 9, 10, 11, 92, 12, 93, 13, 14, 94, 95, 15, 96, 16, 97, 98, 99, 17, 100, 101, 18, 102, 19, 103, 20, 104, 105, 106, 107, 21, 108, 109, 22, 23, 24, 110, 111, 112, 25, 26, 27, 28, 29, 113, 30, 31, 114, 115, 32, 33, 116, 34, 35, 36, 117, 118, 37, 38, 39, 40, 119, 120, 41, 42, 43, 121, 44, 45, 122, 123, 46, 47, 124, 48, 49, 50, 51, 52, 125, 126, 127, 53, 54, 55, 128, 129, 56, 130, 131, 132, 133, 57, 134, 58, 135, 59, 136, 137, 60, 138, 139, 140, 61, 141, 62, 142, 143, 63, 64, 144, 65, 145, 66, 67, 68, 69, 70, 146, 71, 147, 148, 72, 149, 150, 151, 152, 153, 154, 73, 74, 75, 76, 155, 156, 77, 157, 78][i.val]!
  if j<79 then .inl (Fin.ofNat 79 j) else .inr (Fin.ofNat 79 (j-79))

def indexing : (Fin 79 ⊕ Fin 79) ≃ Fin 158 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 79,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*157)*(157-1)^78) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 78 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 78 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 78=(2*157)*(157-1)^78 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquaresOpposite


namespace SplitNonsquaresOpposite
def rawWords (i : ℕ) : ℕ := #[189768989613975084956170, 115962111548674754129977, 270328254322435147790456, 28002762067860532225831, 18676267668556999939654, 74552718603687611305614, 112015592140459418807572, 34652622470466760575008, 220204206256535586605640, 51116393106319181906233, 290576350120744408717432, 294047581836578978805221, 284865961252013641690135, 156746214399746253199439, 43736931971884825579613, 239158775705610464596666, 163100306859585023684861, 85147202152272465847787, 19768919769952785843156, 190559314264663522463658, 43422729751065067622065, 238011951544703855566688, 235193439450909004147605, 184739195579453323084371, 58981640187249333146947, 80131313841540718147724, 9055008508890560166674, 207689206299383706989604, 149440348847824475389073, 261712885182176843841832, 143909660300585749405859, 136244710955524619737926, 272563282104364527666310, 181624555042555151403327, 93780730973868411520453, 224858490306449454166410, 250200686524804806297209, 145748177742155802498011, 290818186544681842870198, 129725636039866157673071, 259481429308341694770910, 186988204123774777669579, 96283643133827682299517, 193177939753463752619762, 298184260444345848687513, 114676275208250636204903, 116703220285329114851022, 232608258619042107402142, 24216283154704439424443, 162034498958330902161790, 42708883567490805192693, 86028814072478779233760, 57978370249961360980930, 229814386671626130927500, 238775711134247170825785, 200499776998183596387555, 8230758470267681986963, 166987164725770624164644, 101472278933834109490821, 51664773339269905087752, 254595440766362951809042, 225554323607035179787345, 110130387818187741907283, 219628955851721178337444, 285817356061301011850017, 274153294165462016217743, 197952558493702702925983, 35530097153667515614319, 184768337561965118894804, 21621721396773834236253, 4805274002361074342584, 48067126071511060940666, 133931938397606927951100, 116194512532812995988464, 270243940799607885536744, 35559023297078996000551, 184233715445870738185286, 94884494806987542478085, 0][i]!
def words (i : Fin 79) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 277, 157]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 79 rawWords i=rowTotals i)

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
private theorem row75 : rowAgrees 75=true := by decide +kernel
private theorem row76 : rowAgrees 76=true := by decide +kernel
private theorem row77 : rowAgrees 77=true := by decide +kernel
private theorem row78 : rowAgrees 78=true := by decide +kernel
private theorem rowChecked : allBelow 79 rowAgrees=true := by
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
  have h := allBelow_step h row75
  have h := allBelow_step h row76
  have h := allBelow_step h row77
  have h := allBelow_step h row78
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 79, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 79, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(3198:ℤ) := by
  change cubicInteger (fun i : Fin 79 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(3198:ℤ) ∧
    87*(79:ℤ)^3+375*79*(4*79-3)+1000*((wordMatrix words-1)^3).trace-
      1110*157*(79-1)=(41771958:ℤ) ∧ 0≤(41771958:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 79 ⊕ Fin 79 → Fin 158
  | .inl i => Fin.ofNat 158 (#[1, 3, 4, 9, 10, 11, 12, 13, 14, 16, 17, 19, 25, 27, 30, 31, 33, 35, 36, 37, 39, 40, 42, 44, 46, 47, 48, 49, 51, 52, 56, 57, 58, 64, 67, 68, 71, 75, 76, 81, 82, 86, 89, 90, 93, 99, 100, 101, 105, 106, 108, 109, 110, 111, 113, 115, 117, 118, 120, 121, 122, 124, 126, 127, 130, 132, 138, 140, 141, 143, 144, 145, 146, 147, 148, 153, 154, 156, 157][i.val]!)
  | .inr i => Fin.ofNat 158 (#[0, 2, 5, 6, 7, 8, 15, 18, 20, 21, 22, 23, 24, 26, 28, 29, 32, 34, 38, 41, 43, 45, 50, 53, 54, 55, 59, 60, 61, 62, 63, 65, 66, 69, 70, 72, 73, 74, 77, 78, 79, 80, 83, 84, 85, 87, 88, 91, 92, 94, 95, 96, 97, 98, 102, 103, 104, 107, 112, 114, 116, 119, 123, 125, 128, 129, 131, 133, 134, 135, 136, 137, 139, 142, 149, 150, 151, 152, 155][i.val]!)

def pointPosition (i : Fin 158) : Fin 79 ⊕ Fin 79 :=
  let j : ℕ := #[79, 0, 80, 1, 2, 81, 82, 83, 84, 3, 4, 5, 6, 7, 8, 85, 9, 10, 86, 11, 87, 88, 89, 90, 91, 12, 92, 13, 93, 94, 14, 15, 95, 16, 96, 17, 18, 19, 97, 20, 21, 98, 22, 99, 23, 100, 24, 25, 26, 27, 101, 28, 29, 102, 103, 104, 30, 31, 32, 105, 106, 107, 108, 109, 33, 110, 111, 34, 35, 112, 113, 36, 114, 115, 116, 37, 38, 117, 118, 119, 120, 39, 40, 121, 122, 123, 41, 124, 125, 42, 43, 126, 127, 44, 128, 129, 130, 131, 132, 45, 46, 47, 133, 134, 135, 48, 49, 136, 50, 51, 52, 53, 137, 54, 138, 55, 139, 56, 57, 140, 58, 59, 60, 141, 61, 142, 62, 63, 143, 144, 64, 145, 65, 146, 147, 148, 149, 150, 66, 151, 67, 68, 152, 69, 70, 71, 72, 73, 74, 153, 154, 155, 156, 75, 76, 157, 77, 78][i.val]!
  if j<79 then .inl (Fin.ofNat 79 j) else .inr (Fin.ofNat 79 (j-79))

def indexing : (Fin 79 ⊕ Fin 79) ≃ Fin 158 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 79,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*157)*(157-1)^78) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 78 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 78 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 78=(2*157)*(157-1)^78 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquaresOpposite


namespace NonsplitNegativeOpposite
def rawWords (i : ℕ) : ℕ := #[282664750845100663597764, 243431420787698802372416, 186865983993855590235737, 56896383215152261493764, 274232998790153435398212, 269936788005849265848512, 265844591173632386698807, 153890779912852003757089, 5200138305824634319874, 200584051313523935174727, 253603089688652694448590, 95769708921636094264519, 202153213806263633289612, 159332805011004104857359, 1160843077633153347133, 254599556335103309076600, 89571730944678532657197, 106464136806224807682476, 176477547864507676672603, 47054869513667017360624, 70675499078675618792330, 261181626547479513012130, 98539795870753705709380, 225413219560370281160084, 213516273969368845548032, 131294649869513268458417, 293559482421719672814098, 185847364302410858468709, 254857635717165823550085, 54522893187129610850379, 181205022715135289870739, 297350779501440149729858, 149608906714738743608463, 240721258799633681536278, 149811285702714984890919, 212036832655370489434732, 277553519040213701315743, 267884157627399425782270, 204037728286168733778678, 131343499729281869007669, 150590783965212469368647, 294201640456827506989271, 64084403499165323385293, 269472042029263224088446, 123571785175330039818195, 284675635010851615972734, 78278654065304336186335, 237974313911020134416025, 247979297516072248505460, 190406443735910102006763, 196760497911208917915321, 85444193459784114627871, 167418300718941831408886, 433651049211995577133, 49257601901482711283581, 41257030416922127560394, 82532899391627249671355, 96517503901944197069788, 17871545442773668125668, 257678210145099558346409, 63192135406651703145562, 212567744979655930903506, 35540849855706219603435, 222492862369430112165632, 284424598662051358027617, 58464756834286828477653, 268155772359014233241738, 136460204797476978750315, 266842221470679985645461, 75762206837615349065248, 156098028937226674346561, 279141645213381361906823, 3559434617331821356327, 40154839785929304117783, 37999860770692937452556, 182395696595721071891065, 3487230073506233551987, 41720200687824813733623, 0][i]!
def words (i : Fin 79) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 79 rawWords i=rowTotals i)

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
private theorem row75 : rowAgrees 75=true := by decide +kernel
private theorem row76 : rowAgrees 76=true := by decide +kernel
private theorem row77 : rowAgrees 77=true := by decide +kernel
private theorem row78 : rowAgrees 78=true := by decide +kernel
private theorem rowChecked : allBelow 79 rowAgrees=true := by
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
  have h := allBelow_step h row75
  have h := allBelow_step h row76
  have h := allBelow_step h row77
  have h := allBelow_step h row78
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 79, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 79, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-5214:ℤ) := by
  change cubicInteger (fun i : Fin 79 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-5214:ℤ) ∧
    87*(79:ℤ)^3+375*79*(4*79-3)+1000*((wordMatrix words-1)^3).trace-
      1110*157*(79-1)=(33359958:ℤ) ∧ 0≤(33359958:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 79 ⊕ Fin 79 → Fin 158
  | .inl i => Fin.ofNat 158 (#[1, 4, 7, 13, 14, 17, 22, 23, 26, 27, 28, 30, 31, 33, 35, 37, 39, 41, 42, 43, 47, 49, 50, 52, 53, 55, 59, 60, 61, 63, 64, 65, 66, 69, 70, 72, 73, 76, 77, 80, 81, 84, 85, 87, 88, 91, 92, 93, 94, 96, 97, 98, 102, 104, 105, 107, 108, 110, 114, 115, 116, 118, 120, 122, 124, 126, 127, 129, 130, 131, 134, 135, 140, 143, 144, 150, 153, 156, 157][i.val]!)
  | .inr i => Fin.ofNat 158 (#[0, 2, 3, 5, 6, 8, 9, 10, 11, 12, 15, 16, 18, 19, 20, 21, 24, 25, 29, 32, 34, 36, 38, 40, 44, 45, 46, 48, 51, 54, 56, 57, 58, 62, 67, 68, 71, 74, 75, 78, 79, 82, 83, 86, 89, 90, 95, 99, 100, 101, 103, 106, 109, 111, 112, 113, 117, 119, 121, 123, 125, 128, 132, 133, 136, 137, 138, 139, 141, 142, 145, 146, 147, 148, 149, 151, 152, 154, 155][i.val]!)

def pointPosition (i : Fin 158) : Fin 79 ⊕ Fin 79 :=
  let j : ℕ := #[79, 0, 80, 81, 1, 82, 83, 2, 84, 85, 86, 87, 88, 3, 4, 89, 90, 5, 91, 92, 93, 94, 6, 7, 95, 96, 8, 9, 10, 97, 11, 12, 98, 13, 99, 14, 100, 15, 101, 16, 102, 17, 18, 19, 103, 104, 105, 20, 106, 21, 22, 107, 23, 24, 108, 25, 109, 110, 111, 26, 27, 28, 112, 29, 30, 31, 32, 113, 114, 33, 34, 115, 35, 36, 116, 117, 37, 38, 118, 119, 39, 40, 120, 121, 41, 42, 122, 43, 44, 123, 124, 45, 46, 47, 48, 125, 49, 50, 51, 126, 127, 128, 52, 129, 53, 54, 130, 55, 56, 131, 57, 132, 133, 134, 58, 59, 60, 135, 61, 136, 62, 137, 63, 138, 64, 139, 65, 66, 140, 67, 68, 69, 141, 142, 70, 71, 143, 144, 145, 146, 72, 147, 148, 73, 74, 149, 150, 151, 152, 153, 75, 154, 155, 76, 156, 157, 77, 78][i.val]!
  if j<79 then .inl (Fin.ofNat 79 j) else .inr (Fin.ofNat 79 (j-79))

def indexing : (Fin 79 ⊕ Fin 79) ≃ Fin 158 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 79,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*157)*(157-1)^78) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 78 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 78 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 78=(2*157)*(157-1)^78 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegativeOpposite

end PaleyBits157
