import Quantum.Hadamard.ConferenceBitCompletion
open Hadamard.BitTrace Hadamard.DeterminantRatio Matrix
set_option maxHeartbeats 12000000
set_option maxRecDepth 60000
namespace PaleyBits89

def rawFull (i : ℕ) : ℕ := #[92163013807473543562719432, 184326027614947087125438864, 368652055229894174250877728, 118334090817098211052193345, 236668181634196422104386690, 473336363268392844208773380, 327702706894095550967984649, 36435394145500964486407187, 72870788291001928972814374, 145741576582003857945628748, 291483153164007715891257496, 582966306328015431782514992, 546962593013340726115467873, 474955166383991314781373635, 330940313125292492113185159, 42910606607894846776808207, 85821213215789693553616414, 171642426431579387107232828, 343284852863158774214465656, 67599686083627410979369201, 135199372167254821958738402, 270398744334509643917476804, 540797488669019287834953608, 462624957695348438220345105, 306279895748006738991128099, 612559791496013477982256198, 606149563349336818514950285, 593329107055983499580338459, 567688194469276861711114807, 516406369295863585972667503, 413842718949037034495772895, 208715418255383931541983679, 417430836510767863083967358, 215891653378845588718372605, 431783306757691177436745210, 244596593872692217423928309, 489193187745384434847856618, 359416355848078732246151125, 99862692053467327042740139, 199725384106934654085480278, 399450768213869308170960556, 179931516785048478892359001, 359863033570096957784718002, 100756047497503778119873893, 201512094995007556239747786, 403024189990015112479495572, 187078360337340087509429033, 374156720674680175018858066, 129343421706670212588154021, 258686843413340425176308042, 517373686826680850352616084, 415777354010671563255670057, 212584688378652989061778003, 425169376757305978123556006, 231368733871921818797549901, 462737467743843637595099802, 306504915844997137740637493, 613009831689994275481274986, 607049643737298413512987861, 595129267831906689576413611, 571288516021123241703265111, 523607012399556345956968111, 428244005156422554464374111, 237517990670154971479186111, 475035981340309942958372222, 331101943037929748467182333, 43233866433169359484802555, 86467732866338718969605110, 172935465732677437939210220, 345870931465354875878420440, 72771843288019614307278769, 145543686576039228614557538, 291087373152078457229115076, 582174746304156914458230152, 545379472965623691466898193, 471788926288557245484234275, 324607832934424353518906439, 30245646226158569588250767, 60491292452317139176501534, 120982584904634278353003068, 241965169809268556706006136, 483930339618537113412012272, 348890659594384089374462433, 78811299546078041299362755, 157622599092156082598725510, 315245198184312165197451020, 11520376725934192945339929, 23040753451868385890679858, 46081506903736771781359716, 0][i]!
def fullRows (i : Fin 90) : ℕ := rawFull i.val

private theorem fullSymmetric : (wordMatrix fullRows).IsSymm := by
  have h : ∀ i j : Fin 90, sign (fullRows i) j.val=sign (fullRows j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem fullDiagonal : ∀ i : Fin 90, sign (fullRows i) i.val=1 := by decide +kernel
private theorem lower0 : (lowerRow 90 rawFull) 0=true := by decide +kernel
private theorem lower1 : (lowerRow 90 rawFull) 1=true := by decide +kernel
private theorem lower2 : (lowerRow 90 rawFull) 2=true := by decide +kernel
private theorem lower3 : (lowerRow 90 rawFull) 3=true := by decide +kernel
private theorem lower4 : (lowerRow 90 rawFull) 4=true := by decide +kernel
private theorem lower5 : (lowerRow 90 rawFull) 5=true := by decide +kernel
private theorem lower6 : (lowerRow 90 rawFull) 6=true := by decide +kernel
private theorem lower7 : (lowerRow 90 rawFull) 7=true := by decide +kernel
private theorem lower8 : (lowerRow 90 rawFull) 8=true := by decide +kernel
private theorem lower9 : (lowerRow 90 rawFull) 9=true := by decide +kernel
private theorem lower10 : (lowerRow 90 rawFull) 10=true := by decide +kernel
private theorem lower11 : (lowerRow 90 rawFull) 11=true := by decide +kernel
private theorem lower12 : (lowerRow 90 rawFull) 12=true := by decide +kernel
private theorem lower13 : (lowerRow 90 rawFull) 13=true := by decide +kernel
private theorem lower14 : (lowerRow 90 rawFull) 14=true := by decide +kernel
private theorem lower15 : (lowerRow 90 rawFull) 15=true := by decide +kernel
private theorem lower16 : (lowerRow 90 rawFull) 16=true := by decide +kernel
private theorem lower17 : (lowerRow 90 rawFull) 17=true := by decide +kernel
private theorem lower18 : (lowerRow 90 rawFull) 18=true := by decide +kernel
private theorem lower19 : (lowerRow 90 rawFull) 19=true := by decide +kernel
private theorem lower20 : (lowerRow 90 rawFull) 20=true := by decide +kernel
private theorem lower21 : (lowerRow 90 rawFull) 21=true := by decide +kernel
private theorem lower22 : (lowerRow 90 rawFull) 22=true := by decide +kernel
private theorem lower23 : (lowerRow 90 rawFull) 23=true := by decide +kernel
private theorem lower24 : (lowerRow 90 rawFull) 24=true := by decide +kernel
private theorem lower25 : (lowerRow 90 rawFull) 25=true := by decide +kernel
private theorem lower26 : (lowerRow 90 rawFull) 26=true := by decide +kernel
private theorem lower27 : (lowerRow 90 rawFull) 27=true := by decide +kernel
private theorem lower28 : (lowerRow 90 rawFull) 28=true := by decide +kernel
private theorem lower29 : (lowerRow 90 rawFull) 29=true := by decide +kernel
private theorem lower30 : (lowerRow 90 rawFull) 30=true := by decide +kernel
private theorem lower31 : (lowerRow 90 rawFull) 31=true := by decide +kernel
private theorem lower32 : (lowerRow 90 rawFull) 32=true := by decide +kernel
private theorem lower33 : (lowerRow 90 rawFull) 33=true := by decide +kernel
private theorem lower34 : (lowerRow 90 rawFull) 34=true := by decide +kernel
private theorem lower35 : (lowerRow 90 rawFull) 35=true := by decide +kernel
private theorem lower36 : (lowerRow 90 rawFull) 36=true := by decide +kernel
private theorem lower37 : (lowerRow 90 rawFull) 37=true := by decide +kernel
private theorem lower38 : (lowerRow 90 rawFull) 38=true := by decide +kernel
private theorem lower39 : (lowerRow 90 rawFull) 39=true := by decide +kernel
private theorem lower40 : (lowerRow 90 rawFull) 40=true := by decide +kernel
private theorem lower41 : (lowerRow 90 rawFull) 41=true := by decide +kernel
private theorem lower42 : (lowerRow 90 rawFull) 42=true := by decide +kernel
private theorem lower43 : (lowerRow 90 rawFull) 43=true := by decide +kernel
private theorem lower44 : (lowerRow 90 rawFull) 44=true := by decide +kernel
private theorem lower45 : (lowerRow 90 rawFull) 45=true := by decide +kernel
private theorem lower46 : (lowerRow 90 rawFull) 46=true := by decide +kernel
private theorem lower47 : (lowerRow 90 rawFull) 47=true := by decide +kernel
private theorem lower48 : (lowerRow 90 rawFull) 48=true := by decide +kernel
private theorem lower49 : (lowerRow 90 rawFull) 49=true := by decide +kernel
private theorem lower50 : (lowerRow 90 rawFull) 50=true := by decide +kernel
private theorem lower51 : (lowerRow 90 rawFull) 51=true := by decide +kernel
private theorem lower52 : (lowerRow 90 rawFull) 52=true := by decide +kernel
private theorem lower53 : (lowerRow 90 rawFull) 53=true := by decide +kernel
private theorem lower54 : (lowerRow 90 rawFull) 54=true := by decide +kernel
private theorem lower55 : (lowerRow 90 rawFull) 55=true := by decide +kernel
private theorem lower56 : (lowerRow 90 rawFull) 56=true := by decide +kernel
private theorem lower57 : (lowerRow 90 rawFull) 57=true := by decide +kernel
private theorem lower58 : (lowerRow 90 rawFull) 58=true := by decide +kernel
private theorem lower59 : (lowerRow 90 rawFull) 59=true := by decide +kernel
private theorem lower60 : (lowerRow 90 rawFull) 60=true := by decide +kernel
private theorem lower61 : (lowerRow 90 rawFull) 61=true := by decide +kernel
private theorem lower62 : (lowerRow 90 rawFull) 62=true := by decide +kernel
private theorem lower63 : (lowerRow 90 rawFull) 63=true := by decide +kernel
private theorem lower64 : (lowerRow 90 rawFull) 64=true := by decide +kernel
private theorem lower65 : (lowerRow 90 rawFull) 65=true := by decide +kernel
private theorem lower66 : (lowerRow 90 rawFull) 66=true := by decide +kernel
private theorem lower67 : (lowerRow 90 rawFull) 67=true := by decide +kernel
private theorem lower68 : (lowerRow 90 rawFull) 68=true := by decide +kernel
private theorem lower69 : (lowerRow 90 rawFull) 69=true := by decide +kernel
private theorem lower70 : (lowerRow 90 rawFull) 70=true := by decide +kernel
private theorem lower71 : (lowerRow 90 rawFull) 71=true := by decide +kernel
private theorem lower72 : (lowerRow 90 rawFull) 72=true := by decide +kernel
private theorem lower73 : (lowerRow 90 rawFull) 73=true := by decide +kernel
private theorem lower74 : (lowerRow 90 rawFull) 74=true := by decide +kernel
private theorem lower75 : (lowerRow 90 rawFull) 75=true := by decide +kernel
private theorem lower76 : (lowerRow 90 rawFull) 76=true := by decide +kernel
private theorem lower77 : (lowerRow 90 rawFull) 77=true := by decide +kernel
private theorem lower78 : (lowerRow 90 rawFull) 78=true := by decide +kernel
private theorem lower79 : (lowerRow 90 rawFull) 79=true := by decide +kernel
private theorem lower80 : (lowerRow 90 rawFull) 80=true := by decide +kernel
private theorem lower81 : (lowerRow 90 rawFull) 81=true := by decide +kernel
private theorem lower82 : (lowerRow 90 rawFull) 82=true := by decide +kernel
private theorem lower83 : (lowerRow 90 rawFull) 83=true := by decide +kernel
private theorem lower84 : (lowerRow 90 rawFull) 84=true := by decide +kernel
private theorem lower85 : (lowerRow 90 rawFull) 85=true := by decide +kernel
private theorem lower86 : (lowerRow 90 rawFull) 86=true := by decide +kernel
private theorem lower87 : (lowerRow 90 rawFull) 87=true := by decide +kernel
private theorem lower88 : (lowerRow 90 rawFull) 88=true := by decide +kernel
private theorem lower89 : (lowerRow 90 rawFull) 89=true := by decide +kernel
private theorem lowerChecked : allBelow 90 (lowerRow 90 rawFull)=true := by
  have h : allBelow 0 (lowerRow 90 rawFull)=true := rfl
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
  exact h

private theorem fullPairs : ∀ i j : Fin 90, i≠j →
    correlation 90 (fullRows i) (fullRows j)=2*sign (fullRows i) j.val :=
  correlations_of_lower rawFull fullSymmetric lowerChecked


namespace SplitSquares
def rawWords (i : ℕ) : ℕ := #[0, 11153953493544, 24643659998832, 10869852016514, 28337795177764, 6836557148438, 6939417076228, 16077297731080, 32017412164664, 1554442109134, 9857316229532, 21897284788504, 6516527268914, 13034283468900, 34846118675168, 34450374740358, 20558159322238, 22604061635002, 28960262481138, 13793432540142, 18931561703380, 22948858301274, 14695851474754, 18414138125996, 24962556706506, 12065907866402, 32926985385036, 21756242483862, 25716153769034, 34695901500242, 26820570655422, 1994347455358, 10462992848628, 20925965610472, 6740447237618, 15814789577668, 31613240337824, 7749590146606, 4504856870492, 8872054717592, 28740785601304, 10094163388646, 18125658182116, 3957381195162, 5576976746772][i]!
def words (i : Fin 45) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[89, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 45 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 45 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 45, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 45, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-924:ℤ) := by
  change cubicInteger (fun i : Fin 45 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-924:ℤ) ∧
    87*(45:ℤ)^3+375*45*(4*45-3)+1000*((wordMatrix words-1)^3).trace-
      1110*89*(45-1)=(5643990:ℤ) ∧ 0≤(5643990:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 45 ⊕ Fin 45 → Fin 90
  | .inl i => Fin.ofNat 90 (#[0, 1, 2, 4, 5, 8, 9, 10, 11, 16, 17, 18, 20, 21, 22, 25, 32, 34, 36, 39, 40, 42, 44, 45, 47, 49, 50, 53, 55, 57, 64, 67, 68, 69, 71, 72, 73, 78, 79, 80, 81, 84, 85, 87, 88][i.val]!)
  | .inr i => Fin.ofNat 90 (#[3, 6, 7, 12, 13, 14, 15, 19, 23, 24, 26, 27, 28, 29, 30, 31, 33, 35, 37, 38, 41, 43, 46, 48, 51, 52, 54, 56, 58, 59, 60, 61, 62, 63, 65, 66, 70, 74, 75, 76, 77, 82, 83, 86, 89][i.val]!)

def pointPosition (i : Fin 90) : Fin 45 ⊕ Fin 45 :=
  let j : ℕ := #[0, 1, 2, 45, 3, 4, 46, 47, 5, 6, 7, 8, 48, 49, 50, 51, 9, 10, 11, 52, 12, 13, 14, 53, 54, 15, 55, 56, 57, 58, 59, 60, 16, 61, 17, 62, 18, 63, 64, 19, 20, 65, 21, 66, 22, 23, 67, 24, 68, 25, 26, 69, 70, 27, 71, 28, 72, 29, 73, 74, 75, 76, 77, 78, 30, 79, 80, 31, 32, 33, 81, 34, 35, 36, 82, 83, 84, 85, 37, 38, 39, 40, 86, 87, 41, 42, 88, 43, 44, 89][i.val]!
  if j<45 then .inl (Fin.ofNat 45 j) else .inr (Fin.ofNat 45 (j-45))

def indexing : (Fin 45 ⊕ Fin 45) ≃ Fin 90 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 45,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*89)*(89-1)^44) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 44 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 44 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 44=(2*89)*(89-1)^44 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquares


namespace SplitNonsquares
def rawWords (i : ℕ) : ℕ := #[35184372088830, 19925606586501, 14408213250355, 15656785250657, 25239919861125, 10760435022093, 4374532880393, 4214267899923, 7329862060093, 33886194944001, 32621607882769, 24487155352443, 27121554719987, 23491296690401, 11763737430727, 23149744363151, 15753551553819, 1614194710863, 27760138412573, 9885240624749, 19357520695259, 5946802993399, 19182138287605, 13099184886691, 30543830205865, 25272277022307, 14948106923973, 15468377521959, 31500370901921, 24365463106205, 31173217086507, 27298974389077, 1924843679403, 21751079064903, 26047148894363, 2209336833391, 20642226911, 16510708766041, 19807381170929, 4430654625777, 13361743308005, 9269269318619, 1806002401053, 21031876908589, 9100823150099][i]!
def words (i : Fin 45) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[177, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 45 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 45 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 45, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 45, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(924:ℤ) := by
  change cubicInteger (fun i : Fin 45 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(924:ℤ) ∧
    87*(45:ℤ)^3+375*45*(4*45-3)+1000*((wordMatrix words-1)^3).trace-
      1110*89*(45-1)=(7491990:ℤ) ∧ 0≤(7491990:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 45 ⊕ Fin 45 → Fin 90
  | .inl i => Fin.ofNat 90 (#[0, 3, 6, 7, 12, 13, 14, 15, 19, 23, 24, 26, 27, 28, 29, 30, 31, 33, 35, 37, 38, 41, 43, 46, 48, 51, 52, 54, 56, 58, 59, 60, 61, 62, 63, 65, 66, 70, 74, 75, 76, 77, 82, 83, 86][i.val]!)
  | .inr i => Fin.ofNat 90 (#[1, 2, 4, 5, 8, 9, 10, 11, 16, 17, 18, 20, 21, 22, 25, 32, 34, 36, 39, 40, 42, 44, 45, 47, 49, 50, 53, 55, 57, 64, 67, 68, 69, 71, 72, 73, 78, 79, 80, 81, 84, 85, 87, 88, 89][i.val]!)

def pointPosition (i : Fin 90) : Fin 45 ⊕ Fin 45 :=
  let j : ℕ := #[0, 45, 46, 1, 47, 48, 2, 3, 49, 50, 51, 52, 4, 5, 6, 7, 53, 54, 55, 8, 56, 57, 58, 9, 10, 59, 11, 12, 13, 14, 15, 16, 60, 17, 61, 18, 62, 19, 20, 63, 64, 21, 65, 22, 66, 67, 23, 68, 24, 69, 70, 25, 26, 71, 27, 72, 28, 73, 29, 30, 31, 32, 33, 34, 74, 35, 36, 75, 76, 77, 37, 78, 79, 80, 38, 39, 40, 41, 81, 82, 83, 84, 42, 43, 85, 86, 44, 87, 88, 89][i.val]!
  if j<45 then .inl (Fin.ofNat 45 j) else .inr (Fin.ofNat 45 (j-45))

def indexing : (Fin 45 ⊕ Fin 45) ≃ Fin 90 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 45,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*89)*(89-1)^44) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 44 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 44 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 44=(2*89)*(89-1)^44 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquares


namespace NonsplitNegative
def rawWords (i : ℕ) : ℕ := #[24672420725658, 27255201045513, 19247447055440, 7868067574147, 8029746389765, 15994338468416, 27966121581092, 20747400810505, 5218837767193, 536425916529, 21942348742918, 7678056407622, 6481436623054, 34800035728184, 25689793532472, 32542576239527, 14656415731211, 21623959231583, 23832156005629, 13832550486909, 2919152065519, 13604477179860, 19444399812521, 6035305708899, 12070872710796, 32944147495249, 17257456028237, 17358701120875, 33596400686451, 22110686382765, 27975592822383, 7775102873274, 7921143404926, 31613500140008, 27011904796632, 26526689446898, 3873652199297, 6636929695561, 4407905312467, 9990620233126, 626239468636, 9009181650105, 18020586879289, 2810505175138, 4460093301959][i]!
def words (i : Fin 45) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173, 173]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 45 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 45 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 45, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 45, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(1800:ℤ) := by
  change cubicInteger (fun i : Fin 45 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(1800:ℤ) ∧
    87*(45:ℤ)^3+375*45*(4*45-3)+1000*((wordMatrix words-1)^3).trace-
      1110*89*(45-1)=(8367990:ℤ) ∧ 0≤(8367990:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 45 ⊕ Fin 45 → Fin 90
  | .inl i => Fin.ofNat 90 (#[0, 3, 4, 6, 7, 8, 11, 12, 13, 14, 16, 17, 18, 20, 21, 27, 29, 30, 35, 37, 41, 42, 43, 46, 47, 48, 52, 54, 59, 60, 62, 68, 69, 71, 72, 73, 75, 76, 77, 78, 81, 82, 83, 85, 86][i.val]!)
  | .inr i => Fin.ofNat 90 (#[1, 2, 5, 9, 10, 15, 19, 22, 23, 24, 25, 26, 28, 31, 32, 33, 34, 36, 38, 39, 40, 44, 45, 49, 50, 51, 53, 55, 56, 57, 58, 61, 63, 64, 65, 66, 67, 70, 74, 79, 80, 84, 87, 88, 89][i.val]!)

def pointPosition (i : Fin 90) : Fin 45 ⊕ Fin 45 :=
  let j : ℕ := #[0, 45, 46, 1, 2, 47, 3, 4, 5, 48, 49, 6, 7, 8, 9, 50, 10, 11, 12, 51, 13, 14, 52, 53, 54, 55, 56, 15, 57, 16, 17, 58, 59, 60, 61, 18, 62, 19, 63, 64, 65, 20, 21, 22, 66, 67, 23, 24, 25, 68, 69, 70, 26, 71, 27, 72, 73, 74, 75, 28, 29, 76, 30, 77, 78, 79, 80, 81, 31, 32, 82, 33, 34, 35, 83, 36, 37, 38, 39, 84, 85, 40, 41, 42, 86, 43, 44, 87, 88, 89][i.val]!
  if j<45 then .inl (Fin.ofNat 45 j) else .inr (Fin.ofNat 45 (j-45))

def indexing : (Fin 45 ⊕ Fin 45) ≃ Fin 90 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 45,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*89)*(89-1)^44) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 44 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 44 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 44=(2*89)*(89-1)^44 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegative


namespace SplitSquaresOpposite
def rawWords (i : ℕ) : ℕ := #[9962803293250, 7204106625177, 7828392625328, 12619959930562, 5380217511046, 2187266440196, 2107133949961, 3664931030046, 16943097472000, 16310803941384, 12243577676221, 13560777359993, 11745648345200, 5881868715363, 11574872181575, 7876775776909, 807097355431, 13880069206286, 4942620312374, 9678760347629, 2973401496699, 9591069143802, 6549592443345, 15271915102932, 12636138511153, 7474053461986, 7734188760979, 15750185450960, 12182731553102, 15586608543253, 13649487194538, 962421839701, 10875539532451, 13023574447181, 1104668416695, 10321113455, 8255354383020, 9903690585464, 2215327312888, 6680871654002, 4634634659309, 903001200526, 10515938454294, 4550411575049, 0][i]!
def words (i : Fin 45) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 153, 177]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 45 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 45 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 45, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 45, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(924:ℤ) := by
  change cubicInteger (fun i : Fin 45 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(924:ℤ) ∧
    87*(45:ℤ)^3+375*45*(4*45-3)+1000*((wordMatrix words-1)^3).trace-
      1110*89*(45-1)=(7491990:ℤ) ∧ 0≤(7491990:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 45 ⊕ Fin 45 → Fin 90
  | .inl i => Fin.ofNat 90 (#[3, 6, 7, 12, 13, 14, 15, 19, 23, 24, 26, 27, 28, 29, 30, 31, 33, 35, 37, 38, 41, 43, 46, 48, 51, 52, 54, 56, 58, 59, 60, 61, 62, 63, 65, 66, 70, 74, 75, 76, 77, 82, 83, 86, 89][i.val]!)
  | .inr i => Fin.ofNat 90 (#[0, 1, 2, 4, 5, 8, 9, 10, 11, 16, 17, 18, 20, 21, 22, 25, 32, 34, 36, 39, 40, 42, 44, 45, 47, 49, 50, 53, 55, 57, 64, 67, 68, 69, 71, 72, 73, 78, 79, 80, 81, 84, 85, 87, 88][i.val]!)

def pointPosition (i : Fin 90) : Fin 45 ⊕ Fin 45 :=
  let j : ℕ := #[45, 46, 47, 0, 48, 49, 1, 2, 50, 51, 52, 53, 3, 4, 5, 6, 54, 55, 56, 7, 57, 58, 59, 8, 9, 60, 10, 11, 12, 13, 14, 15, 61, 16, 62, 17, 63, 18, 19, 64, 65, 20, 66, 21, 67, 68, 22, 69, 23, 70, 71, 24, 25, 72, 26, 73, 27, 74, 28, 29, 30, 31, 32, 33, 75, 34, 35, 76, 77, 78, 36, 79, 80, 81, 37, 38, 39, 40, 82, 83, 84, 85, 41, 42, 86, 87, 43, 88, 89, 44][i.val]!
  if j<45 then .inl (Fin.ofNat 45 j) else .inr (Fin.ofNat 45 (j-45))

def indexing : (Fin 45 ⊕ Fin 45) ≃ Fin 90 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 45,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*89)*(89-1)^44) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 44 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 44 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 44=(2*89)*(89-1)^44 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitSquaresOpposite


namespace SplitNonsquaresOpposite
def rawWords (i : ℕ) : ℕ := #[5576976746772, 12321829999416, 5434926008257, 14168897588882, 3418278574219, 3469708538114, 8038648865540, 16008706082332, 777221054567, 4928658114766, 10948642394252, 3258263634457, 6517141734450, 17423059337584, 17225187370179, 10279079661119, 11302030817501, 14480131240569, 6896716270071, 9465780851690, 11474429150637, 7347925737377, 9207069062998, 12481278353253, 6032953933201, 16463492692518, 10878121241931, 12858076884517, 17347950750121, 13410285327711, 997173727679, 5231496424314, 10462982805236, 3370223618809, 7907394788834, 15806620168912, 3874795073303, 2252428435246, 4436027358796, 14370392800652, 5047081694323, 9062829091058, 1978690597581, 2788488373386, 0][i]!
def words (i : Fin 45) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 89]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 45 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 45 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 45, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 45, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-924:ℤ) := by
  change cubicInteger (fun i : Fin 45 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-924:ℤ) ∧
    87*(45:ℤ)^3+375*45*(4*45-3)+1000*((wordMatrix words-1)^3).trace-
      1110*89*(45-1)=(5643990:ℤ) ∧ 0≤(5643990:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 45 ⊕ Fin 45 → Fin 90
  | .inl i => Fin.ofNat 90 (#[1, 2, 4, 5, 8, 9, 10, 11, 16, 17, 18, 20, 21, 22, 25, 32, 34, 36, 39, 40, 42, 44, 45, 47, 49, 50, 53, 55, 57, 64, 67, 68, 69, 71, 72, 73, 78, 79, 80, 81, 84, 85, 87, 88, 89][i.val]!)
  | .inr i => Fin.ofNat 90 (#[0, 3, 6, 7, 12, 13, 14, 15, 19, 23, 24, 26, 27, 28, 29, 30, 31, 33, 35, 37, 38, 41, 43, 46, 48, 51, 52, 54, 56, 58, 59, 60, 61, 62, 63, 65, 66, 70, 74, 75, 76, 77, 82, 83, 86][i.val]!)

def pointPosition (i : Fin 90) : Fin 45 ⊕ Fin 45 :=
  let j : ℕ := #[45, 0, 1, 46, 2, 3, 47, 48, 4, 5, 6, 7, 49, 50, 51, 52, 8, 9, 10, 53, 11, 12, 13, 54, 55, 14, 56, 57, 58, 59, 60, 61, 15, 62, 16, 63, 17, 64, 65, 18, 19, 66, 20, 67, 21, 22, 68, 23, 69, 24, 25, 70, 71, 26, 72, 27, 73, 28, 74, 75, 76, 77, 78, 79, 29, 80, 81, 30, 31, 32, 82, 33, 34, 35, 83, 84, 85, 86, 36, 37, 38, 39, 87, 88, 40, 41, 89, 42, 43, 44][i.val]!
  if j<45 then .inl (Fin.ofNat 45 j) else .inr (Fin.ofNat 45 (j-45))

def indexing : (Fin 45 ⊕ Fin 45) ≃ Fin 90 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 45,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*89)*(89-1)^44) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 44 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 44 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 44=(2*89)*(89-1)^44 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end SplitNonsquaresOpposite


namespace NonsplitNegativeOpposite
def rawWords (i : ℕ) : ℕ := #[6715931063840, 11647235718188, 15117044937282, 3254129709986, 7880566605696, 1485344411787, 4072464051332, 16927267427448, 11866315556888, 7922856632349, 15983162716371, 16852342063426, 17377338139823, 5269545621063, 12325925686351, 7609345771614, 9998223552757, 16351133991837, 2880436203389, 6035607834171, 9049697524766, 5435063297065, 10180717504754, 8261772447169, 15149224569834, 13122742933396, 12764929920951, 12029139254921, 8388165557622, 16643055270605, 15558693713202, 16846078475071, 4570713152687, 13953876338967, 12645575905998, 1653665084725, 2072527194735, 2282678174428, 14364709665192, 129380037966, 4796266928884, 4556935585755, 3590352191125, 304662928774, 0][i]!
def words (i : Fin 45) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93, 93]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal 45 rawWords i=rowTotals i)

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
private theorem rowChecked : allBelow 45 rowAgrees=true := by
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
  exact h

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin 45, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin 45, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=(-1800:ℤ) := by
  change cubicInteger (fun i : Fin 45 ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=(-1800:ℤ) ∧
    87*(45:ℤ)^3+375*45*(4*45-3)+1000*((wordMatrix words-1)^3).trace-
      1110*89*(45-1)=(4767990:ℤ) ∧ 0≤(4767990:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin 45 ⊕ Fin 45 → Fin 90
  | .inl i => Fin.ofNat 90 (#[1, 2, 5, 9, 10, 15, 19, 22, 23, 24, 25, 26, 28, 31, 32, 33, 34, 36, 38, 39, 40, 44, 45, 49, 50, 51, 53, 55, 56, 57, 58, 61, 63, 64, 65, 66, 67, 70, 74, 79, 80, 84, 87, 88, 89][i.val]!)
  | .inr i => Fin.ofNat 90 (#[0, 3, 4, 6, 7, 8, 11, 12, 13, 14, 16, 17, 18, 20, 21, 27, 29, 30, 35, 37, 41, 42, 43, 46, 47, 48, 52, 54, 59, 60, 62, 68, 69, 71, 72, 73, 75, 76, 77, 78, 81, 82, 83, 85, 86][i.val]!)

def pointPosition (i : Fin 90) : Fin 45 ⊕ Fin 45 :=
  let j : ℕ := #[45, 0, 1, 46, 47, 2, 48, 49, 50, 3, 4, 51, 52, 53, 54, 5, 55, 56, 57, 6, 58, 59, 7, 8, 9, 10, 11, 60, 12, 61, 62, 13, 14, 15, 16, 63, 17, 64, 18, 19, 20, 65, 66, 67, 21, 22, 68, 69, 70, 23, 24, 25, 71, 26, 72, 27, 28, 29, 30, 73, 74, 31, 75, 32, 33, 34, 35, 36, 76, 77, 37, 78, 79, 80, 38, 81, 82, 83, 84, 39, 40, 85, 86, 87, 41, 88, 89, 42, 43, 44][i.val]!
  if j<45 then .inl (Fin.ofNat 45 j) else .inr (Fin.ofNat 45 (j-45))

def indexing : (Fin 45 ⊕ Fin 45) ≃ Fin 90 where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin 45,
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*89)*(89-1)^44) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound 44 ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant 44 fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound 44=(2*89)*(89-1)^44 := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end NonsplitNegativeOpposite

end PaleyBits89
