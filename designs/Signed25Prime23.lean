import Signed25Grid23Part0
import Signed25Grid23Part12
import Signed25Grid23Part24
import Signed25Grid23Part36
import Signed25Grid23Part48
import SignedExtendedClassification
import SignedBudgetCertificate

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_23_25 : divisorGrid 23 25 235 qInputs_23_25 keep_23_25 := by
  intro d
  fin_cases d
  · exact grid23x25Case0
  · exact grid23x25Case1
  · exact grid23x25Case2
  · exact grid23x25Case3
  · exact grid23x25Case4
  · exact grid23x25Case5
  · exact grid23x25Case6
  · exact grid23x25Case7
  · exact grid23x25Case8
  · exact grid23x25Case9
  · exact grid23x25Case10
  · exact grid23x25Case11
  · exact grid23x25Case12
  · exact grid23x25Case13
  · exact grid23x25Case14
  · exact grid23x25Case15
  · exact grid23x25Case16
  · exact grid23x25Case17
  · exact grid23x25Case18
  · exact grid23x25Case19
  · exact grid23x25Case20
  · exact grid23x25Case21
  · exact grid23x25Case22
  · exact grid23x25Case23
  · exact grid23x25Case24
  · exact grid23x25Case25
  · exact grid23x25Case26
  · exact grid23x25Case27
  · exact grid23x25Case28
  · exact grid23x25Case29
  · exact grid23x25Case30
  · exact grid23x25Case31
  · exact grid23x25Case32
  · exact grid23x25Case33
  · exact grid23x25Case34
  · exact grid23x25Case35
  · exact grid23x25Case36
  · exact grid23x25Case37
  · exact grid23x25Case38
  · exact grid23x25Case39
  · exact grid23x25Case40
  · exact grid23x25Case41
  · exact grid23x25Case42
  · exact grid23x25Case43
  · exact grid23x25Case44
  · exact grid23x25Case45
  · exact grid23x25Case46
  · exact grid23x25Case47
  · exact grid23x25Case48
  · exact grid23x25Case49



private theorem frontier_mixed_667_613_38 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=667) : ¬∃ f : G → ℤ, IsSDS 613 38 f :=
  abelian_short_linear G 23 29 23 0 5 11 613 38 25 7 6 13
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_989_729_154 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=989) : ¬∃ f : G → ℤ, IsSDS 729 154 f :=
  abelian_short_linear G 23 43 23 1 5 11 729 154 25 17 6 13
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_989_936_361 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=989) : ¬∃ f : G → ℤ, IsSDS 936 361 f :=
  abelian_short_linear G 23 43 23 0 5 11 936 361 25 26 6 13
    ⟨⟨6,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1127_582_7 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1127) : ¬∃ f : G → ℤ, IsSDS 582 7 f :=
  abelian_short_linear G 23 49 23 1 5 11 582 7 25 4 6 13
    ⟨⟨(-32),(-1),1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1541_576_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1541) : ¬∃ f : G → ℤ, IsSDS 576 1 f :=
  abelian_short_linear G 23 67 23 1 5 11 576 1 25 2 6 13
    ⟨⟨(-239200),9200,5000,207⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1771_661_86 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1771) : ¬∃ f : G → ℤ, IsSDS 661 86 f :=
  abelian_short_linear G 23 77 23 1 5 11 661 86 25 17 6 13
    ⟨⟨(-20148),(-1817),525,58⟩,[0,0,0,0,0,0,0,1150,0,0,0,0,0,0,0,0,0,13800,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1771_1006_431 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1771) : ¬∃ f : G → ℤ, IsSDS 1006 431 f :=
  abelian_short_linear G 23 77 23 1 5 11 1006 431 25 38 6 13
    ⟨⟨(-3372),(-5900),4215,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1771_1029_454 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1771) : ¬∃ f : G → ℤ, IsSDS 1029 454 f :=
  abelian_short_linear G 23 77 23 1 5 11 1029 454 25 39 6 13
    ⟨⟨(-84214132),0,3525280,(-72105)⟩,[0,0,0,0,0,0,7371040,0,0,0,0,0,0,0,0,0,0,0,0,0,0,19348980,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1771_1650_1075 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1771) : ¬∃ f : G → ℤ, IsSDS 1650 1075 f :=
  abelian_short_linear G 23 77 23 0 5 11 1650 1075 25 60 6 13
    ⟨⟨45,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1817_952_377 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1817) : ¬∃ f : G → ℤ, IsSDS 952 377 f :=
  abelian_short_linear G 23 79 23 1 5 11 952 377 25 36 6 13
    ⟨⟨8,(-8),5,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1817_1113_538 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1817) : ¬∃ f : G → ℤ, IsSDS 1113 538 f :=
  abelian_short_linear G 23 79 23 1 5 11 1113 538 25 43 6 13
    ⟨⟨(-60),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1909_841_266 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1909) : ¬∃ f : G → ℤ, IsSDS 841 266 f :=
  abelian_short_linear G 23 83 23 1 5 11 841 266 25 31 6 13
    ⟨⟨0,(-30452),7995,367⟩,[0,0,0,0,0,0,0,0,55660,0,0,0,0,0,0,0,89470,0,0,0,0,133860,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1909_1324_749 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1909) : ¬∃ f : G → ℤ, IsSDS 1324 749 f :=
  abelian_short_linear G 23 83 23 1 5 11 1324 749 25 52 6 13
    ⟨⟨42,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2369_625_50 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2369) : ¬∃ f : G → ℤ, IsSDS 625 50 f :=
  abelian_short_linear G 23 103 23 2 5 11 625 50 25 15 6 13
    ⟨⟨0,(-2530),300,71⟩,[0,0,575,0,0,0,0,0,0,0,9200,0,0,0,0,12075,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2369_2304_1729 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2369) : ¬∃ f : G → ℤ, IsSDS 2304 1729 f :=
  abelian_short_linear G 23 103 23 0 5 11 2304 1729 25 88 6 13
    ⟨⟨2266,13,(-35),0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3059_741_166 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3059) : ¬∃ f : G → ℤ, IsSDS 741 166 f :=
  abelian_short_linear G 23 133 23 0 5 11 741 166 25 31 6 13
    ⟨⟨(-184),(-3),7,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3059_2374_1799 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3059) : ¬∃ f : G → ℤ, IsSDS 2374 1799 f :=
  abelian_short_linear G 23 133 23 0 5 11 2374 1799 25 102 6 13
    ⟨⟨1392,(-31),15,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3979_594_19 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3979) : ¬∃ f : G → ℤ, IsSDS 594 19 f :=
  abelian_short_linear G 23 173 23 4 5 11 594 19 25 12 6 13
    ⟨⟨(-414),(-69),10,3⟩,[0,0,0,0,0,0,0,0,0,0,0,0,230,0,0,0,0,230,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4531_589_14 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4531) : ¬∃ f : G → ℤ, IsSDS 589 14 f :=
  abelian_short_linear G 23 197 23 4 5 11 589 14 25 11 6 13
    ⟨⟨(-4936536),(-1470988),162600,66125⟩,[0,0,0,0,0,0,0,0,0,0,0,1246600,0,0,0,0,3739800,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6923_597_22 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6923) : ¬∃ f : G → ℤ, IsSDS 597 22 f :=
  abelian_short_linear G 23 301 23 4 5 11 597 22 25 17 6 13
    ⟨⟨0,(-2270652),263264,57592⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,11164039,0,0,0,0,6811956],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6923_6738_6163 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6923) : ¬∃ f : G → ℤ, IsSDS 6738 6163 f :=
  abelian_short_linear G 23 301 23 0 5 11 6738 6163 25 284 6 13
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7889_576_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7889) : ¬∃ f : G → ℤ, IsSDS 576 1 f :=
  abelian_short_linear G 23 343 23 7 5 11 576 1 25 4 6 13
    ⟨⟨(-70989362),(-4888489),1155125,258750⟩,[0,0,0,0,42508600,0,0,0,0,21254300,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8303_618_43 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8303) : ¬∃ f : G → ℤ, IsSDS 618 43 f :=
  abelian_short_linear G 23 361 23 0 5 11 618 43 25 26 6 13
    ⟨⟨(-41),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8303_7725_7150 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8303) : ¬∃ f : G → ℤ, IsSDS 7725 7150 f :=
  abelian_short_linear G 23 361 23 0 5 11 7725 7150 25 335 6 13
    ⟨⟨320,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8441_600_25 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8441) : ¬∃ f : G → ℤ, IsSDS 600 25 f :=
  abelian_short_linear G 23 367 23 3 5 11 600 25 25 20 6 13
    ⟨⟨0,(-1380),125,33⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6900,0,0,0,0,6900,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8441_8121_7546 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8441) : ¬∃ f : G → ℤ, IsSDS 8121 7546 f :=
  abelian_short_linear G 23 367 23 0 5 11 8121 7546 25 347 6 13
    ⟨⟨(-367),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8809_604_29 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8809) : ¬∃ f : G → ℤ, IsSDS 604 29 f :=
  abelian_short_linear G 23 383 23 2 5 11 604 29 25 22 6 13
    ⟨⟨(-16019684),(-935456),222425,24150⟩,[0,0,0,0,0,0,0,0,0,8769900,0,0,0,0,0,0,0,13154850,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8809_8401_7826 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8809) : ¬∃ f : G → ℤ, IsSDS 8401 7826 f :=
  abelian_short_linear G 23 383 23 0 5 11 8401 7826 25 361 6 13
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_10741_601_26 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=10741) : ¬∃ f : G → ℤ, IsSDS 601 26 f :=
  abelian_short_linear G 23 467 23 1 5 11 601 26 25 23 6 13
    ⟨⟨(-461414),0,6951,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,19992,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_10741_10284_9709 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=10741) : ¬∃ f : G → ℤ, IsSDS 10284 9709 f :=
  abelian_short_linear G 23 467 23 1 5 11 10284 9709 25 444 6 13
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_10879_589_14 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=10879) : ¬∃ f : G → ℤ, IsSDS 589 14 f :=
  abelian_short_linear G 23 473 23 4 5 11 589 14 25 17 6 13
    ⟨⟨(-31654854),(-2398095),312800,111216⟩,[0,0,15987300,0,0,0,0,6394920,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_10879_10686_10111 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=10879) : ¬∃ f : G → ℤ, IsSDS 10686 10111 f :=
  abelian_short_linear G 23 473 23 0 5 11 10686 10111 25 456 6 13
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_12673_577_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=12673) : ¬∃ f : G → ℤ, IsSDS 577 2 f :=
  abelian_short_linear G 23 551 23 9 5 11 577 2 25 7 6 13
    ⟨⟨(-782),(-138),25,2⟩,[0,0,0,0,0,0,0,575,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_21137_577_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=21137) : ¬∃ f : G → ℤ, IsSDS 577 2 f :=
  abelian_short_linear G 23 919 23 8 5 11 577 2 25 9 6 13
    ⟨⟨(-304080),(-38000),10317,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_31717_577_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=31717) : ¬∃ f : G → ℤ, IsSDS 577 2 f :=
  abelian_short_linear G 23 1379 23 7 5 11 577 2 25 11 6 13
    ⟨⟨(-1617533000),(-626188500),88203123,0⟩,[0,0,0,0,0,0,0,0,0,0,0,2056549500,0,0,0,0,1599538500,0,0,0,0,914022000,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_33281_576_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=33281) : ¬∃ f : G → ℤ, IsSDS 576 1 f :=
  abelian_short_linear G 23 1447 23 8 5 11 576 1 25 8 6 13
    ⟨⟨(-5175900),(-183393),110700,0⟩,[0,0,0,0,0,0,0,0,1018850,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_44413_577_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=44413) : ¬∃ f : G → ℤ, IsSDS 577 2 f :=
  abelian_short_linear G 23 1931 23 6 5 11 577 2 25 13 6 13
    ⟨⟨0,(-1043165000),60885000,18017901⟩,[0,0,0,730620000,0,0,0,0,0,0,0,0,0,1501830000,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_44413_44392_43817 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=44413) : ¬∃ f : G → ℤ, IsSDS 44392 43817 f :=
  abelian_short_linear G 23 1931 23 0 5 11 44392 43817 25 1918 6 13
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_75601_576_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=75601) : ¬∃ f : G → ℤ, IsSDS 576 1 f :=
  abelian_short_linear G 23 3287 23 6 5 11 576 1 25 12 6 13
    ⟨⟨(-1748),(-782),75,3⟩,[0,0,0,0,0,0,0,1150,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_76153_577_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=76153) : ¬∃ f : G → ℤ, IsSDS 577 2 f :=
  abelian_short_linear G 23 3311 23 4 5 11 577 2 25 17 6 13
    ⟨⟨0,0,18363399,(-30035000)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,2384460000,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_76153_75948_75373 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=76153) : ¬∃ f : G → ℤ, IsSDS 75948 75373 f :=
  abelian_short_linear G 23 3311 23 0 5 11 75948 75373 25 3294 6 13
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_95197_577_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=95197) : ¬∃ f : G → ℤ, IsSDS 577 2 f :=
  abelian_short_linear G 23 4139 23 3 5 11 577 2 25 19 6 13
    ⟨⟨4,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_95197_94900_94325 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=95197) : ¬∃ f : G → ℤ, IsSDS 94900 94325 f :=
  abelian_short_linear G 23 4139 23 0 5 11 94900 94325 25 4120 6 13
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_103109_576_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=103109) : ¬∃ f : G → ℤ, IsSDS 576 1 f :=
  abelian_short_linear G 23 4483 23 5 5 11 576 1 25 14 6 13
    ⟨⟨0,0,98,(-89)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8119,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_103109_103041_102466 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=103109) : ¬∃ f : G → ℤ, IsSDS 103041 102466 f :=
  abelian_short_linear G 23 4483 23 0 5 11 103041 102466 25 4469 6 13
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_116357_577_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=116357) : ¬∃ f : G → ℤ, IsSDS 577 2 f :=
  abelian_short_linear G 23 5059 23 2 5 11 577 2 25 21 6 13
    ⟨⟨1,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_116357_115968_115393 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=116357) : ¬∃ f : G → ℤ, IsSDS 115968 115393 f :=
  abelian_short_linear G 23 5059 23 0 5 11 115968 115393 25 5038 6 13
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_255461_576_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=255461) : ¬∃ f : G → ℤ, IsSDS 576 1 f :=
  abelian_short_linear G 23 11107 23 1 5 11 576 1 25 22 6 13
    ⟨⟨2,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_255461_255025_254450 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=255461) : ¬∃ f : G → ℤ, IsSDS 255025 254450 f :=
  abelian_short_linear G 23 11107 23 0 5 11 255025 254450 25 11085 6 13
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_23_25_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=23*m)
    (hm : 23 < m) (hn : k-l=(23:ℤ)*25) : False := by
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  have row := endpoint_case (s:=25) hf hg hn (by decide) hm grid_23_25
  simp only [keep_23_25,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=613 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_667_613_38 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=729 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_989_729_154 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=936 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_989_936_361 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=582 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1127_582_7 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=576 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1541_576_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=661 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1771_661_86 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1006 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1771_1006_431 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1029 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1771_1029_454 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1650 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1771_1650_1075 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=952 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1817_952_377 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1113 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1817_1113_538 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=841 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1909_841_266 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1324 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1909_1324_749 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=625 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2369_625_50 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2304 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2369_2304_1729 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=741 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3059_741_166 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2374 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3059_2374_1799 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=594 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3979_594_19 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=589 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4531_589_14 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=597 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6923_597_22 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=6738 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6923_6738_6163 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=576 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7889_576_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=618 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8303_618_43 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=7725 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8303_7725_7150 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=600 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8441_600_25 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=8121 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8441_8121_7546 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=604 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8809_604_29 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=8401 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8809_8401_7826 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=601 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_10741_601_26 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=10284 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_10741_10284_9709 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=589 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_10879_589_14 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=10686 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_10879_10686_10111 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=577 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_12673_577_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=577 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_21137_577_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=577 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_31717_577_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=576 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_33281_576_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=577 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_44413_577_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=44392 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_44413_44392_43817 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=576 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_75601_576_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=577 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_76153_577_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=75948 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_76153_75948_75373 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=577 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_95197_577_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=94900 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_95197_94900_94325 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=576 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_103109_576_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=103041 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_103109_103041_102466 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=577 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_116357_577_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=115968 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_116357_115968_115393 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=576 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_255461_576_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=255025 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_255461_255025_254450 G hg ⟨f,hf⟩

end Signed39.Contraction
