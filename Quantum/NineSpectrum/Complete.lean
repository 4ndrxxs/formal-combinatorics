module
public import Quantum.OrderNine
public import Quantum.OrderNineGluing
public import Quantum.NineSpectrum.Part00
public import Quantum.NineSpectrum.Part01
public import Quantum.NineSpectrum.Part02
public import Quantum.NineSpectrum.Part03
public import Quantum.NineSpectrum.Part04
public import Quantum.NineSpectrum.Part05
public import Quantum.NineSpectrum.Part06
public import Quantum.NineSpectrum.Part07
public import Quantum.NineSpectrum.Part08

/-! Every admissible order-nine projective cardinality is attained. -/
@[expose] public section
namespace NineSpectrum
open QuantumCertificate

theorem positive (c : ℕ) (lo : 9 ≤ c) (hi : c ≤ 81) (skip : c ≠ 10) :
    Realized 9 c := by
  interval_cases c <;> first
    | exact card9
    | exact card11
    | exact card12
    | exact card13
    | exact card14
    | exact card15
    | exact card16
    | exact card17
    | exact card18
    | exact card19
    | exact card20
    | exact card21
    | exact card22
    | exact card23
    | exact card24
    | exact card25
    | exact card26
    | exact card27
    | exact card28
    | exact card29
    | exact card30
    | exact card31
    | exact card32
    | exact card33
    | exact OrderNineGluing.card34
    | exact card35
    | exact card36
    | exact card37
    | exact card38
    | exact card39
    | exact card40
    | exact card41
    | exact card42
    | exact card43
    | exact card44
    | exact card45
    | exact card46
    | exact card47
    | exact card48
    | exact card49
    | exact card50
    | exact card51
    | exact card52
    | exact card53
    | exact card54
    | exact card55
    | exact card56
    | exact card57
    | exact card58
    | exact card59
    | exact OrderNine.card60
    | exact OrderNineGluing.card61
    | exact OrderNine.card62
    | exact card63
    | exact card64
    | exact OrderNine.card65
    | exact OrderNine.card66
    | exact OrderNineGluing.card67
    | exact OrderNine.card68
    | exact OrderNine.card69
    | exact OrderNine.card70
    | exact OrderNine.card71
    | exact card72
    | exact OrderNine.card73
    | exact OrderNine.card74
    | exact card75
    | exact card76
    | exact card77
    | exact card78
    | exact card79
    | exact card80
    | exact card81
    | omega

#print axioms positive

end NineSpectrum
