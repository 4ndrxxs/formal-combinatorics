module
public import Quantum.EvenSpectrum
public import Quantum.SmallSixPart6
public import Quantum.SmallSixPart15
public import Quantum.SmallSixPart23
public import Quantum.SmallSixPart30

/-! The complete positive spectrum at order six, after Zhang–Ji, Xu and Das–Kumar. -/
@[expose] public section
namespace SmallSix
open QuantumCertificate

theorem good : Good 6 := by
  intro c lo hi hole
  have upper : c ≤ 36 := by omega
  interval_cases c <;> first
    | exact card6
    | exact card8
    | exact card9
    | exact card10
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
    | exact card34
    | exact card35
    | exact card36
    | omega

#print axioms good
end SmallSix
