module
public import Quantum.SmallEven.EightPart0
public import Quantum.SmallEven.EightPart1
public import Quantum.SmallEven.EightPart2

@[expose] public section
namespace SmallEight
open QuantumCertificate

private theorem flip : ∀ p : Cell 8, evenMask 4 (p.1,swapHalf 4 p.2) = !(evenMask 4 p) := by
  decide +kernel

theorem good : Good 8 := by
  intro c lo hi hole
  change c ≤ 64 at hi
  interval_cases c
  · exact diagonal_pair (m:=4) (x:=4) (y:=4) flip SmallEven.B8_4.block SmallEven.B8_4.block
  · exact False.elim (hole rfl)
  · exact diagonal_pair (m:=4) (x:=4) (y:=6) flip SmallEven.B8_4.block SmallEven.B8_6.block
  · exact diagonal_pair (m:=4) (x:=4) (y:=7) flip SmallEven.B8_4.block SmallEven.B8_7.block
  · exact diagonal_pair (m:=4) (x:=6) (y:=6) flip SmallEven.B8_6.block SmallEven.B8_6.block
  · exact diagonal_pair (m:=4) (x:=6) (y:=7) flip SmallEven.B8_6.block SmallEven.B8_7.block
  · exact diagonal_pair (m:=4) (x:=7) (y:=7) flip SmallEven.B8_7.block SmallEven.B8_7.block
  · exact diagonal_pair (m:=4) (x:=6) (y:=9) flip SmallEven.B8_6.block SmallEven.B8_9.block
  · exact diagonal_pair (m:=4) (x:=7) (y:=9) flip SmallEven.B8_7.block SmallEven.B8_9.block
  · exact diagonal_pair (m:=4) (x:=4) (y:=13) flip SmallEven.B8_4.block SmallEven.B8_13.block
  · exact diagonal_pair (m:=4) (x:=9) (y:=9) flip SmallEven.B8_9.block SmallEven.B8_9.block
  · exact diagonal_pair (m:=4) (x:=6) (y:=13) flip SmallEven.B8_6.block SmallEven.B8_13.block
  · exact diagonal_pair (m:=4) (x:=7) (y:=13) flip SmallEven.B8_7.block SmallEven.B8_13.block
  · exact diagonal_pair (m:=4) (x:=6) (y:=15) flip SmallEven.B8_6.block SmallEven.B8_15.block
  · exact diagonal_pair (m:=4) (x:=9) (y:=13) flip SmallEven.B8_9.block SmallEven.B8_13.block
  · exact diagonal_pair (m:=4) (x:=4) (y:=19) flip SmallEven.B8_4.block SmallEven.B8_19.block
  · exact diagonal_pair (m:=4) (x:=9) (y:=15) flip SmallEven.B8_9.block SmallEven.B8_15.block
  · exact diagonal_pair (m:=4) (x:=6) (y:=19) flip SmallEven.B8_6.block SmallEven.B8_19.block
  · exact diagonal_pair (m:=4) (x:=13) (y:=13) flip SmallEven.B8_13.block SmallEven.B8_13.block
  · exact diagonal_pair (m:=4) (x:=4) (y:=23) flip SmallEven.B8_4.block SmallEven.B8_23.block
  · exact diagonal_pair (m:=4) (x:=13) (y:=15) flip SmallEven.B8_13.block SmallEven.B8_15.block
  · exact diagonal_pair (m:=4) (x:=6) (y:=23) flip SmallEven.B8_6.block SmallEven.B8_23.block
  · exact diagonal_pair (m:=4) (x:=15) (y:=15) flip SmallEven.B8_15.block SmallEven.B8_15.block
  · exact diagonal_pair (m:=4) (x:=6) (y:=25) flip SmallEven.B8_6.block SmallEven.B8_25.block
  · exact diagonal_pair (m:=4) (x:=13) (y:=19) flip SmallEven.B8_13.block SmallEven.B8_19.block
  · exact diagonal_pair (m:=4) (x:=4) (y:=29) flip SmallEven.B8_4.block SmallEven.B8_29.block
  · exact diagonal_pair (m:=4) (x:=15) (y:=19) flip SmallEven.B8_15.block SmallEven.B8_19.block
  · exact diagonal_pair (m:=4) (x:=6) (y:=29) flip SmallEven.B8_6.block SmallEven.B8_29.block
  · exact diagonal_pair (m:=4) (x:=13) (y:=23) flip SmallEven.B8_13.block SmallEven.B8_23.block
  · exact diagonal_pair (m:=4) (x:=7) (y:=30) flip SmallEven.B8_7.block SmallEven.B8_30.block
  · exact diagonal_pair (m:=4) (x:=19) (y:=19) flip SmallEven.B8_19.block SmallEven.B8_19.block
  · exact diagonal_pair (m:=4) (x:=9) (y:=30) flip SmallEven.B8_9.block SmallEven.B8_30.block
  · exact diagonal_pair (m:=4) (x:=15) (y:=25) flip SmallEven.B8_15.block SmallEven.B8_25.block
  · exact diagonal_pair (m:=4) (x:=9) (y:=32) flip SmallEven.B8_9.block SmallEven.B8_32.block
  · exact diagonal_pair (m:=4) (x:=19) (y:=23) flip SmallEven.B8_19.block SmallEven.B8_23.block
  · exact diagonal_pair (m:=4) (x:=13) (y:=30) flip SmallEven.B8_13.block SmallEven.B8_30.block
  · exact diagonal_pair (m:=4) (x:=19) (y:=25) flip SmallEven.B8_19.block SmallEven.B8_25.block
  · exact diagonal_pair (m:=4) (x:=15) (y:=30) flip SmallEven.B8_15.block SmallEven.B8_30.block
  · exact diagonal_pair (m:=4) (x:=23) (y:=23) flip SmallEven.B8_23.block SmallEven.B8_23.block
  · exact diagonal_pair (m:=4) (x:=15) (y:=32) flip SmallEven.B8_15.block SmallEven.B8_32.block
  · exact diagonal_pair (m:=4) (x:=23) (y:=25) flip SmallEven.B8_23.block SmallEven.B8_25.block
  · exact diagonal_pair (m:=4) (x:=19) (y:=30) flip SmallEven.B8_19.block SmallEven.B8_30.block
  · exact diagonal_pair (m:=4) (x:=25) (y:=25) flip SmallEven.B8_25.block SmallEven.B8_25.block
  · exact diagonal_pair (m:=4) (x:=19) (y:=32) flip SmallEven.B8_19.block SmallEven.B8_32.block
  · exact diagonal_pair (m:=4) (x:=23) (y:=29) flip SmallEven.B8_23.block SmallEven.B8_29.block
  · exact diagonal_pair (m:=4) (x:=23) (y:=30) flip SmallEven.B8_23.block SmallEven.B8_30.block
  · exact diagonal_pair (m:=4) (x:=25) (y:=29) flip SmallEven.B8_25.block SmallEven.B8_29.block
  · exact diagonal_pair (m:=4) (x:=25) (y:=30) flip SmallEven.B8_25.block SmallEven.B8_30.block
  · exact diagonal_pair (m:=4) (x:=25) (y:=31) flip SmallEven.B8_25.block SmallEven.B8_31.block
  · exact diagonal_pair (m:=4) (x:=25) (y:=32) flip SmallEven.B8_25.block SmallEven.B8_32.block
  · exact diagonal_pair (m:=4) (x:=29) (y:=29) flip SmallEven.B8_29.block SmallEven.B8_29.block
  · exact diagonal_pair (m:=4) (x:=29) (y:=30) flip SmallEven.B8_29.block SmallEven.B8_30.block
  · exact diagonal_pair (m:=4) (x:=30) (y:=30) flip SmallEven.B8_30.block SmallEven.B8_30.block
  · exact diagonal_pair (m:=4) (x:=30) (y:=31) flip SmallEven.B8_30.block SmallEven.B8_31.block
  · exact diagonal_pair (m:=4) (x:=31) (y:=31) flip SmallEven.B8_31.block SmallEven.B8_31.block
  · exact diagonal_pair (m:=4) (x:=31) (y:=32) flip SmallEven.B8_31.block SmallEven.B8_32.block
  · exact diagonal_pair (m:=4) (x:=32) (y:=32) flip SmallEven.B8_32.block SmallEven.B8_32.block

#print axioms good
end SmallEight
