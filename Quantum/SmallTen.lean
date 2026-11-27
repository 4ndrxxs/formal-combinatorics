module
public import Quantum.SmallEven.TenPart0
public import Quantum.SmallEven.TenPart1
public import Quantum.SmallEven.TenPart2
public import Quantum.SmallEven.TenPart3

@[expose] public section
namespace SmallTen
open QuantumCertificate

private theorem flip : ∀ p : Cell 10, evenMask 5 (p.1,swapHalf 5 p.2) = !(evenMask 5 p) := by
  decide +kernel

theorem good : Good 10 := by
  intro c lo hi hole
  change c ≤ 100 at hi
  interval_cases c
  · exact diagonal_pair (m:=5) (x:=5) (y:=5) flip SmallEven.B10_5.block SmallEven.B10_5.block
  · exact False.elim (hole rfl)
  · exact diagonal_pair (m:=5) (x:=5) (y:=7) flip SmallEven.B10_5.block SmallEven.B10_7.block
  · exact diagonal_pair (m:=5) (x:=5) (y:=8) flip SmallEven.B10_5.block SmallEven.B10_8.block
  · exact diagonal_pair (m:=5) (x:=7) (y:=7) flip SmallEven.B10_7.block SmallEven.B10_7.block
  · exact diagonal_pair (m:=5) (x:=7) (y:=8) flip SmallEven.B10_7.block SmallEven.B10_8.block
  · exact diagonal_pair (m:=5) (x:=8) (y:=8) flip SmallEven.B10_8.block SmallEven.B10_8.block
  · exact diagonal_pair (m:=5) (x:=8) (y:=9) flip SmallEven.B10_8.block SmallEven.B10_9.block
  · exact diagonal_pair (m:=5) (x:=9) (y:=9) flip SmallEven.B10_9.block SmallEven.B10_9.block
  · exact diagonal_pair (m:=5) (x:=8) (y:=11) flip SmallEven.B10_8.block SmallEven.B10_11.block
  · exact diagonal_pair (m:=5) (x:=9) (y:=11) flip SmallEven.B10_9.block SmallEven.B10_11.block
  · exact diagonal_pair (m:=5) (x:=8) (y:=13) flip SmallEven.B10_8.block SmallEven.B10_13.block
  · exact diagonal_pair (m:=5) (x:=11) (y:=11) flip SmallEven.B10_11.block SmallEven.B10_11.block
  · exact diagonal_pair (m:=5) (x:=9) (y:=14) flip SmallEven.B10_9.block SmallEven.B10_14.block
  · exact diagonal_pair (m:=5) (x:=11) (y:=13) flip SmallEven.B10_11.block SmallEven.B10_13.block
  · exact diagonal_pair (m:=5) (x:=11) (y:=14) flip SmallEven.B10_11.block SmallEven.B10_14.block
  · exact diagonal_pair (m:=5) (x:=13) (y:=13) flip SmallEven.B10_13.block SmallEven.B10_13.block
  · exact diagonal_pair (m:=5) (x:=13) (y:=14) flip SmallEven.B10_13.block SmallEven.B10_14.block
  · exact diagonal_pair (m:=5) (x:=14) (y:=14) flip SmallEven.B10_14.block SmallEven.B10_14.block
  · exact diagonal_pair (m:=5) (x:=8) (y:=21) flip SmallEven.B10_8.block SmallEven.B10_21.block
  · exact diagonal_pair (m:=5) (x:=9) (y:=21) flip SmallEven.B10_9.block SmallEven.B10_21.block
  · exact diagonal_pair (m:=5) (x:=8) (y:=23) flip SmallEven.B10_8.block SmallEven.B10_23.block
  · exact diagonal_pair (m:=5) (x:=11) (y:=21) flip SmallEven.B10_11.block SmallEven.B10_21.block
  · exact diagonal_pair (m:=5) (x:=8) (y:=25) flip SmallEven.B10_8.block SmallEven.B10_25.block
  · exact diagonal_pair (m:=5) (x:=13) (y:=21) flip SmallEven.B10_13.block SmallEven.B10_21.block
  · exact diagonal_pair (m:=5) (x:=14) (y:=21) flip SmallEven.B10_14.block SmallEven.B10_21.block
  · exact diagonal_pair (m:=5) (x:=13) (y:=23) flip SmallEven.B10_13.block SmallEven.B10_23.block
  · exact diagonal_pair (m:=5) (x:=14) (y:=23) flip SmallEven.B10_14.block SmallEven.B10_23.block
  · exact diagonal_pair (m:=5) (x:=13) (y:=25) flip SmallEven.B10_13.block SmallEven.B10_25.block
  · exact diagonal_pair (m:=5) (x:=14) (y:=25) flip SmallEven.B10_14.block SmallEven.B10_25.block
  · exact diagonal_pair (m:=5) (x:=11) (y:=29) flip SmallEven.B10_11.block SmallEven.B10_29.block
  · exact diagonal_pair (m:=5) (x:=8) (y:=33) flip SmallEven.B10_8.block SmallEven.B10_33.block
  · exact diagonal_pair (m:=5) (x:=21) (y:=21) flip SmallEven.B10_21.block SmallEven.B10_21.block
  · exact diagonal_pair (m:=5) (x:=14) (y:=29) flip SmallEven.B10_14.block SmallEven.B10_29.block
  · exact diagonal_pair (m:=5) (x:=21) (y:=23) flip SmallEven.B10_21.block SmallEven.B10_23.block
  · exact diagonal_pair (m:=5) (x:=8) (y:=37) flip SmallEven.B10_8.block SmallEven.B10_37.block
  · exact diagonal_pair (m:=5) (x:=23) (y:=23) flip SmallEven.B10_23.block SmallEven.B10_23.block
  · exact diagonal_pair (m:=5) (x:=14) (y:=33) flip SmallEven.B10_14.block SmallEven.B10_33.block
  · exact diagonal_pair (m:=5) (x:=23) (y:=25) flip SmallEven.B10_23.block SmallEven.B10_25.block
  · exact diagonal_pair (m:=5) (x:=8) (y:=41) flip SmallEven.B10_8.block SmallEven.B10_41.block
  · exact diagonal_pair (m:=5) (x:=25) (y:=25) flip SmallEven.B10_25.block SmallEven.B10_25.block
  · exact diagonal_pair (m:=5) (x:=14) (y:=37) flip SmallEven.B10_14.block SmallEven.B10_37.block
  · exact diagonal_pair (m:=5) (x:=23) (y:=29) flip SmallEven.B10_23.block SmallEven.B10_29.block
  · exact diagonal_pair (m:=5) (x:=9) (y:=44) flip SmallEven.B10_9.block SmallEven.B10_44.block
  · exact diagonal_pair (m:=5) (x:=25) (y:=29) flip SmallEven.B10_25.block SmallEven.B10_29.block
  · exact diagonal_pair (m:=5) (x:=14) (y:=41) flip SmallEven.B10_14.block SmallEven.B10_41.block
  · exact diagonal_pair (m:=5) (x:=23) (y:=33) flip SmallEven.B10_23.block SmallEven.B10_33.block
  · exact diagonal_pair (m:=5) (x:=13) (y:=44) flip SmallEven.B10_13.block SmallEven.B10_44.block
  · exact diagonal_pair (m:=5) (x:=29) (y:=29) flip SmallEven.B10_29.block SmallEven.B10_29.block
  · exact diagonal_pair (m:=5) (x:=14) (y:=45) flip SmallEven.B10_14.block SmallEven.B10_45.block
  · exact diagonal_pair (m:=5) (x:=23) (y:=37) flip SmallEven.B10_23.block SmallEven.B10_37.block
  · exact diagonal_pair (m:=5) (x:=14) (y:=47) flip SmallEven.B10_14.block SmallEven.B10_47.block
  · exact diagonal_pair (m:=5) (x:=29) (y:=33) flip SmallEven.B10_29.block SmallEven.B10_33.block
  · exact diagonal_pair (m:=5) (x:=14) (y:=49) flip SmallEven.B10_14.block SmallEven.B10_49.block
  · exact diagonal_pair (m:=5) (x:=23) (y:=41) flip SmallEven.B10_23.block SmallEven.B10_41.block
  · exact diagonal_pair (m:=5) (x:=21) (y:=44) flip SmallEven.B10_21.block SmallEven.B10_44.block
  · exact diagonal_pair (m:=5) (x:=33) (y:=33) flip SmallEven.B10_33.block SmallEven.B10_33.block
  · exact diagonal_pair (m:=5) (x:=23) (y:=44) flip SmallEven.B10_23.block SmallEven.B10_44.block
  · exact diagonal_pair (m:=5) (x:=23) (y:=45) flip SmallEven.B10_23.block SmallEven.B10_45.block
  · exact diagonal_pair (m:=5) (x:=25) (y:=44) flip SmallEven.B10_25.block SmallEven.B10_44.block
  · exact diagonal_pair (m:=5) (x:=33) (y:=37) flip SmallEven.B10_33.block SmallEven.B10_37.block
  · exact diagonal_pair (m:=5) (x:=21) (y:=50) flip SmallEven.B10_21.block SmallEven.B10_50.block
  · exact diagonal_pair (m:=5) (x:=25) (y:=47) flip SmallEven.B10_25.block SmallEven.B10_47.block
  · exact diagonal_pair (m:=5) (x:=29) (y:=44) flip SmallEven.B10_29.block SmallEven.B10_44.block
  · exact diagonal_pair (m:=5) (x:=37) (y:=37) flip SmallEven.B10_37.block SmallEven.B10_37.block
  · exact diagonal_pair (m:=5) (x:=25) (y:=50) flip SmallEven.B10_25.block SmallEven.B10_50.block
  · exact diagonal_pair (m:=5) (x:=29) (y:=47) flip SmallEven.B10_29.block SmallEven.B10_47.block
  · exact diagonal_pair (m:=5) (x:=33) (y:=44) flip SmallEven.B10_33.block SmallEven.B10_44.block
  · exact diagonal_pair (m:=5) (x:=37) (y:=41) flip SmallEven.B10_37.block SmallEven.B10_41.block
  · exact diagonal_pair (m:=5) (x:=29) (y:=50) flip SmallEven.B10_29.block SmallEven.B10_50.block
  · exact diagonal_pair (m:=5) (x:=33) (y:=47) flip SmallEven.B10_33.block SmallEven.B10_47.block
  · exact diagonal_pair (m:=5) (x:=37) (y:=44) flip SmallEven.B10_37.block SmallEven.B10_44.block
  · exact diagonal_pair (m:=5) (x:=41) (y:=41) flip SmallEven.B10_41.block SmallEven.B10_41.block
  · exact diagonal_pair (m:=5) (x:=33) (y:=50) flip SmallEven.B10_33.block SmallEven.B10_50.block
  · exact diagonal_pair (m:=5) (x:=37) (y:=47) flip SmallEven.B10_37.block SmallEven.B10_47.block
  · exact diagonal_pair (m:=5) (x:=41) (y:=44) flip SmallEven.B10_41.block SmallEven.B10_44.block
  · exact diagonal_pair (m:=5) (x:=41) (y:=45) flip SmallEven.B10_41.block SmallEven.B10_45.block
  · exact diagonal_pair (m:=5) (x:=37) (y:=50) flip SmallEven.B10_37.block SmallEven.B10_50.block
  · exact diagonal_pair (m:=5) (x:=44) (y:=44) flip SmallEven.B10_44.block SmallEven.B10_44.block
  · exact diagonal_pair (m:=5) (x:=44) (y:=45) flip SmallEven.B10_44.block SmallEven.B10_45.block
  · exact diagonal_pair (m:=5) (x:=45) (y:=45) flip SmallEven.B10_45.block SmallEven.B10_45.block
  · exact diagonal_pair (m:=5) (x:=44) (y:=47) flip SmallEven.B10_44.block SmallEven.B10_47.block
  · exact diagonal_pair (m:=5) (x:=45) (y:=47) flip SmallEven.B10_45.block SmallEven.B10_47.block
  · exact diagonal_pair (m:=5) (x:=44) (y:=49) flip SmallEven.B10_44.block SmallEven.B10_49.block
  · exact diagonal_pair (m:=5) (x:=47) (y:=47) flip SmallEven.B10_47.block SmallEven.B10_47.block
  · exact diagonal_pair (m:=5) (x:=45) (y:=50) flip SmallEven.B10_45.block SmallEven.B10_50.block
  · exact diagonal_pair (m:=5) (x:=47) (y:=49) flip SmallEven.B10_47.block SmallEven.B10_49.block
  · exact diagonal_pair (m:=5) (x:=47) (y:=50) flip SmallEven.B10_47.block SmallEven.B10_50.block
  · exact diagonal_pair (m:=5) (x:=49) (y:=49) flip SmallEven.B10_49.block SmallEven.B10_49.block
  · exact diagonal_pair (m:=5) (x:=49) (y:=50) flip SmallEven.B10_49.block SmallEven.B10_50.block
  · exact diagonal_pair (m:=5) (x:=50) (y:=50) flip SmallEven.B10_50.block SmallEven.B10_50.block

#print axioms good
end SmallTen
