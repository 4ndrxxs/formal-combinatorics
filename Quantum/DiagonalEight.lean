module
public import Quantum.Diagonal
public import Quantum.SmallSixNumbers

/-! A maximal diagonal quantum Latin square of order eight, with coefficients
    in the twelfth cyclotomic field. Every orthonormal basis and ray is checked. -/
@[expose] public section
namespace DiagonalEight
open QuantumCertificate SmallSixNumbers
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def alphabet : Array Quad := #[((2, 0), (0, 0)), ((0, 1), (1, 0)), ((1, 0), (0, 1)), ((0, 0), (2, 0)), ((-1, 0), (0, 1)), ((0, -1), (1, 0)),
  ((-2, 0), (0, 0)), ((0, -1), (-1, 0)), ((-1, 0), (0, -1)), ((0, 0), (-2, 0)), ((1, 0), (0, -1)), ((0, 1), (-1, 0))]
private def words : Array ℕ := #[0, 370672056, 176030712, 235609920, 234003744, 174671640, 372031128, 1628640,
  311092704, 215930520, 18322200, 77654304, 79260480, 19681272, 217308600, 312698880,
  410856552, 351526032, 118087632, 213478056, 214856136, 116458992, 349919856, 409478472,
  334289736, 271745136, 41519088, 136681416, 135303336, 39912912, 273351312, 332930664,
  135846216, 40455792, 272808432, 332387784, 333746856, 274437072, 38827152, 137224296,
  212413032, 117001872, 349376976, 411921576, 410562504, 350983152, 118630512, 213772104,
  79803360, 20224152, 216765720, 312178464, 310549824, 215387640, 18865080, 78174720,
  234524160, 174965688, 371737080, 1085760, 2714400, 373115160, 173587608, 232917984]
private def rep (p : Cell 8) (x : Fin 8) : Quad :=
  alphabet[(words[p.1.val*8+p.2.val]! / 12^x.val) % 12]!

theorem diagonal : MaximalDiagonal 8 := by
  apply (model 3 (show Nat.Prime 3 by decide).not_isSquare).maximal_diagonal rep ((2,0),(0,0)) (by decide)
  · decide +kernel
  · exact (by decide +kernel : ∀ i j : Cell 8, rep i = rep j → i=j)
  all_goals decide +kernel

theorem idempotent : MaximalIdempotent 8 := diagonal.idempotent

#print axioms diagonal
#print axioms idempotent
end DiagonalEight
