import SignedElevenShapes

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem frontier_mixed_2497_256_3 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=2497) :
    ¬∃f:G→ℤ, IsSDS 256 3 f :=
  Signed39.Template.eleven_shape_exclusion G 227 256 3 8 62 3 hg (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

end Signed39.Contraction
