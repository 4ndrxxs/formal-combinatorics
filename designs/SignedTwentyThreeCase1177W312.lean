import SignedElevenShapes

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem frontier_mixed_1177_312_59 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=1177) :
    ¬∃f:G→ℤ, IsSDS 312 59 f :=
  Signed39.Template.eleven_shape_exclusion G 107 312 59 24 39 4 hg (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

end Signed39.Contraction
