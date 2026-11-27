import SignedElevenShapes

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem frontier_mixed_913_625_372 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=913) :
    ¬∃f:G→ℤ, IsSDS 625 372 f :=
  Signed39.Template.eleven_shape_exclusion G 83 625 372 53 68 9 hg (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

end Signed39.Contraction
