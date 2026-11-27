import SignedElevenShapes

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem frontier_mixed_539_310_57 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=539) :
    ¬∃f:G→ℤ, IsSDS 310 57 f :=
  Signed39.Template.eleven_shape_exclusion G 49 310 57 16 9 2 hg (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

end Signed39.Contraction
