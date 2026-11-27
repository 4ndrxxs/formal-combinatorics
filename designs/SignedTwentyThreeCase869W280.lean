import SignedElevenShapes

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem frontier_mixed_869_280_27 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=869) :
    ¬∃f:G→ℤ, IsSDS 280 27 f :=
  Signed39.Template.eleven_shape_exclusion G 79 280 27 14 36 5 hg (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

end Signed39.Contraction
