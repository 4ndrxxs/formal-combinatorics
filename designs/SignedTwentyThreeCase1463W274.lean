import SignedElevenShapes

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem frontier_mixed_1463_274_21 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=1463) :
    ¬∃f:G→ℤ, IsSDS 274 21 f :=
  Signed39.Template.eleven_shape_exclusion G 133 274 21 16 121 10 hg (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

end Signed39.Contraction
