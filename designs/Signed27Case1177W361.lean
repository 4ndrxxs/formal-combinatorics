import SignedOrbit11Cofactor27

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem frontier_mixed_1177_361_64 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=1177) :
    ¬∃f:G→ℤ,IsSDS 361 64 f := Signed39.Shape.shape_11_27 G 107 361 64 25 39 4 hg (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

end Signed39.Contraction
