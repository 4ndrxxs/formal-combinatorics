import SignedOrbit11Cofactor27

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem frontier_mixed_1441_324_27 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=1441) :
    ¬∃f:G→ℤ,IsSDS 324 27 f := Signed39.Shape.shape_11_27 G 131 324 27 18 12 1 hg (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

end Signed39.Contraction
