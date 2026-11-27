import Signed47Cofactor27
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem fixed_47_27_false {G:Type} [AddCommGroup G] [Fintype G] [DecidableEq G] {m:ℕ} {k l:ℤ} {f:G→ℤ}
    (hf:IsSDS k l f) (hg:Fintype.card G=47*m) (_hm : 47 < m) (hn:k-l=(47:ℤ)*27) : False := by
  let : Fact (Nat.Prime 47) := ⟨by decide⟩
  have cop:=valuation_one_coprime hf hg hn (by decide : ¬(47:ℤ)∣27)
  exact Signed39.Shape.no_47_norm_1269 G hg cop hn ⟨f,hf⟩

end Signed39.Contraction
