import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! A coprime polynomial pencil P(t)+u Q(t) is irreducible over K(u)
when P has larger degree. Both degrees refer to t. -/

noncomputable section
open Polynomial
namespace PermanentCurve
variable {K : Type*} [Field K]

def graph (P Q : K[X]) : (RatFunc K)[X] :=
  P.map RatFunc.C + C RatFunc.X * Q.map RatFunc.C

private def bivar (P Q : K[X]) : K[X][X] :=
  P.map C + C X * Q.map C

private theorem bivar_irreducible (P Q : K[X]) (nz : Q ≠ 0) (cop : IsCoprime Q P) :
    Irreducible (bivar P Q) := by
  have src : Irreducible (C Q * X + C P) := irreducible_C_mul_X_add_C nz cop.isRelPrime
  have eq : bivar P Q = Bivariate.swap (C Q * X + C P) := by
    simp only [map_add,map_mul,Bivariate.swap_C,Bivariate.swap_Y,bivar]
    ring
  rw [eq,MulEquiv.irreducible_iff]
  exact src

theorem graph_natDegree (P Q : K[X]) (hi : Q.natDegree < P.natDegree) :
    (graph P Q).natDegree = P.natDegree := by
  have pc := Polynomial.natDegree_map_eq_of_injective RatFunc.C_injective (p:=P)
  have bound := Polynomial.natDegree_C_mul_le (RatFunc.X : RatFunc K) (Q.map RatFunc.C)
  rw [graph,natDegree_add_eq_left_of_natDegree_lt]
  · exact pc
  · exact (bound.trans (Polynomial.natDegree_map_le)).trans_lt (hi.trans_eq pc.symm)

theorem graph_irreducible (P Q : K[X]) (nz : Q ≠ 0) (cop : IsCoprime Q P)
    (hi : Q.natDegree < P.natDegree) : Irreducible (graph P Q) := by
  let F := bivar P Q
  have move : F.map (algebraMap K[X] (RatFunc K)) = graph P Q := by
    simp only [F,bivar,graph,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_map,
      Polynomial.map_C,RatFunc.algebraMap_X]
    rfl
  have irr := bivar_irreducible P Q nz cop
  have primitive : F.IsPrimitive := by
    apply irr.isPrimitive
    intro zero
    have bound := Polynomial.natDegree_map_le (f:=algebraMap K[X] (RatFunc K)) (p:=F)
    rw [move,graph_natDegree P Q hi] at bound
    change F.natDegree = 0 at zero
    rw [zero] at bound
    omega
  rw [←move,← primitive.irreducible_iff_irreducible_map_fraction_map]
  exact irr

#print axioms graph_irreducible
end PermanentCurve
