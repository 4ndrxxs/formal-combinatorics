import PermanentCurveIrreducible
import Mathlib.Tactic

/-! Integer polynomials defining an irreducible degree-fifteen restriction
of the complementary cubic determinant. The Bézout identity holds before
extension of the coefficient field. -/

noncomputable section
open Polynomial
namespace PermanentCurve
variable {R : Type*} [CommRing R]

def curveP (x : R) : R := (-3) + (7)*x + (-25)*x^2 + (61)*x^3 + (149)*x^4 + (-79)*x^5 + (-696)*x^6 + (782)*x^7 + (-433)*x^8 + (-743)*x^9 + (1318)*x^10 + (-548)*x^11 + (-82)*x^12 + (164)*x^13 + (-24)*x^14 + (-16)*x^15

def curveQ (x : R) : R := (-6) + (23)*x + (-27)*x^2 + (57)*x^3 + (-25)*x^4 + (-31)*x^5 + (1)*x^6 + (-282)*x^7 + (164)*x^8 + (-201)*x^9 + (329)*x^10 + (-54)*x^11 + (-52)*x^12 + (8)*x^13

private def bezU (x : R) : R := (21701154399483022149877100307075) + (-8644630554419955003303595173610)*x + (180402427740258950488189477374803)*x^2 + (-61911369117968301304330676985312)*x^3 + (-1168555340304340093149567550611509)*x^4 + (-1665574683847488368168793754440156)*x^5 + (1917881247280603171182247979707428)*x^6 + (-2031236913787334387238519885511298)*x^7 + (-785849413994989444963513695616509)*x^8 + (3924935355084502817894088752330132)*x^9 + (-2095349161880612382114378026301498)*x^10 + (-18988972748486657260822392329122)*x^11 + (559693659860653532720965297464212)*x^12 + (-123844240179646663375562464022392)*x^13 + (-61057830297938146743610834204400)*x^14

private def bezV (x : R) : R := (-45908883176378592158529606044934) + (76544050759993031452429211929949)*x + (-61213934416612747307185542299960)*x^2 + (282851398266142525851732921877889)*x^3 + (340101284298082009133497016330166)*x^4 + (407279989711347122297155521180971)*x^5 + (791084837267996908095235466992214)*x^6 + (-534794439511678318481096972569088)*x^7 + (193510350664653730717483123938580)*x^8 + (-1093934613143010769677356347867597)*x^9 + (302025605839892782599748539737574)*x^10 + (182309201101929255286662104806404)*x^11 + (-30528915148969073371805417102200)*x^12

private theorem bezout (x : R) :
    bezU x * curveQ x + bezV x * curveP x = 7519723132237643576326216292352 := by
  unfold bezU bezV curveQ curveP
  ring

theorem map_curveP {S : Type*} [CommRing S] (f : R →+* S) (x : R) :
    f (curveP x) = curveP (f x) := by simp only [curveP, map_add, map_mul, map_pow, map_neg, map_ofNat]

theorem map_curveQ {S : Type*} [CommRing S] (f : R →+* S) (x : R) :
    f (curveQ x) = curveQ (f x) := by simp only [curveQ, map_add, map_mul, map_pow, map_neg, map_ofNat, map_one]

variable (K : Type*) [Field K] [CharZero K]

theorem curve_degrees : (curveP (X : K[X])).natDegree = 15 ∧
    (curveQ (X : K[X])).natDegree = 13 := by
  constructor
  · unfold curveP
    compute_degree!
  · unfold curveQ
    compute_degree!

theorem curve_coprime : IsCoprime (curveQ (X : K[X])) (curveP X) := by
  let n : K := 7519723132237643576326216292352
  have nz : n ≠ 0 := by dsimp [n]; norm_num
  refine ⟨C n⁻¹ * bezU X,C n⁻¹ * bezV X,?_⟩
  rw [mul_assoc,mul_assoc,←mul_add,bezout]
  change C n⁻¹ * (7519723132237643576326216292352 : K[X]) = 1
  rw [show (7519723132237643576326216292352 : K[X]) = C n by dsimp [n]; rw [map_ofNat],←map_mul,inv_mul_cancel₀ nz,map_one]

def obstructionPolynomial : (RatFunc K)[X] := graph (curveP (X : K[X])) (curveQ X)

theorem obstruction_irreducible : Irreducible (obstructionPolynomial K) := by
  obtain ⟨p,q⟩ := curve_degrees K
  apply graph_irreducible _ _ _ (curve_coprime K) (by omega)
  intro zero
  rw [zero,natDegree_zero] at q
  contradiction

theorem obstruction_degree : (obstructionPolynomial K).natDegree = 15 := by
  obtain ⟨p,q⟩ := curve_degrees K
  exact (graph_natDegree _ _ (by omega)).trans p

#print axioms obstruction_irreducible
#print axioms obstruction_degree
end PermanentCurve
