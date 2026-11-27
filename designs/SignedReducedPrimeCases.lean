import SignedProjectedWords
import Signed39Analytic

namespace Signed39.Contraction

open Finset

set_option maxRecDepth 15000
set_option maxHeartbeats 6000000

private def W83 (x:ZMod 83) : ℤ := ([0, 0, 0, 5, 40, 28, 5, 37, 40, 10, 27, 29, 4, 3, 37, 33, 39, 13, 10, 18, 27, 1, 29, 11, 4, 14, 2, 15, 36, 35, 32, 22, 39, 34, 13, 24, 9, 31, 17, 8, 26, 21, 1, 6, 28, 38, 11, 30, 3, 33, 14, 18, 2, 12, 15, 16, 36, 23, 35, 24, 32, 8, 22, 6, 38, 30, 34, 19, 12, 16, 23, 25, 9, 7, 31, 19, 17, 25, 7, 20, 26, 20, 21]:List ℤ).getD x.val 0
theorem fixed_mass_83 (u:ZMod 83→ℤ) (fix:∀x,u (4*x)=u x) : (41:ℤ)∣mass u-u 0 := by
  let E:=scalarPerm (H:=ZMod 83) 4 21 (by rw [ZMod.card]; decide)
  have scale (x:ZMod 83) : E x=4*x:=nsmul_eq_mul _ _
  have weights : ∀x:ZMod 83,(41:ℤ)∣(if x=0 then (0:ℤ) else 1)+W83 (4*x)-W83 x := by decide +kernel
  exact orbit_mass_dvd E.toEquiv u W83 41 0 (fun x=>by change u (E x)=u x; rw [scale,fix])
    (fun x=>by change (41:ℤ) ∣ (if x=0 then (0:ℤ) else 1)+W83 (E x)-W83 x; rw [scale]; exact weights x)

private def W127 (x:ZMod 127) : ℤ := ([0, 0, 27, 0, 54, 20, 27, 6, 18, 62, 47, 29, 54, 16, 33, 19, 45, 44, 26, 21, 11, 5, 56, 3, 18, 39, 43, 62, 60, 7, 46, 40, 9, 29, 8, 25, 53, 14, 48, 16, 38, 23, 32, 28, 20, 19, 30, 33, 45, 11, 3, 44, 7, 10, 26, 49, 24, 21, 34, 4, 10, 24, 4, 5, 36, 36, 56, 42, 35, 2, 52, 55, 17, 57, 41, 39, 12, 35, 43, 13, 2, 61, 50, 52, 59, 1, 55, 6, 47, 17, 46, 22, 57, 40, 60, 41, 9, 15, 38, 28, 30, 12, 8, 49, 34, 25, 37, 42, 53, 58, 13, 14, 51, 1, 48, 22, 61, 15, 31, 50, 37, 58, 51, 23, 31, 59, 32]:List ℤ).getD x.val 0
theorem fixed_mass_127 (u:ZMod 127→ℤ) (fix:∀x,u (9*x)=u x) : (63:ℤ)∣mass u-u 0 := by
  let E:=scalarPerm (H:=ZMod 127) 9 113 (by rw [ZMod.card]; decide)
  have scale (x:ZMod 127) : E x=9*x:=nsmul_eq_mul _ _
  have weights : ∀x:ZMod 127,(63:ℤ)∣(if x=0 then (0:ℤ) else 1)+W127 (9*x)-W127 x := by decide +kernel
  exact orbit_mass_dvd E.toEquiv u W127 63 0 (fun x=>by change u (E x)=u x; rw [scale,fix])
    (fun x=>by change (63:ℤ) ∣ (if x=0 then (0:ℤ) else 1)+W127 (E x)-W127 x; rw [scale]; exact weights x)

private def W251 (x:ZMod 251) : ℤ := ([0, 0, 0, 124, 80, 70, 124, 47, 80, 123, 70, 64, 79, 98, 47, 69, 35, 11, 123, 67, 25, 46, 19, 61, 79, 15, 98, 122, 2, 72, 69, 4, 35, 63, 11, 117, 78, 33, 22, 97, 25, 31, 46, 93, 19, 68, 61, 50, 34, 94, 15, 10, 53, 102, 122, 9, 2, 66, 27, 74, 24, 52, 4, 45, 115, 43, 18, 56, 91, 60, 117, 108, 78, 76, 113, 14, 22, 111, 97, 88, 105, 121, 31, 41, 1, 81, 48, 71, 99, 36, 68, 20, 16, 3, 5, 12, 34, 26, 94, 62, 95, 54, 10, 28, 53, 116, 57, 118, 77, 23, 89, 32, 82, 100, 21, 6, 27, 96, 29, 58, 24, 83, 7, 30, 84, 85, 45, 44, 115, 92, 43, 64, 18, 114, 56, 67, 91, 106, 60, 42, 72, 49, 63, 37, 33, 17, 76, 93, 113, 50, 14, 55, 102, 9, 66, 74, 52, 90, 88, 101, 105, 108, 121, 59, 111, 8, 41, 86, 1, 71, 81, 65, 48, 12, 26, 62, 99, 73, 36, 118, 23, 32, 20, 51, 16, 103, 3, 75, 5, 44, 92, 109, 114, 112, 106, 42, 49, 37, 17, 13, 95, 55, 54, 119, 90, 101, 28, 59, 8, 86, 116, 65, 57, 107, 73, 38, 77, 51, 103, 75, 89, 109, 112, 87, 82, 13, 100, 119, 21, 104, 6, 110, 107, 38, 96, 120, 29, 87, 58, 39, 104, 110, 83, 120, 7, 39, 30, 40, 84, 40, 85]:List ℤ).getD x.val 0
theorem fixed_mass_251 (u:ZMod 251→ℤ) (fix:∀x,u (3*x)=u x) : (125:ℤ)∣mass u-u 0 := by
  let E:=scalarPerm (H:=ZMod 251) 3 84 (by rw [ZMod.card]; decide)
  have scale (x:ZMod 251) : E x=3*x:=nsmul_eq_mul _ _
  have weights : ∀x:ZMod 251,(125:ℤ)∣(if x=0 then (0:ℤ) else 1)+W251 (3*x)-W251 x := by decide +kernel
  exact orbit_mass_dvd E.toEquiv u W251 125 0 (fun x=>by change u (E x)=u x; rw [scale,fix])
    (fun x=>by change (125:ℤ) ∣ (if x=0 then (0:ℤ) else 1)+W251 (E x)-W251 x; rw [scale]; exact weights x)

theorem reduced_3937_777 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=3937) :
    ¬∃f:G→ℤ,IsSDS 777 2 f := by
  let : Fact (Nat.Prime 5):=⟨by decide⟩
  rintro ⟨f,hf⟩
  obtain ⟨φ,onto⟩:=exists_prime_quotient 127 (by decide) (hg ▸ (by decide : 127∣3937))
  obtain ⟨u,mu,fu⟩:=normalized_proj_word hf φ onto 3937 127 31 775 62 93 hg (ZMod.card 127) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨w,mw,fw⟩:=reduced_flat_word (q:=5) u 127 775 62 (-1) 44 31 15 (by rw [ZMod.card]; rfl) fu (by simpa using mu)
    (by decide) (by decide) 21 (by decide) (by rw [ZMod.card]; decide) (by decide) (by decide)
  obtain ⟨y,my,fy,cy⟩:=fixed_flat_quotient w 31 9 113 15 44 0 16 (by decide) fw mw
    (by decide) (by decide) [⟨31,1,11,63⟩] (by dsimp [compatibleFactors,factorProduct]; decide +kernel) (by decide)
  have res:=fixed_mass_127 y fy
  rw [my] at res
  have en:=coeff_square_le y 0; rw [cy] at en; norm_num at en
  have bd:-6≤y 0 ∧ y 0≤6:=by constructor <;> nlinarith [sq_nonneg (y 0-(7:ℤ)),sq_nonneg (y 0+(7:ℤ))]
  omega
#print axioms reduced_3937_777

theorem reduced_7781_869 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=7781) :
    ¬∃f:G→ℤ,IsSDS 869 1 f := by
  let : Fact (Nat.Prime 2):=⟨by decide⟩
  rintro ⟨f,hf⟩
  obtain ⟨φ,onto⟩:=exists_prime_quotient 251 (by decide) (hg ▸ (by decide : 251∣7781))
  obtain ⟨u,mu,fu⟩:=normalized_proj_word hf φ onto 7781 251 31 868 31 93 hg (ZMod.card 251) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨w,mw,fw⟩:=reduced_flat_word (q:=2) u 251 868 31 1 (-79) 217 24 (by rw [ZMod.card]; rfl) fu (by simpa using mu)
    (by decide) (by decide) 25 (by decide) (by rw [ZMod.card]; decide) (by decide) (by decide)
  obtain ⟨y,my,fy,cy⟩:=fixed_flat_quotient w 217 3 84 24 (-79) 0 126 (by decide) fw mw
    (by decide) (by decide) [⟨7,1,117,125⟩,⟨31,1,31,125⟩] (by dsimp [compatibleFactors,factorProduct]; decide +kernel) (by decide)
  have res:=fixed_mass_251 y fy
  rw [my] at res
  have en:=coeff_square_le y 0; rw [cy] at en; norm_num at en
  have bd:-15≤y 0 ∧ y 0≤15:=by constructor <;> nlinarith [sq_nonneg (y 0-(16:ℤ)),sq_nonneg (y 0+(16:ℤ))]
  omega
#print axioms reduced_7781_869

end Signed39.Contraction
