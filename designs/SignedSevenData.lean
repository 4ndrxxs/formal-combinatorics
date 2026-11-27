import SignedFiniteProfiles

namespace Signed39.Profiles

def seven (f : ZMod 7 → ℤ) : List ℤ := [f 0,f 1,f 2,f 3,f 4,f 5,f 6]

theorem sum_seven (f : ZMod 7 → ℤ) : (∑ i,f i)=f 0+f 1+f 2+f 3+f 4+f 5+f 6 := by
  have U : (Finset.univ : Finset (ZMod 7))={0,1,2,3,4,5,6} := by decide
  rw [U]
  simp (config:={ decide := true })
  ring

theorem seven_sum (f : ZMod 7 → ℤ) : (seven f).sum=∑i,f i := by
  rw [sum_seven]; simp [seven]; ring

def flatSixteen : List ℤ → Prop
  | [a,b,c,d,e,f,g] => a*b+b*c+c*d+d*e+e*f+f*g+g*a= -16 ∧
      a*c+b*d+c*e+d*f+e*g+f*a+g*b= -16 ∧ a*d+b*e+c*f+d*g+e*a+f*b+g*c= -16
  | _ => False

instance (L : List ℤ) : Decidable (flatSixteen L) := by unfold flatSixteen; split <;> infer_instance

def massAlphabet : List ℤ := (List.range 19).map (fun x : ℕ => (x:ℤ)-9)
def sevenPatterns : List (List ℤ) := [[-9,1,1,1,2,2,2],[-6,-2,-2,-2,4,4,4],[-4,-4,-4,0,4,4,4],
  [-4,-4,-4,2,2,2,6],[-2,-2,-2,-1,-1,-1,9]]

open Finset Contraction

theorem list_flat_sixteen (x : ZMod 7 → ℤ) (h1 : corr x 1= -16) (h2 : corr x 2= -16) (h3 : corr x 3= -16) :
    flatSixteen (seven x) := by
  unfold corr at h1 h2 h3
  rw [sum_seven] at h1 h2 h3
  exact ⟨h1,h2,h3⟩

theorem seven_spectrum (x : ZMod 7 → ℤ) (sm : mass x=0) (sq : energy x=96) :
    ∃ L∈shortWords massAlphabet 7 (-9) 0 96, (seven x).Perm L ∧ seven x∈orders 7 L := by
  have bounds (i : ZMod 7) : -9≤x i ∧ x i≤9 := by
    have le : (x i)^2≤96 := sq ▸ single_le_sum (fun _ _=>sq_nonneg _) (mem_univ i)
    constructor
    · by_contra! h; nlinarith [mul_nonneg (show 0≤ -10-x i by omega) (show 0≤10-x i by omega)]
    · by_contra! h; nlinarith [mul_nonneg (show 0≤x i-10 by omega) (show 0≤x i+10 by omega)]
  have any (i:ZMod 7) : x i∈massAlphabet ∧ (-9:ℤ)≤x i := by
    have h:=bounds i
    refine ⟨?_,h.1⟩
    unfold massAlphabet
    let n := (x i+9).toNat
    have small : n<19 := by dsimp [n]; omega
    have eq : (n:ℤ)-9=x i := by dsimp [n]; omega
    exact List.mem_map.mpr ⟨n,List.mem_range.mpr small,eq⟩
  apply short_possible (xs:=seven x)
  · intro y mem
    simp only [seven,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> apply any
  · exact (seven_sum x).trans sm
  · unfold energy at sq
    rw [sum_seven] at sq
    simpa [squareSum,seven,add_assoc] using sq

end Signed39.Profiles
