import PermanentFive

/-! Four canonical boards with thirteen cells, up to row and column
permutations and transpose. Each is used for a nonsingular Hessian block. -/

namespace PermanentFive
open Finset
def threeRows : Finset Cell := univ.filter (fun x ↦ x.1.val < 3)
def mixedBoard : Finset Cell := univ.filter (fun x ↦ x.1.val < 2 ∨ x.2.val < 1)
def rowPairBoard : Finset Cell := (threeRows.erase (0,0)).erase (0,1)
def colPairBoard : Finset Cell := (threeRows.erase (0,0)).erase (1,0)
def crossPairBoard : Finset Cell := (threeRows.erase (0,0)).erase (1,1)
end PermanentFive
