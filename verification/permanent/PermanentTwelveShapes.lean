import PermanentBlockShapes

/-! Representatives of the twelve-cell subboards and their thirteen-cell parents. -/

namespace PermanentFive
open Finset
def thirteenShape : Fin 4 → Finset Cell :=
  ![rowPairBoard, colPairBoard, crossPairBoard, mixedBoard]

def twelveShape : Fin 9 → Finset Cell :=
  ![threeRows \ {(0,0),(0,1),(0,2)}, threeRows \ {(0,0),(0,1),(1,0)},
    threeRows \ {(0,0),(0,1),(1,2)}, threeRows \ {(0,0),(1,0),(2,0)},
    threeRows \ {(0,0),(1,0),(2,1)}, threeRows \ {(0,0),(1,1),(2,2)},
    mixedBoard.erase (0,0), mixedBoard.erase (0,1), mixedBoard.erase (2,0)]

theorem thirteenShape_card : ∀ t, (thirteenShape t).card = 13 := by decide +kernel
end PermanentFive
