import Signed473Template

namespace Signed39.Template

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def template0 : Case := ⟨⟨[-11,5,7,2,3,-3,1,-3,-1,-1,1],
  [3,15,6,13,21]⟩,2,0⟩
theorem checked0 : checked template0 0 := by decide +kernel

def template1 : Case := ⟨⟨[-10,3,-6,-2,2,1,-1,-1,4,7,3],
  [3,8,16,20,12]⟩,9,0⟩
theorem checked1 : checked template1 1 := by decide +kernel

def template2 : Case := ⟨⟨[-5,-5,-5,4,4,4,-5,4,5,-5,4],
  [8,9,6,2,16]⟩,8,0⟩
theorem checked2 : checked template2 2 := by decide +kernel

def template3 : Case := ⟨⟨[-11,-3,1,3,-1,2,-1,7,-3,5,1],
  [15,13,21,6,3]⟩,7,0⟩
theorem checked3 : checked template3 3 := by decide +kernel

def template4 : Case := ⟨⟨[-10,-5,5,5,0,3,1,-2,3,-4,4],
  [2,8,17,18,14]⟩,2,0⟩
theorem checked4 : checked template4 4 := by decide +kernel

def template5 : Case := ⟨⟨[-10,5,0,1,3,4,-5,5,3,-2,-4],
  [14,2,18,8,17]⟩,1,0⟩
theorem checked5 : checked template5 5 := by decide +kernel

def template6 : Case := ⟨⟨[-11,3,-1,5,-3,-1,7,1,1,2,-3],
  [6,21,15,3,13]⟩,6,0⟩
theorem checked6 : checked template6 6 := by decide +kernel

def template7 : Case := ⟨⟨[-10,0,3,-5,3,-4,5,1,4,5,-2],
  [17,14,8,2,18]⟩,6,0⟩
theorem checked7 : checked template7 7 := by decide +kernel

end Signed39.Template
