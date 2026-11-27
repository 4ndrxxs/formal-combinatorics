import Signed473Template

namespace Signed39.Template

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def template24 : Case := ⟨⟨[-10,-2,5,4,1,5,-4,3,-5,3,0],
  [17,14,8,2,18]⟩,2,0⟩
theorem checked24 : checked template24 24 := by decide +kernel

def template25 : Case := ⟨⟨[-11,-3,2,1,1,7,-1,-3,5,-1,3],
  [6,21,15,3,13]⟩,5,0⟩
theorem checked25 : checked template25 25 := by decide +kernel

def template26 : Case := ⟨⟨[-10,-4,-2,3,5,-5,4,3,1,0,5],
  [14,2,18,8,17]⟩,4,0⟩
theorem checked26 : checked template26 26 := by decide +kernel

def template27 : Case := ⟨⟨[-10,4,-4,3,-2,1,3,0,5,5,-5],
  [2,8,17,18,14]⟩,8,0⟩
theorem checked27 : checked template27 27 := by decide +kernel

def template28 : Case := ⟨⟨[-11,1,5,-3,7,-1,2,-1,3,1,-3],
  [15,13,21,6,3]⟩,4,0⟩
theorem checked28 : checked template28 28 := by decide +kernel

def template29 : Case := ⟨⟨[-5,-5,-5,4,-5,5,4,-5,4,4,4],
  [9,2,16,6,8]⟩,5,0⟩
theorem checked29 : checked template29 29 := by decide +kernel

def template30 : Case := ⟨⟨[-10,3,7,4,-1,-1,1,2,-2,-6,3],
  [3,8,16,20,12]⟩,2,0⟩
theorem checked30 : checked template30 30 := by decide +kernel

def template31 : Case := ⟨⟨[-11,1,-1,-1,-3,1,-3,3,2,7,5],
  [3,15,6,13,21]⟩,9,0⟩
theorem checked31 : checked template31 31 := by decide +kernel

end Signed39.Template
