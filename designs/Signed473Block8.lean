import Signed473Template

namespace Signed39.Template

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def template8 : Case := ⟨⟨[-10,7,-1,1,-2,3,3,4,-1,2,-6],
  [12,3,20,8,16]⟩,1,0⟩
theorem checked8 : checked template8 8 := by decide +kernel

def template9 : Case := ⟨⟨[-10,4,1,-6,3,-1,2,3,7,-1,-2],
  [20,16,3,12,8]⟩,8,0⟩
theorem checked9 : checked template9 9 := by decide +kernel

def template10 : Case := ⟨⟨[-11,-1,-3,-3,2,5,1,-1,1,3,7],
  [21,3,13,15,6]⟩,10,0⟩
theorem checked10 : checked template10 10 := by decide +kernel

def template11 : Case := ⟨⟨[-10,3,4,0,-4,5,3,5,-2,-5,1],
  [8,18,14,17,2]⟩,5,0⟩
theorem checked11 : checked template11 11 := by decide +kernel

def template12 : Case := ⟨⟨[-10,-1,3,-1,-6,4,-2,7,2,3,1],
  [8,20,12,16,3]⟩,7,0⟩
theorem checked12 : checked template12 12 := by decide +kernel

def template13 : Case := ⟨⟨[-11,-1,-3,7,1,-3,3,5,-1,1,2],
  [13,6,3,21,15]⟩,3,0⟩
theorem checked13 : checked template13 13 := by decide +kernel

def template14 : Case := ⟨⟨[-10,2,4,3,1,7,-6,-1,3,-2,-1],
  [16,12,8,3,20]⟩,5,0⟩
theorem checked14 : checked template14 14 := by decide +kernel

def template15 : Case := ⟨⟨[-10,3,3,5,4,-2,0,-5,-4,1,5],
  [18,17,2,14,8]⟩,3,0⟩
theorem checked15 : checked template15 15 := by decide +kernel

end Signed39.Template
