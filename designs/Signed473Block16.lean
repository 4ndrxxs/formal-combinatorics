import Signed473Template

namespace Signed39.Template

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def template16 : Case := ⟨⟨[-10,5,1,-4,-5,0,-2,4,5,3,3],
  [18,17,2,14,8]⟩,1,0⟩
theorem checked16 : checked template16 16 := by decide +kernel

def template17 : Case := ⟨⟨[-10,-1,-2,3,-1,-6,7,1,3,4,2],
  [16,12,8,3,20]⟩,6,0⟩
theorem checked17 : checked template17 17 := by decide +kernel

def template18 : Case := ⟨⟨[-11,2,1,-1,5,3,-3,1,7,-3,-1],
  [13,6,3,21,15]⟩,8,0⟩
theorem checked18 : checked template18 18 := by decide +kernel

def template19 : Case := ⟨⟨[-10,1,3,2,7,-2,4,-6,-1,3,-1],
  [8,20,12,16,3]⟩,4,0⟩
theorem checked19 : checked template19 19 := by decide +kernel

def template20 : Case := ⟨⟨[-10,1,-5,-2,5,3,5,-4,0,4,3],
  [8,18,14,17,2]⟩,4,0⟩
theorem checked20 : checked template20 20 := by decide +kernel

def template21 : Case := ⟨⟨[-11,7,3,1,-1,1,5,2,-3,-3,-1],
  [21,3,13,15,6]⟩,1,0⟩
theorem checked21 : checked template21 21 := by decide +kernel

def template22 : Case := ⟨⟨[-10,-2,-1,7,3,2,-1,3,-6,1,4],
  [20,16,3,12,8]⟩,3,0⟩
theorem checked22 : checked template22 22 := by decide +kernel

def template23 : Case := ⟨⟨[-10,-6,2,-1,4,3,3,-2,1,-1,7],
  [12,3,20,8,16]⟩,10,0⟩
theorem checked23 : checked template23 23 := by decide +kernel

end Signed39.Template
