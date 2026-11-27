import PermanentWeightedWords
noncomputable section
open Matrix Equiv Finset MvPolynomial QuinticPencil PermanentFive PermanentBorder
namespace PermanentArrow.Weighted
variable {R : Type*} [CommRing R]
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
private theorem f12 : firstWords (I:=Fin 3) (1,2)=(((0,0) ::ₘ (2,1) ::ₘ 0) ::ₘ ((2,0) ::ₘ (0,1) ::ₘ 0) ::ₘ 0) := by decide +kernel
private theorem f10 : firstWords (I:=Fin 3) (1,0)=(((0,1) ::ₘ (2,2) ::ₘ 0) ::ₘ ((2,1) ::ₘ (0,2) ::ₘ 0) ::ₘ 0) := by decide +kernel
private theorem f02 : firstWords (I:=Fin 3) (0,2)=(((1,0) ::ₘ (2,1) ::ₘ 0) ::ₘ ((2,0) ::ₘ (1,1) ::ₘ 0) ::ₘ 0) := by decide +kernel
private theorem f00 : firstWords (I:=Fin 3) (0,0)=(((1,1) ::ₘ (2,2) ::ₘ 0) ::ₘ ((2,1) ::ₘ (1,2) ::ₘ 0) ::ₘ 0) := by decide +kernel
private theorem base_first (s : Fin 3→R) :
    gradAt (board 0 s) (0,0)=prodAll 0 s ∧ firstJet 0 1 2 s=0 := by
  constructor
  · rw [first_eval,f00]
    norm_num [evalWords,board,total,prodAll,skip,Fin.sum_univ_succ,Fin.prod_univ_succ]
  · unfold firstJet
    simp only [first_eval,f12,f10,f02,f00]
    norm_num [evalWords,board,total,prodAll,skip,Fin.sum_univ_succ,Fin.prod_univ_succ]
private theorem h1200 : secondWords (I:=Fin 3) (1,2) (0,0)=(((2,1) ::ₘ 0) ::ₘ 0) := by decide +kernel
private theorem h1000 : secondWords (I:=Fin 3) (1,0) (0,0)=(0) := by decide +kernel
private theorem h0200 : secondWords (I:=Fin 3) (0,2) (0,0)=(0) := by decide +kernel
private theorem h0000 : secondWords (I:=Fin 3) (0,0) (0,0)=(0) := by decide +kernel
private theorem row_0_0 (s : Fin 3→R) : rowJet 0 1 2 s (0,0)= 0 := by
  simp only [rowJet,second_eval,h1200,h1000,h0200,h0000]
  norm_num [evalWords,board,total,prodAll,skip,Fin.sum_univ_succ,Fin.prod_univ_succ]
private theorem h1201 : secondWords (I:=Fin 3) (1,2) (0,1)=(((2,0) ::ₘ 0) ::ₘ 0) := by decide +kernel
private theorem h1001 : secondWords (I:=Fin 3) (1,0) (0,1)=(((2,2) ::ₘ 0) ::ₘ 0) := by decide +kernel
private theorem h0201 : secondWords (I:=Fin 3) (0,2) (0,1)=(0) := by decide +kernel
private theorem h0001 : secondWords (I:=Fin 3) (0,0) (0,1)=(0) := by decide +kernel
private theorem row_0_1 (s : Fin 3→R) : rowJet 0 1 2 s (0,1)= 0 := by
  simp only [rowJet,second_eval,h1201,h1001,h0201,h0001]
  norm_num [evalWords,board,total,prodAll,skip,Fin.sum_univ_succ,Fin.prod_univ_succ]
private theorem h1202 : secondWords (I:=Fin 3) (1,2) (0,2)=(0) := by decide +kernel
private theorem h1002 : secondWords (I:=Fin 3) (1,0) (0,2)=(((2,1) ::ₘ 0) ::ₘ 0) := by decide +kernel
private theorem h0202 : secondWords (I:=Fin 3) (0,2) (0,2)=(0) := by decide +kernel
private theorem h0002 : secondWords (I:=Fin 3) (0,0) (0,2)=(0) := by decide +kernel
private theorem row_0_2 (s : Fin 3→R) : rowJet 0 1 2 s (0,2)= 0 := by
  simp only [rowJet,second_eval,h1202,h1002,h0202,h0002]
  norm_num [evalWords,board,total,prodAll,skip,Fin.sum_univ_succ,Fin.prod_univ_succ]
private theorem h1210 : secondWords (I:=Fin 3) (1,2) (1,0)=(0) := by decide +kernel
private theorem h1010 : secondWords (I:=Fin 3) (1,0) (1,0)=(0) := by decide +kernel
private theorem h0210 : secondWords (I:=Fin 3) (0,2) (1,0)=(((2,1) ::ₘ 0) ::ₘ 0) := by decide +kernel
private theorem h0010 : secondWords (I:=Fin 3) (0,0) (1,0)=(0) := by decide +kernel
private theorem row_1_0 (s : Fin 3→R) : rowJet 0 1 2 s (1,0)= 0 := by
  simp only [rowJet,second_eval,h1210,h1010,h0210,h0010]
  norm_num [evalWords,board,total,prodAll,skip,Fin.sum_univ_succ,Fin.prod_univ_succ]
private theorem h1211 : secondWords (I:=Fin 3) (1,2) (1,1)=(0) := by decide +kernel
private theorem h1011 : secondWords (I:=Fin 3) (1,0) (1,1)=(0) := by decide +kernel
private theorem h0211 : secondWords (I:=Fin 3) (0,2) (1,1)=(((2,0) ::ₘ 0) ::ₘ 0) := by decide +kernel
private theorem h0011 : secondWords (I:=Fin 3) (0,0) (1,1)=(((2,2) ::ₘ 0) ::ₘ 0) := by decide +kernel
private theorem row_1_1 (s : Fin 3→R) : rowJet 0 1 2 s (1,1)= 0 := by
  simp only [rowJet,second_eval,h1211,h1011,h0211,h0011]
  norm_num [evalWords,board,total,prodAll,skip,Fin.sum_univ_succ,Fin.prod_univ_succ]
private theorem h1212 : secondWords (I:=Fin 3) (1,2) (1,2)=(0) := by decide +kernel
private theorem h1012 : secondWords (I:=Fin 3) (1,0) (1,2)=(0) := by decide +kernel
private theorem h0212 : secondWords (I:=Fin 3) (0,2) (1,2)=(0) := by decide +kernel
private theorem h0012 : secondWords (I:=Fin 3) (0,0) (1,2)=(((2,1) ::ₘ 0) ::ₘ 0) := by decide +kernel
private theorem row_1_2 (s : Fin 3→R) : rowJet 0 1 2 s (1,2)= 0 := by
  simp only [rowJet,second_eval,h1212,h1012,h0212,h0012]
  norm_num [evalWords,board,total,prodAll,skip,Fin.sum_univ_succ,Fin.prod_univ_succ]
private theorem h1220 : secondWords (I:=Fin 3) (1,2) (2,0)=(((0,1) ::ₘ 0) ::ₘ 0) := by decide +kernel
private theorem h1020 : secondWords (I:=Fin 3) (1,0) (2,0)=(0) := by decide +kernel
private theorem h0220 : secondWords (I:=Fin 3) (0,2) (2,0)=(((1,1) ::ₘ 0) ::ₘ 0) := by decide +kernel
private theorem h0020 : secondWords (I:=Fin 3) (0,0) (2,0)=(0) := by decide +kernel
private theorem row_2_0 (s : Fin 3→R) : rowJet 0 1 2 s (2,0)= 0 := by
  simp only [rowJet,second_eval,h1220,h1020,h0220,h0020]
  norm_num [evalWords,board,total,prodAll,skip,Fin.sum_univ_succ,Fin.prod_univ_succ]
private theorem h1221 : secondWords (I:=Fin 3) (1,2) (2,1)=(((0,0) ::ₘ 0) ::ₘ 0) := by decide +kernel
private theorem h1021 : secondWords (I:=Fin 3) (1,0) (2,1)=(((0,2) ::ₘ 0) ::ₘ 0) := by decide +kernel
private theorem h0221 : secondWords (I:=Fin 3) (0,2) (2,1)=(((1,0) ::ₘ 0) ::ₘ 0) := by decide +kernel
private theorem h0021 : secondWords (I:=Fin 3) (0,0) (2,1)=(((1,2) ::ₘ 0) ::ₘ 0) := by decide +kernel
private theorem row_2_1 (s : Fin 3→R) : rowJet 0 1 2 s (2,1)= -2*(skip 0 1 s+skip 0 2 s) := by
  simp only [rowJet,second_eval,h1221,h1021,h0221,h0021]
  norm_num [evalWords,board,total,prodAll,skip,Fin.sum_univ_succ,Fin.prod_univ_succ]
  ring
private theorem h1222 : secondWords (I:=Fin 3) (1,2) (2,2)=(0) := by decide +kernel
private theorem h1022 : secondWords (I:=Fin 3) (1,0) (2,2)=(((0,1) ::ₘ 0) ::ₘ 0) := by decide +kernel
private theorem h0222 : secondWords (I:=Fin 3) (0,2) (2,2)=(0) := by decide +kernel
private theorem h0022 : secondWords (I:=Fin 3) (0,0) (2,2)=(((1,1) ::ₘ 0) ::ₘ 0) := by decide +kernel
private theorem row_2_2 (s : Fin 3→R) : rowJet 0 1 2 s (2,2)= 0 := by
  simp only [rowJet,second_eval,h1222,h1022,h0222,h0022]
  norm_num [evalWords,board,total,prodAll,skip,Fin.sum_univ_succ,Fin.prod_univ_succ]
theorem fixed_3 (s : Fin 3→R) (v : CellOf (Fin 3)) : Law 0 1 2 s v := by
  refine ⟨(base_first s).1,(base_first s).2,?_⟩
  obtain ⟨a,b⟩ := v
  fin_cases a <;> fin_cases b
  · exact row_0_0 s
  · exact row_0_1 s
  · exact row_0_2 s
  · exact row_1_0 s
  · exact row_1_1 s
  · exact row_1_2 s
  · exact row_2_0 s
  · exact row_2_1 s
  · exact row_2_2 s
theorem anchor_3 : ∀ c i j : Fin 3, c≠i → c≠j → i≠j → ∃ v : Perm (Fin 3), v c=0 ∧ v i=1 ∧ v j=2 := by decide +kernel
end PermanentArrow.Weighted
