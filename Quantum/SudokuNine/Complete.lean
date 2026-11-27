module
public import Quantum.SudokuNine.Part02
public import Quantum.SudokuNine.Part03
public import Quantum.SudokuNine.Part04
public import Quantum.SudokuNine.Part05
public import Quantum.SudokuNine.Part06
public import Quantum.SudokuNine.Part07
public import Quantum.SudokuNine.Part08
public import Quantum.SudokuNine.Part09
public import Quantum.SudokuNine.Part10
public import Quantum.SudokuNine.Part11
public import Quantum.SudokuNine.Part12
public import Quantum.SudokuNine.Part13
public import Quantum.SudokuNine.Part14
public import Quantum.SudokuNine.Part15
public import Quantum.SudokuNine.Part16
public import Quantum.SudokuNine.Part17
public import Quantum.SudokuNine.Part18
public import Quantum.SudokuNine.Part19
public import Quantum.SudokuNine.Part20

@[expose] public section
namespace SudokuNine
open QuantumSudoku

def verified : List ℕ := [9,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,66,68,69,70,71,72,75,76,77,78,79,80,81]

theorem realized (c : ℕ) (h : c∈verified) : Realizes 3 c := by
  simp only [verified,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact C9.realized
  · exact C11.realized
  · exact C12.realized
  · exact C13.realized
  · exact C14.realized
  · exact C15.realized
  · exact C16.realized
  · exact C17.realized
  · exact C18.realized
  · exact C19.realized
  · exact C20.realized
  · exact C21.realized
  · exact C22.realized
  · exact C23.realized
  · exact C24.realized
  · exact C25.realized
  · exact C26.realized
  · exact C27.realized
  · exact C28.realized
  · exact C29.realized
  · exact C30.realized
  · exact C31.realized
  · exact C32.realized
  · exact C33.realized
  · exact C34.realized
  · exact C35.realized
  · exact C36.realized
  · exact C37.realized
  · exact C38.realized
  · exact C39.realized
  · exact C40.realized
  · exact C41.realized
  · exact C42.realized
  · exact C43.realized
  · exact C44.realized
  · exact C45.realized
  · exact C46.realized
  · exact C47.realized
  · exact C48.realized
  · exact C49.realized
  · exact C50.realized
  · exact C51.realized
  · exact C52.realized
  · exact C53.realized
  · exact C54.realized
  · exact C55.realized
  · exact C56.realized
  · exact C57.realized
  · exact C58.realized
  · exact C59.realized
  · exact C60.realized
  · exact C61.realized
  · exact C62.realized
  · exact C63.realized
  · exact C64.realized
  · exact C66.realized
  · exact C68.realized
  · exact C69.realized
  · exact C70.realized
  · exact C71.realized
  · exact C72.realized
  · exact C75.realized
  · exact C76.realized
  · exact C77.realized
  · exact C78.realized
  · exact C79.realized
  · exact C80.realized
  · exact C81.realized
#print axioms realized

end SudokuNine
