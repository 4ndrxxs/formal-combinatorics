module
public import Quantum.DiagonalSpectrum

/-! Exact rational examples for all four cardinalities in order six. -/
@[expose] public section
namespace DiagonalSix.Examples
open QuantumCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def coefficients : Array ℤ := #[5, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 5, 3, 0, 0, 4, 0, 0, 4, 0, 0, -3, 0, 0, 0, 3, 0, 0, 0, 4, 0, 4, 0, 0, 0, -3, 0, 0, 3, 0, 4, 0, 0, 0, 4, 0, -3, 0]
def rep {c : ℕ} (w : Fin c) (j : Fin 6) : IQ := (coefficients[w.val*6+j.val]!,0)

def words6 : Array ℕ := #[0, 1, 2, 3, 4, 5, 5, 2, 3, 1, 0, 4, 4, 0, 5, 2, 1, 3, 2, 3, 1, 4, 5, 0, 1, 4, 0, 5, 3, 2, 3, 5, 4, 0, 2, 1]
def lab6 (p : Cell 6) : Fin 6 := Fin.ofNat 6 (words6[p.1.val*6+p.2.val]!)
theorem order6 : DiagonalRealized 6 6 := by
  apply diagonal_certificate (d:=1) (M:=25) (by decide) (by decide) rep lab6
  all_goals decide +kernel
#print axioms order6

def words8 : Array ℕ := #[0, 1, 2, 3, 4, 5, 5, 2, 3, 1, 0, 4, 4, 6, 5, 2, 1, 7, 2, 7, 1, 4, 5, 6, 1, 4, 0, 5, 3, 2, 3, 5, 4, 0, 2, 1]
def lab8 (p : Cell 6) : Fin 8 := Fin.ofNat 8 (words8[p.1.val*6+p.2.val]!)
theorem order8 : DiagonalRealized 6 8 := by
  apply diagonal_certificate (d:=1) (M:=25) (by decide) (by decide) rep lab8
  all_goals decide +kernel
#print axioms order8

def words10 : Array ℕ := #[0, 1, 2, 3, 4, 5, 9, 2, 3, 8, 0, 4, 4, 6, 5, 2, 1, 7, 2, 7, 1, 4, 5, 6, 8, 4, 0, 9, 3, 2, 3, 5, 4, 0, 2, 1]
def lab10 (p : Cell 6) : Fin 10 := Fin.ofNat 10 (words10[p.1.val*6+p.2.val]!)
theorem order10 : DiagonalRealized 6 10 := by
  apply diagonal_certificate (d:=1) (M:=25) (by decide) (by decide) rep lab10
  all_goals decide +kernel
#print axioms order10

def words12 : Array ℕ := #[0, 1, 10, 3, 11, 5, 9, 2, 3, 8, 0, 4, 4, 6, 5, 2, 1, 7, 2, 7, 1, 4, 5, 6, 8, 4, 0, 9, 3, 2, 3, 5, 11, 0, 10, 1]
def lab12 (p : Cell 6) : Fin 12 := Fin.ofNat 12 (words12[p.1.val*6+p.2.val]!)
theorem order12 : DiagonalRealized 6 12 := by
  apply diagonal_certificate (d:=1) (M:=25) (by decide) (by decide) rep lab12
  all_goals decide +kernel
#print axioms order12

end DiagonalSix.Examples
