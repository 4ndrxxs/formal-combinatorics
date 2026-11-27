module
public import Quantum.FractionalTwo.sameSource00
public import Quantum.FractionalTwo.sameSource01
public import Quantum.FractionalTwo.checked00
public import Quantum.FractionalTwo.checked01
public import Quantum.FractionalTwo.checked02
public import Quantum.FractionalTwo.checked03
public import Quantum.FractionalTwo.checked04
public import Quantum.FractionalTwo.checked05

@[expose] public section
namespace FractionalTwo
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open UniqueSudoku.Rup
private theorem sources : Interval sameSource 0 814 := (interval_join sameSource00 sameSource01)
private theorem traces : Interval checked 0 641 := (interval_join (interval_join checked00 (interval_join checked01 checked02)) (interval_join checked03 (interval_join checked04 checked05)))
theorem anchored_extension (t : Fin 64 → ℝ) (ht : Fractional t) (anchor : t 0=1) :
    ∃ j : Fin 288,Agrees t (candidate j) := by
  by_contra hd
  have sat (j : ℕ) (hj : j<nSource+nRows) : Holds (truth t) (db j) := by
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      by_cases first : j<nSource
      · have H := sources j (Nat.zero_le _) first
        rw [show db j=sourceMask (tags j) from beq_iff_eq.mp H]
        exact source_holds ht anchor hd (tags j)
      · let i:=j-nSource
        have hi : i<nRows := by dsimp [i];omega
        have he : nSource+i=j := by dsimp [i];omega
        apply derive _ (opposite t) db j (fun u hu => ih u hu (by omega)) (steps i)
        simpa only [checked,he] using traces i (Nat.zero_le _) hi
  have h := sat 1454 (by decide +kernel)
  rw [show db 1454=0 by decide +kernel] at h
  exact empty_false _ h
#print axioms anchored_extension
end FractionalTwo
