import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-! An explicit system of four circulant T-matrices of order 271. A coordinate
is encoded as its signed standard basis vector: its low two bits specify
the coordinate and the high bit specifies the sign. -/

namespace Hadamard.PeriodicT
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 100000

structure System (q : ℕ) where
  entry : Fin 4 → Fin q → ℤ
  ternary : ∀ c j, entry c j = 0 ∨ entry c j = 1 ∨ entry c j = -1
  partition : ∀ j, ∃! c, entry c j ≠ 0
  correlation : ∀ t : Fin q, (∑ c, ∑ j, entry c j * entry c (j + t)) =
    if t.val = 0 then (q : ℤ) else 0

def code (i : ℕ) : Fin 8 :=
  ⟨(2894934125002565389846616472039998694333772995902815856702703365890262326116300518714474633275069201901385253866294625079269816693171972273858181441271307537937595973991265580623467523559770513238070341602775385005466788466716042378699053101320 >>> (3*i)) % 8, Nat.mod_lt _ (by decide)⟩

def component (c : Fin 4) (a : Fin 8) : ℤ :=
  if a.val % 4 = c.val then (if a.val < 4 then 1 else -1) else 0

def letterDot (a b : Fin 8) : ℤ :=
  if a.val % 4 = b.val % 4 then (if (a.val < 4) = (b.val < 4) then 1 else -1) else 0

private theorem components_agree : ∀ a b : Fin 8,
    letterDot a b = ∑ c, component c a * component c b := by decide +kernel

private theorem components_ternary : ∀ a : Fin 8, ∀ c : Fin 4,
    component c a = 0 ∨ component c a = 1 ∨ component c a = -1 := by decide +kernel

private theorem components_partition : ∀ a : Fin 8, ∃! c : Fin 4, component c a ≠ 0 := by
  unfold ExistsUnique
  decide +kernel

def dotPrefix (t : ℕ) : ℕ → ℤ
  | 0 => 0
  | j+1 => dotPrefix t j + letterDot (code j) (code ((j+t)%271))

private theorem dotPrefix_eq (t j : ℕ) : dotPrefix t j =
    ∑ x ∈ range j, letterDot (code x) (code ((x+t)%271)) := by
  induction j with
  | zero => simp [dotPrefix]
  | succ j ih => simp [dotPrefix, sum_range_succ, ih]

def test (a : ℕ) : ℕ → Bool
  | 0 => true
  | j+1 => test a j && (dotPrefix (a+j) 271 == (if a+j=0 then 271 else 0))

private theorem test_true {a j : ℕ} (h : test a j = true) {t : ℕ} (lo : a≤t) (hi : t<a+j) :
    dotPrefix t 271 = (if t=0 then 271 else 0) := by
  induction j with
  | zero => omega
  | succ j ih =>
    simp only [test, Bool.and_eq_true, beq_iff_eq] at h
    by_cases e : t=a+j
    · simpa [e] using h.2
    · exact ih h.1 (by omega)

private theorem test_0 : test 0 16 = true := by decide +kernel
private theorem test_1 : test 16 16 = true := by decide +kernel
private theorem test_2 : test 32 16 = true := by decide +kernel
private theorem test_3 : test 48 16 = true := by decide +kernel
private theorem test_4 : test 64 16 = true := by decide +kernel
private theorem test_5 : test 80 16 = true := by decide +kernel
private theorem test_6 : test 96 16 = true := by decide +kernel
private theorem test_7 : test 112 16 = true := by decide +kernel
private theorem test_8 : test 128 16 = true := by decide +kernel
private theorem test_9 : test 144 16 = true := by decide +kernel
private theorem test_10 : test 160 16 = true := by decide +kernel
private theorem test_11 : test 176 16 = true := by decide +kernel
private theorem test_12 : test 192 16 = true := by decide +kernel
private theorem test_13 : test 208 16 = true := by decide +kernel
private theorem test_14 : test 224 16 = true := by decide +kernel
private theorem test_15 : test 240 16 = true := by decide +kernel
private theorem test_16 : test 256 15 = true := by decide +kernel

private theorem correlations (t : Fin 271) : dotPrefix t.val 271 = if t.val=0 then 271 else 0 := by
  by_cases h0 : t.val<16
  · exact test_true test_0 (by omega) (by omega)
  by_cases h1 : t.val<32
  · exact test_true test_1 (by omega) (by omega)
  by_cases h2 : t.val<48
  · exact test_true test_2 (by omega) (by omega)
  by_cases h3 : t.val<64
  · exact test_true test_3 (by omega) (by omega)
  by_cases h4 : t.val<80
  · exact test_true test_4 (by omega) (by omega)
  by_cases h5 : t.val<96
  · exact test_true test_5 (by omega) (by omega)
  by_cases h6 : t.val<112
  · exact test_true test_6 (by omega) (by omega)
  by_cases h7 : t.val<128
  · exact test_true test_7 (by omega) (by omega)
  by_cases h8 : t.val<144
  · exact test_true test_8 (by omega) (by omega)
  by_cases h9 : t.val<160
  · exact test_true test_9 (by omega) (by omega)
  by_cases h10 : t.val<176
  · exact test_true test_10 (by omega) (by omega)
  by_cases h11 : t.val<192
  · exact test_true test_11 (by omega) (by omega)
  by_cases h12 : t.val<208
  · exact test_true test_12 (by omega) (by omega)
  by_cases h13 : t.val<224
  · exact test_true test_13 (by omega) (by omega)
  by_cases h14 : t.val<240
  · exact test_true test_14 (by omega) (by omega)
  by_cases h15 : t.val<256
  · exact test_true test_15 (by omega) (by omega)
  exact test_true test_16 (by omega) (by omega)

/-- Four disjoint ternary circulants, covering every position and having
total periodic autocorrelation zero at every nonzero shift. -/
def system271 : System 271 where
  entry c j := component c (code j.val)
  ternary c j := components_ternary _ _
  partition j := components_partition _
  correlation t := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ j : Fin 271, letterDot (code j.val) (code ((j.val+t.val)%271)) := by
        apply Finset.sum_congr rfl
        intro j _
        exact (components_agree _ _).symm
      _ = dotPrefix t.val 271 := by
        rw [dotPrefix_eq]
        exact Fin.sum_univ_eq_sum_range (fun j => letterDot (code j) (code ((j+t.val)%271))) 271
      _ = _ := correlations t

theorem exists_periodic_T_271 : Nonempty (System 271) := ⟨system271⟩

#print axioms exists_periodic_T_271
end Hadamard.PeriodicT

