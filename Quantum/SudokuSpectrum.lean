module

public import Quantum.SudokuLayers
public import Quantum.Spectrum
public import Quantum.SudokuSmallLayers

/-! The punctured interval of projective cardinalities for quantum Sudoku. -/
@[expose] public section
noncomputable section
namespace QuantumSudoku
open QuantumCertificate Collections Finset
open scoped BigOperators

def Allowed (l u c : ℕ) : Prop := l≤c ∧ c≤u ∧ c≠l+1

private theorem split_interval {a b l u c : ℕ} (ha : a+3≤b) (hl : l+3≤u)
    (h : Allowed (a+l) (b+u) c) : ∃ x y, Allowed a b x ∧ Allowed l u y ∧ x+y=c := by
  unfold Allowed at *
  by_cases e : c≤a+u
  · exact ⟨a,c-a,by omega⟩
  by_cases e' : c=a+u+1
  · exact ⟨a+2,u-1,by omega⟩
  exact ⟨c-u,u,by omega⟩

theorem sum_interval (k l u : ℕ) (hk : 1≤k) (hw : l+3≤u) (c : ℕ)
    (h : Allowed (k*l) (k*u) c) :
    ∃ w : Fin k → ℕ, (∀ i, Allowed l u (w i)) ∧ ∑ i, w i = c := by
  induction k, hk using Nat.le_induction generalizing c with
  | base =>
    exact ⟨fun _ => c,fun _ => by simpa using h,by simp⟩
  | succ k hk ih =>
    rw [Nat.succ_mul,Nat.succ_mul] at h
    have width : k*l+3≤k*u := calc
      k*l+3 ≤ k*l+k*3 := by omega
      _ = k*(l+3) := by ring
      _ ≤ k*u := Nat.mul_le_mul_left k hw
    obtain ⟨x,y,hx,hy,hxy⟩ := split_interval width hw h
    obtain ⟨w,hw',hs⟩ := ih x hx
    refine ⟨Fin.cons y w,Fin.cases hy hw',?_⟩
    rw [Fin.sum_univ_succ]
    simpa [hs,add_comm] using hxy

theorem from_layer_range (n c : ℕ) (hn : 2≤n)
    (unions : ∀ t, Allowed n (n*(n*n)) t → Attain n n t)
    (hc : Allowed (n^2) (n^4) c) : Realizes n c := by
  let : NeZero n := ⟨by omega⟩
  have wide : n+3≤n*(n*n) := by nlinarith [Nat.mul_self_le_mul_self hn]
  have hh : Allowed (n*n) (n*(n*(n*n))) c := by convert hc using 1 <;> ring
  obtain ⟨w,hw,hs⟩ := sum_interval n n (n*(n*n)) (by omega) wide c hh
  choose F hF using fun y => unions (w y) (hw y)
  have h := Layers.gives_sum F
  simpa only [hF,hs] using h

theorem large_spectrum (n c : ℕ) (hn : 6≤n) :
    Realizes n c ↔ n^2≤c ∧ c≤n^4 ∧ c≠n^2+1 := by
  let : NeZero n := ⟨by omega⟩
  constructor
  · intro h
    have b := (to_latin h).bounds
    rw [show (n*n)^2=n^4 by ring,show n*n=n^2 by ring] at b
    exact b
  · apply from_layer_range n c (by omega)
    intro t ht
    have base : Good n := fun m lo hi hole =>
      (QuantumCertificate.spectrum n m hn).mpr ⟨lo,by simpa [pow_two] using hi,hole⟩
    exact large_union (by omega) base n (by omega) t ht.1 ht.2.1 ht.2.2

/-- The complete spectrum for every block side at least four, with actual
    complex orthonormal bases in every row, column and block. -/
theorem spectrum (n c : ℕ) (hn : 4≤n) :
    Realizes n c ↔ n^2≤c ∧ c≤n^4 ∧ c≠n^2+1 := by
  by_cases large : 6≤n
  · exact large_spectrum n c large
  let : NeZero n := ⟨by omega⟩
  constructor
  · intro h
    have b := (to_latin h).bounds
    rw [show (n*n)^2=n^4 by ring,show n*n=n^2 by ring] at b
    exact b
  · apply from_layer_range n c (by omega)
    intro t ht
    rcases (by omega : n=4 ∨ n=5) with rfl|rfl
    · exact SmallLayers.four t ht.1 ht.2.1 ht.2.2
    · exact SmallLayers.five t ht.1 ht.2.1 ht.2.2

#print axioms spectrum
end QuantumSudoku
