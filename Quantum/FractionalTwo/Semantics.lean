module
public import Quantum.FractionalTwo.Boards
public import Quantum.UniqueSudokuRup

/-! Each initial clause follows from a unit sum of nonnegative weights, the
normalized clue at the origin, or a mismatch with a valid classical square. -/
@[expose] public section
noncomputable section
namespace FractionalTwo
open Finset FractionalBinary UniqueSudoku.Rup
open scoped BigOperators
abbrev A := Fin 64
abbrev S := Fin 4 × Fin 4
def atom (s : S) (d : Fin 4) : A := Fin.ofNat 64 (16*s.1.val+4*s.2.val+d.val)
def loc (a : A) : S := (Fin.ofNat 4 (a.val/16),Fin.ofNat 4 (a.val/4))
def digit (a : A) : Fin 4 := Fin.ofNat 4 a.val
def house (u : Fin 64) (i : Fin 4) : A :=
  if u.val<16 then atom (Fin.ofNat 4 (u.val/4),Fin.ofNat 4 u.val) i else
  atom (line (Fin.ofNat 12 ((u.val-16)/4)) i) (Fin.ofNat 4 u.val)

structure Fractional (t : A→ℝ) : Prop where
  nonneg : ∀ a,0≤t a
  total : ∀ u,∑ i,t (house u i)=1

def Agrees (t : A→ℝ) (f : S→Fin 4) := ∀ a,t a=1 → f (loc a)=digit a
def possible (i : A) : ℕ := 2*i.val
def forced (i : A) : ℕ := 2*(64+i.val)
def truth (t : A→ℝ) (l : ℕ) : Prop :=
  let a:=Fin.ofNat 64 (l/2)
  let p := if l/2<64 then 0<t a else t a=1
  if l%2=0 then p else ¬p

theorem opposite (t : A→ℝ) (l : ℕ) : truth t l → ¬truth t (flip l) := by
  by_cases e : l%2=0
  · have ne : (l+1)%2≠0 := by omega
    have div : (l+1)/2=l/2 := by omega
    simp [truth,UniqueSudoku.Rup.flip,e,ne,div]
  · have yes : (l-1)%2=0 := by omega
    have div : (l-1)/2=l/2 := by omega
    simp [truth,UniqueSudoku.Rup.flip,e,yes,div]

@[simp] theorem truth_possible (t : A→ℝ) (a : A) : truth t (possible a) ↔ 0<t a := by
  have half : 2*a.val/2=a.val := by omega
  simp [truth,possible,half,a.isLt]

@[simp] theorem truth_forced (t : A→ℝ) (a : A) : truth t (forced a) ↔ t a=1 := by
  have half : 2*(64+a.val)/2=64+a.val := by omega
  have c : Fin.ofNat 64 (64+a.val)=a := by apply Fin.ext;change (64+a.val)%64=a.val;omega
  rw [truth,forced,ite_eq_left (by omega),half,ite_eq_right (by omega),c]

@[simp] theorem truth_negative (t : A→ℝ) (v : ℕ) : truth t (flip v) ↔ ¬truth t v := by
  by_cases e : v%2=0
  · have ne : (v+1)%2≠0 := by omega
    have div : (v+1)/2=v/2 := by omega
    simp [truth,UniqueSudoku.Rup.flip,e,ne,div]
  · have yes : (v-1)%2=0 := by omega
    have div : (v-1)/2=v/2 := by omega
    simp [truth,UniqueSudoku.Rup.flip,e,yes,div]

def mask : List ℕ → ℕ
  | [] => 0
  | a::s => bit a ||| mask s

@[simp] theorem mask_mem (s : List ℕ) (a : ℕ) : (mask s).testBit a=true ↔ a∈s := by
  induction s with
  | nil => simp [mask]
  | cons b s ih =>
    simp only [mask,Nat.testBit_or,Bool.or_eq_true,bit_test,decide_eq_true_eq,ih,List.mem_cons]
    rw [eq_comm (a:=b) (b:=a)]

theorem holds_mask (t : A→ℝ) (s : List ℕ) : Holds (truth t) (mask s) ↔ ∃v∈s,truth t v := by simp [Holds]

def source (kind : ℕ) (u : Fin 64) (j : Fin 288) (a b : Fin 4) : List ℕ :=
  match kind with
  | 0 => (List.finRange 4).map (fun i => possible (house u i))
  | 1 => forced (house u a)::((List.finRange 4).filter (·≠a)).map (fun i => possible (house u i))
  | 2 => if a=b then [forced (house u a),flip (forced (house u a))] else
    [flip (forced (house u a)),flip (possible (house u b))]
  | 3 => ((List.finRange 64).filter (fun v => candidate j (loc v)≠digit v)).map forced
  | _ => [forced 0]

def sourceMask (c : ℕ) : ℕ := mask (source (c/4608) (Fin.ofNat 64 (c/16%288)) (Fin.ofNat 288 (c/16))
    (Fin.ofNat 4 (c/4)) (Fin.ofNat 4 c))

theorem source_holds {t : A→ℝ} (ht : Fractional t) (h0 : t 0=1) (hd : ¬∃ j,Agrees t (candidate j))
    (c : ℕ) : Holds (truth t) (sourceMask c) := by
  unfold sourceMask
  apply (holds_mask _ _).mpr
  generalize c/4608=k
  generalize Fin.ofNat 64 (c/16%288)=u
  generalize Fin.ofNat 288 (c/16)=j
  generalize Fin.ofNat 4 (c/4)=a
  generalize Fin.ofNat 4 c=b
  have anyPos : ∃ i,0<t (house u i) := by
    by_contra no
    push Not at no
    have z (i) : t (house u i)=0 := le_antisymm (no i) (ht.nonneg _)
    simpa [z] using ht.total u
  have forced_at (ne : ∀ i,i≠a → t (house u i)=0) : t (house u a)=1 := by
    have h (i) : t (house u i) = if i=a then t (house u a) else 0 := by
      by_cases e : i=a <;> simp [e,ne i]
    calc
      _=(∑ i : Fin 4,if i=a then t (house u a) else 0) := by simp
      _=(∑ i,t (house u i)) := sum_congr rfl (fun i _ => (h i).symm)
      _=1 := ht.total u
  cases k with
  | zero =>
    obtain ⟨i,hi⟩ := anyPos
    exact ⟨_,List.mem_map.mpr ⟨i,by simp,rfl⟩,(truth_possible _ _).mpr hi⟩
  | succ k => cases k with
    | zero =>
      by_cases hh : ∃ i,i≠a ∧ 0<t (house u i)
      · obtain ⟨i,ha,hi⟩ := hh
        refine ⟨possible (house u i),List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,by simp [ha],rfl⟩),?_⟩
        exact (truth_possible _ _).mpr hi
      · push Not at hh
        exact ⟨_,List.mem_cons_self,(truth_forced _ _).mpr (forced_at (fun i hi => le_antisymm (hh i hi) (ht.nonneg _)))⟩
    | succ k => cases k with
      | zero =>
        by_cases same : a=b
        · by_cases yes : truth t (forced (house u a))
          · exact ⟨_,by simp [source,same],yes⟩
          · exact ⟨_,by simp [source,same],(truth_negative _ _).mpr yes⟩
        · by_cases yes : t (house u a)=1
          · have le : t (house u a)+t (house u b)≤1 := by
              calc
                _=(∑ i∈{a,b},t (house u i)) := by simp [same]
                _≤(∑ i,t (house u i)) := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => ht.nonneg _)
                _=1 := ht.total u
            exact ⟨flip (possible (house u b)),by simp [source,same],by simp;linarith⟩
          · exact ⟨flip (forced (house u a)),by simp [source,same],by simp [yes]⟩
      | succ k => cases k with
        | zero =>
          have no : ¬Agrees t (candidate j) := fun yes => hd ⟨j,yes⟩
          unfold Agrees at no
          push Not at no
          obtain ⟨v,hv,hn⟩ := no
          exact ⟨_,List.mem_map.mpr ⟨v,by simp [hn],rfl⟩,(truth_forced _ _).mpr hv⟩
        | succ k => exact ⟨forced 0,by simp [source],(truth_forced _ _).mpr h0⟩

end FractionalTwo
