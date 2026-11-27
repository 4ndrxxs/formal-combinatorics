module
public import Quantum.SudokuTradeCertificate

/-! A proof-producing coloring test. Each physical vertex has three line labels,
a reference color, and a flag indicating whether that color is prescribed. -/
@[expose] public section
namespace Activated
open UniqueSudoku.Rup
variable {v d : ℕ} [NeZero v] [NeZero d]

structure Pattern (v d : ℕ) where
  color : Fin v → Fin d
  pin : Fin v → Bool
  line : Fin v → Fin 3 → ℕ
  group : Fin v → Fin d → Fin v

def Near (P : Pattern v d) (i j : Fin v) : Prop := i≠j ∧ ∃ k,P.line i k=P.line j k

instance (P : Pattern v d) (i j : Fin v) : Decidable (Near P i j) :=
  inferInstanceAs (Decidable (i≠j ∧ ∃ k : Fin 3,P.line i k=P.line j k))

structure Good (P : Pattern v d) (g : Fin v→Fin d) : Prop where
  fixed : ∀ i, P.pin i=true → g i=P.color i
  proper : ∀ i j, Near P i j → g i≠g j
  cover : ∀ u, Function.Surjective (fun k => g (P.group u k))

namespace SAT
def literal (i : Fin v) (c : Fin d) : ℕ := 2*(c.val+d*i.val)

def atom (g : Fin v→Fin d) (k : ℕ) : Prop := g (Fin.ofNat v (k/d))=Fin.ofNat d k
def truth (g : Fin v→Fin d) (l : ℕ) : Prop := if l%2=0 then atom g (l/2) else ¬atom g (l/2)

theorem truth_flip (g : Fin v→Fin d) (l : ℕ) : truth g (flip l) ↔ ¬truth g l := by
  classical
  by_cases h : l%2=0
  · have hn : (l+1)%2≠0 := by omega
    have hd : (l+1)/2=l/2 := by omega
    simp [truth,UniqueSudoku.Rup.flip,h,hn,hd]
  · have hn : (l-1)%2=0 := by omega
    have hd : (l-1)/2=l/2 := by omega
    simp [truth,UniqueSudoku.Rup.flip,h,hn,hd]

@[simp] theorem truth_lit (g : Fin v→Fin d) (i : Fin v) (k : Fin d) : truth g (literal i k) ↔ g i=k := by
  have even : (2*(k.val+d*i.val))%2=0 := by simp
  have div : (2*(k.val+d*i.val))/2=k.val+d*i.val := by omega
  have index : Fin.ofNat v ((k.val+d*i.val)/d)=i := by
    apply Fin.ext
    change _%v=i.val
    rw [Nat.add_mul_div_left _ _ (NeZero.pos d),Nat.div_eq_of_lt k.isLt,zero_add,Nat.mod_eq_of_lt i.isLt]
  have col : Fin.ofNat d (k.val+d*i.val)=k := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt k.isLt]
  simp only [truth,literal,even,if_true,div,atom,index,col]

def mask : List ℕ→ℕ
  | [] => 0
  | x::xs => bit x ||| mask xs

@[simp] theorem mask_mem (ls : List ℕ) (k : ℕ) : (mask ls).testBit k=true ↔ k∈ls := by
  induction ls with
  | nil => simp [mask]
  | cons u us ih =>
    simp only [mask,Nat.testBit_or,Bool.or_eq_true,bit_test,decide_eq_true_eq,ih,List.mem_cons]
    rw [eq_comm (a:=u) (b:=k)]

theorem holds_mask (g : Fin v→Fin d) (ls : List ℕ) : Holds (truth g) (mask ls) ↔ ∃ k∈ls,truth g k := by
  simp [Holds]

def taut (i : Fin v) (a : Fin d) : ℕ := mask [literal i a,flip (literal i a)]
theorem taut_holds (g : Fin v→Fin d) (i : Fin v) (a : Fin d) : Holds (truth g) (taut i a) := by
  rw [taut,holds_mask]
  by_cases h : truth g (literal i a)
  · exact ⟨_,by simp,h⟩
  · exact ⟨_,by simp,(truth_flip _ _).mpr h⟩

def clause (P : Pattern v d) (tag : ℕ) : ℕ :=
  let u := Fin.ofNat v (tag/8)
  let w := Fin.ofNat v (tag/8/v)
  let a := Fin.ofNat d (tag/8/v/v)
  let b := Fin.ofNat d (tag/8/v/v/d)
  match tag%8 with
  | 0 => mask (List.ofFn (literal u : Fin d→ℕ))
  | 1 => if a=b then taut u a else mask [flip (literal u a),flip (literal u b)]
  | 2 => if Near P u w then mask [flip (literal u a),flip (literal w a)] else taut u a
  | 3 => if P.pin u then mask [literal u (P.color u)] else taut u a
  | 4 => mask (List.ofFn fun i : Fin d => literal (P.group u i) a)
  | _ => mask (List.ofFn fun i : Fin v => flip (literal i (P.color i)))

theorem clause_sound {P : Pattern v d} {g : Fin v→Fin d} (good : Good P g) (diff : g≠P.color) (tag : ℕ) :
    Holds (truth g) (clause P tag) := by
  classical
  unfold clause
  set u := Fin.ofNat v (tag/8)
  set w := Fin.ofNat v (tag/8/v)
  set a := Fin.ofNat d (tag/8/v/v)
  set b := Fin.ofNat d (tag/8/v/v/d)
  split
  · rw [holds_mask]
    exact ⟨_,List.mem_ofFn.mpr ⟨g u,rfl⟩,by simp⟩
  · change Holds _ (if a=b then _ else _)
    split
    · exact taut_holds _ _ _
    · rename_i ne
      rw [holds_mask]
      by_cases ea : g u=a
      · exact ⟨UniqueSudoku.Rup.flip (literal u b),by simp,(truth_flip _ (literal u b)).mpr (by simpa using (show g u≠b from fun eb => ne (ea.symm.trans eb)))⟩
      · exact ⟨UniqueSudoku.Rup.flip (literal u a),by simp,(truth_flip _ (literal u a)).mpr (by simpa using ea)⟩
  · change Holds _ (if Near P u w then _ else _)
    split
    · rename_i near
      rw [holds_mask]
      by_cases ea : g u=a
      · exact ⟨UniqueSudoku.Rup.flip (literal w a),by simp,(truth_flip _ (literal w a)).mpr (by simpa using (show g w≠a from fun eb => good.proper _ _ near (ea.trans eb.symm)))⟩
      · exact ⟨UniqueSudoku.Rup.flip (literal u a),by simp,(truth_flip _ (literal u a)).mpr (by simpa using ea)⟩
    · exact taut_holds _ _ _
  · change Holds _ (if P.pin u then _ else _)
    split
    · rename_i pin
      rw [holds_mask]
      exact ⟨_,by simp,(truth_lit _ _ _).mpr (good.fixed _ pin)⟩
    · exact taut_holds _ _ _
  · rw [holds_mask]
    obtain ⟨i,hi⟩:=good.cover u a
    exact ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,(truth_lit _ _ _).mpr hi⟩
  · rw [holds_mask]
    obtain ⟨i,ne⟩ : ∃ i, g i≠P.color i := by
      by_contra! same
      exact diff (funext same)
    exact ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,(truth_flip _ _).mpr (by simpa using ne)⟩

def db (P : Pattern v d) (count : ℕ) (tag learned : ℕ→ℕ) (j : ℕ) : ℕ :=
  if j<count then clause P (tag j) else learned (j-count)

def check (P : Pattern v d) (c : ℕ) (tag learned : ℕ→ℕ) (steps : ℕ→List (ℕ×ℕ)) (i : ℕ) : Bool :=
  let D := db P c tag learned
  run D (c+i) (D (c+i)) (steps i)

theorem force (P : Pattern v d) (c n : ℕ) (tag learned : ℕ→ℕ) (steps : ℕ→List (ℕ×ℕ))
    (hn : 0<n) (checks : ∀ i, i<n → check P c tag learned steps i=true)
    (empty : db P c tag learned (c+n-1)=0) (g : Fin v→Fin d) (good : Good P g) : g=P.color := by
  classical
  by_contra diff
  let D:=db P c tag learned
  have valid (j : ℕ) (hj : j<c+n) : Holds (truth g) (D j) := by
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      by_cases first : j<c
      · simpa [D,db,first] using clause_sound good diff (tag j)
      · let i:=j-c
        have small : i<n := by dsimp [i];omega
        have eq : c+i=j := by dsimp [i];omega
        apply derive _ (fun l hl h' => (truth_flip g l).mp h' hl) D j (fun k hk => ih k hk (by omega)) (steps i)
        simpa only [check,eq,D] using checks i small
  have bad := valid (c+n-1) (by omega)
  change Holds (truth g) (db P c tag learned (c+n-1)) at bad
  rw [empty] at bad
  exact empty_false _ bad

end SAT

def CheckInterval (f : ℕ→Bool) (a b : ℕ) : Prop := ∀ (i : ℕ), (a ≤ i) → (i < b) → f i = true

theorem intervalFin (f : ℕ→Bool) (a b : ℕ) (h : ∀ j : Fin (b-a), f (a+j.val)=true) :
    CheckInterval f a b := by
  intro i ha hb
  have eq:=h ⟨i-a,by omega⟩
  change f (a+(i-a))=true at eq
  rwa [show a+(i-a)=i by omega] at eq

theorem intervalJoin {f : ℕ→Bool} {a m b : ℕ} (l : CheckInterval f a m) (r : CheckInterval f m b) :
    CheckInterval f a b := fun i ha hb => by
  by_cases c : i<m
  · exact l i ha c
  · exact r i (by omega) hb

end Activated
