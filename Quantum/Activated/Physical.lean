module
public import Quantum.Activated.Constraints
public import Quantum.FractionalPhysicalCut
public import Quantum.SudokuSolutionCardinality

/-! Connecting a finite coloring certificate to an ordinary physical Sudoku.
All unspecified cells must occur among the certified slots. The reference
solution and the quantum solution use the same symbol map. -/
@[expose] public section
noncomputable section
namespace Activated
open Function QuantumSudoku FractionalLayouts PartialSudoku PhysicalSudokuCut SudokuEmbedding QuantumCertificate
variable {n m v d : ℕ} [NeZero n] [NeZero d] [NeZero v]

abbrev Cell (n : ℕ) := Sites n × Sites n

def Peer (s t : Cell n) : Prop :=
  s≠t ∧ (s.1=t.1 ∨ s.2=t.2 ∨ (s.1.1=t.1.1 ∧ s.2.1=t.2.1))

instance (s t : Cell n) : Decidable (Peer s t) :=
  inferInstanceAs (Decidable (s≠t ∧ (s.1=t.1 ∨ s.2=t.2 ∨ (s.1.1=t.1.1 ∧ s.2.1=t.2.1))))

theorem different_peers {p : Puzzle n} {f : Solution n} (hf : ClassicalCompletes p f)
    {s t : Cell n} (near : Peer s t) : f s.1 s.2≠f t.1 t.2 := by
  rcases s with ⟨⟨x,r⟩,⟨y,c⟩⟩
  rcases t with ⟨⟨z,u⟩,⟨w,b⟩⟩
  rcases near with ⟨ne,h|h|h⟩
  · change (x,r)=(z,u) at h
    cases h
    intro eq
    exact ne (Prod.ext rfl ((hf.1 .row (x,r)).injective eq))
  · change (y,c)=(w,b) at h
    cases h
    intro eq
    exact ne (Prod.ext ((hf.1 .column (y,c)).injective eq) rfl)
  · obtain ⟨hx,hy⟩:=h
    change x=z at hx
    change y=w at hy
    subst z; subst w
    intro eq
    have e : (r,c)=(u,b) := (hf.1 .block (x,y)).injective eq
    cases e
    exact ne rfl

def coordCode (u : Word m) : Code m := Sum.elim (fun j => Sum.inl ⟨j.val,by omega⟩) Sum.inr u

private theorem numer_coord : ∀ i j : Fin 4,
    ImpossibleSudoku.numerator ⟨i.val,by omega⟩ j=if j=i then (2,0) else (0,0) := by decide +kernel

theorem coord_vector (L : Full n m) (u : Word m) : L.vector (coordCode u)=unitAxis (L.symbol u) := by
  cases u with
  | inr u => rfl
  | inl i =>
    ext p
    obtain ⟨z,rfl⟩:=L.symbol.surjective p
    cases z with
    | inl j =>
      change (Sum.elim (fun k : Fin 4 => (vector 1 4 (ImpossibleSudoku.numerator ⟨i.val,by omega⟩)) k)
          (fun _ : Fin m => (0:ℂ)) (L.symbol.symm (L.symbol (.inl j))))=_
      rw [Equiv.symm_apply_apply]
      by_cases e : j=i <;> simp [unitAxis,vector,numer_coord,e,L.symbol.injective.eq_iff] <;> norm_num
    | inr j =>
      change (Sum.elim (fun k : Fin 4 => (vector 1 4 (ImpossibleSudoku.numerator ⟨i.val,by omega⟩)) k)
          (fun _ : Fin m => (0:ℂ)) (L.symbol.symm (L.symbol (.inr j))))=_
      simp [unitAxis,L.symbol.injective.eq_iff]

theorem mixed_of_label (L : Full n m) {r c : Sites n} {q : Fin 24} (hq : L.label r c=.inl q)
    {a b : Fin 4} (ne : a≠b) (ha : ImpossibleSudoku.numerator q a≠(0,0))
    (hb : ImpossibleSudoku.numerator q b≠(0,0)) : SudokuLocus.Mixed L.board := by
  have nz (i : Fin 4) (hi : ImpossibleSudoku.numerator q i≠(0,0)) :
      L.board r c (L.symbol (.inl i))≠0 := by
    have emb : embed 1 (ImpossibleSudoku.numerator q i)≠0 := fun eq =>
      hi (embed_injective (by decide : 0<1) (eq.trans (map_zero (embed 1)).symm))
    simp [Full.board,hq,Full.vector,Full.spread,vector,emb]
  exact ⟨r,c,_,_,fun e => ne (Sum.inl.inj (L.symbol.injective e)),nz a ha,nz b hb⟩

structure Chart (n m v d : ℕ) where
  ref : Sites n→Sites n→Word m
  missing : Sites n→Sites n→Bool
  slot : Fin v→Cell n
  find : Sites n→Sites n→Fin v
  ax : Fin d→Word m
  pos : Direction→Sites n→Word m→Sites n

variable (L : Full n m) (P : Pattern v d) (A : Chart n m v d)

def Chart.baseline (r c : Sites n) := L.symbol (A.ref r c)
def Chart.puzzle (r c : Sites n) := if A.missing r c then none else some (A.baseline L r c)

structure Compatible : Prop where
  perm : ∀ dir k s,physicalSlice A.ref dir k (A.pos dir k s)=s
  given : ∀ r c,A.missing r c=false → L.label r c=coordCode (A.ref r c)
  cover : ∀ r c,A.missing r c=true → A.slot (A.find r c)=(r,c)
  label : ∀ i,A.ref (A.slot i).1 (A.slot i).2=A.ax (P.color i)
  pins : ∀ i,P.pin i=true → A.missing (A.slot i).1 (A.slot i).2=false
  adj : ∀ i j,Near P i j → Peer (A.slot i) (A.slot j)
  distinct : Injective A.ax

variable {L P A}
theorem Compatible.classical (h : Compatible L P A) : ClassicalCompletes (A.puzzle L) (A.baseline L) := by
  constructor
  · intro dir k
    apply Finite.surjective_iff_bijective.mp
    intro w
    obtain ⟨s,rfl⟩:=L.symbol.surjective w
    exact ⟨A.pos dir k s,congrArg L.symbol (h.perm dir k s)⟩
  · intro r c j given
    exact (show A.missing r c=false ∧ A.baseline L r c=j by simpa [Chart.puzzle] using given).2

theorem Compatible.quantum (h : Compatible L P A) : QuantumCompletes (A.puzzle L) L.board := by
  refine ⟨L.quantum.1,?_⟩
  intro r c j clue
  by_cases miss : A.missing r c=true
  · simp [Chart.puzzle,miss] at clue
  have off : A.missing r c=false := Bool.eq_false_iff.mpr miss
  have eq : A.baseline L r c=j := by simpa [Chart.puzzle,off] using clue
  refine ⟨1,?_⟩
  rw [←eq]
  simp only [Circle.coe_one,one_smul]
  change L.vector (L.label r c)=_
  rw [h.given r c off,coord_vector]
  rfl

theorem Compatible.unique (h : Compatible L P A)
    (clique : ∀ u i j,i≠j → Near P (P.group u i) (P.group u j))
    (force : ∀ g,Good P g → g=P.color) {f : Solution n} (hf : ClassicalCompletes (A.puzzle L) f) :
    f=A.baseline L := by
  classical
  let digit (i : Fin d) := L.symbol (A.ax i)
  have dinj : Injective digit := L.symbol.injective.comp h.distinct
  have base (i : Fin v) : A.baseline L (A.slot i).1 (A.slot i).2=digit (P.color i) :=
    congrArg L.symbol (h.label i)
  have fixed (r c : Sites n) (hg : A.missing r c=false) : f r c=A.baseline L r c :=
    hf.2 _ _ _ (by simp [Chart.puzzle,hg])
  have used (i : Fin v) : ∃ j,f (A.slot i).1 (A.slot i).2=digit j := by
    let s:=A.slot i
    obtain ⟨c,hc⟩:=(h.classical.1 .row s.1).surjective (f s.1 s.2)
    change A.baseline L s.1 c=f s.1 s.2 at hc
    by_cases miss : A.missing s.1 c=true
    · have eq:=h.cover s.1 c miss
      exact ⟨P.color (A.find s.1 c),hc.symm.trans (by simpa only [eq] using base (A.find s.1 c))⟩
    · have eq : c=s.2 := (hf.1 .row s.1).injective ((fixed _ _ (Bool.eq_false_iff.mpr miss)).trans hc)
      exact ⟨P.color i,hc.symm.trans (eq ▸ base i)⟩
  choose g hg using used
  have proper (i j : Fin v) (near : Near P i j) : g i≠g j := fun eq =>
    different_peers hf (h.adj i j near) ((hg i).trans ((congrArg digit eq).trans (hg j).symm))
  have good : Good P g := ⟨fun i pin => dinj ((hg i).symm.trans ((fixed _ _ (h.pins i pin)).trans (base i))),
    proper,fun u => Finite.injective_iff_surjective.mp (fun i j eq => by
      by_contra ne
      exact proper _ _ (clique u i j ne) eq)⟩
  have solved:=force g good
  funext r c
  by_cases miss : A.missing r c=true
  · obtain hs:=h.cover r c miss
    have vv: f (A.slot (A.find r c)).1 (A.slot (A.find r c)).2=
        A.baseline L (A.slot (A.find r c)).1 (A.slot (A.find r c)).2 :=
      (hg _).trans ((congrArg digit (congrFun solved _)).trans (base _).symm)
    simpa [hs] using vv
  · exact fixed r c (Bool.eq_false_iff.mpr miss)

theorem counterexample (h : Compatible L P A) (clique : ∀ u i j,i≠j → Near P (P.group u i) (P.group u j))
    (force : ∀ g,Good P g → g=P.color) (hm : SudokuLocus.Mixed L.board) : SudokuTrade.UniqueQuantumCounterexample n := by
  have hc:=h.classical
  have hv:=h.quantum
  have unique:=fun f => h.unique clique force (f:=f)
  refine ⟨A.puzzle L,⟨A.baseline L,hc,unique⟩,⟨_,_,SudokuLocus.classical_quantum hc,hv,
    SudokuLocus.mixed_inequivalent hc unique hv hm⟩,?_⟩
  obtain ⟨r,c,a,b,ne,ha,hb⟩:=hm
  exact ⟨SudokuContinuum.circleEmbedding hv ne ha hb⟩

#print axioms counterexample
end Activated
