module
public import Quantum.FractionalBellThreeGrid

/-! A deterministic ternary Sudoku whose distinguished symbol never has a
local value 2 selects one bit per band and one bit per stack. Its four-block
CHSH score is at most two. The supported face argument preserves that bound
under arbitrary scalar convex mixtures. -/
@[expose] public section
noncomputable section
namespace FractionalBellThree
open QuantumSudoku FractionalLayouts FractionalBlockBell FractionalPolygons.Sudoku
  Complex Matrix Finset
open scoped BigOperators ComplexConjugate

private theorem no_ternary_transition :
    ∀ x : F, ∀ g : F → F, (∀ i j, g i=g j → i=j) → (∀ y, g y+x+y≠2) →
      ∀ y, g y+x+y=g 0+x+0 := by decide +kernel

private theorem deterministic_bound {p : P} (hc : Classical p) (hz : supported p) : score p≤2 := by
  obtain ⟨f,hf,hp⟩ := hc
  have sur (xy : Index F) := (Finite.injective_iff_bijective.mp (hf .block xy)).surjective zeroSymbol
  choose pick picked using sur
  have hit (xy rc : Index F) : f (arrange .block (xy,rc))=zeroSymbol ↔ rc=pick xy :=
    ⟨fun e => hf .block xy (e.trans (picked xy).symm),fun e => e ▸ picked xy⟩
  have clean (xy : Index F) :
      aDigit (arrange .block (xy,pick xy))≠2 ∧ bDigit (arrange .block (xy,pick xy))≠2 := by
    have out (e : aDigit (arrange .block (xy,pick xy))=2 ∨ bDigit (arrange .block (xy,pick xy))=2) :
        False := by
      have bad := hz _ e
      norm_num [hp,picked] at bad
    exact ⟨fun a => out (Or.inl a),fun b => out (Or.inr b)⟩
  have rowPick (x : F) : Function.Injective (fun y => (pick (x,y)).1) := by
    intro y z he
    have eq := (picked (x,y)).trans (picked (x,z)).symm
    change f ((x,(pick (x,y)).1),(y,(pick (x,y)).2))=f ((x,(pick (x,z)).1),(z,(pick (x,z)).2)) at eq
    rw [show (pick (x,y)).1=(pick (x,z)).1 from he] at eq
    exact congrArg Prod.fst (hf .row (x,(pick (x,z)).1) eq)
  have colPick (y : F) : Function.Injective (fun x => (pick (x,y)).2) := by
    intro x z he
    have eq := (picked (x,y)).trans (picked (z,y)).symm
    change f ((x,(pick (x,y)).1),(y,(pick (x,y)).2))=f ((z,(pick (z,y)).1),(y,(pick (z,y)).2)) at eq
    rw [show (pick (x,y)).2=(pick (z,y)).2 from he] at eq
    exact congrArg Prod.fst (hf .column (y,(pick (z,y)).2) eq)
  have aa (x y : F) : aDigit (arrange .block ((x,y),pick (x,y)))=
      aDigit (arrange .block ((x,0),pick (x,0))) :=
    no_ternary_transition x (fun y => (pick (x,y)).1)
      (fun _ _ eq => rowPick x eq) (fun y => (clean (x,y)).1) y
  have bb (x y : F) : bDigit (arrange .block ((x,y),pick (x,y)))=
      bDigit (arrange .block ((0,y),pick (0,y))) := by
    have cond (x : F) : (pick (x,y)).2+y+x≠2 := by
      simpa [arrange,bDigit,add_right_comm] using (clean (x,y)).2
    simpa [arrange,bDigit,add_right_comm] using
      no_ternary_transition y (fun x => (pick (x,y)).2) (fun _ _ eq => colPick y eq) cond x
  let A (x : Two) := aDigit (arrange .block ((tag x,0),pick (tag x,0)))
  let B (y : Two) := bDigit (arrange .block ((0,tag y),pick (0,tag y)))
  have eff (z : Index Two) : coeff z (pick (tag z.1,tag z.2))=pay z.1 z.2 (A z.1) (B z.2) := by
    unfold coeff binpos A B
    rw [aa,bb]
  have val : score p=∑ z : Index Two, (pay z.1 z.2 (A z.1) (B z.2):ℝ) := by
    simp only [score,binpos,hp,hit,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',
      Finset.mem_univ,ite_true,eff]
  have chsh : ∀ A B : Two → F, (∑ xy : Index Two, pay xy.1 xy.2 (A xy.1) (B xy.2))≤2 := by
    decide +kernel
  rw [val]
  exact_mod_cast chsh A B

theorem supported_hull {p : P} (hc : p∈convexHull ℝ {p | Classical p}) (hp : supported p) :
    score p≤2 := by
  let G : Set P := {p | (∀ q,0≤p q zeroSymbol) ∧ (supported p → score p≤2)}
  have base : {p : P | Classical p}⊆G := by
    intro p c
    refine ⟨?_,deterministic_bound c⟩
    obtain ⟨_,_,h⟩ := c
    intro q
    rw [h]
    split <;> norm_num
  have cv : Convex ℝ G := by
    intro p hq q jq a b ha hb hs
    by_cases za : a=0
    · have y : b=1 := by linarith
      simpa [za,y] using jq
    by_cases zb : b=0
    · have y : a=1 := by linarith
      simpa [zb,y] using hq
    obtain ⟨pn,ps⟩ := hq
    obtain ⟨qn,qs⟩ := jq
    refine ⟨fun u => add_nonneg (mul_nonneg ha (pn _)) (mul_nonneg hb (qn _)),?_⟩
    intro s
    have both (u : Site F) (bad : aDigit u=2 ∨ bDigit u=2) : p u zeroSymbol=0 ∧ q u zeroSymbol=0 := by
      have z := s u bad
      change a*p u zeroSymbol+b*q u zeroSymbol=0 at z
      obtain ⟨e,f⟩ := (add_eq_zero_iff_of_nonneg (mul_nonneg ha (pn u)) (mul_nonneg hb (qn u))).mp z
      exact ⟨(mul_eq_zero.mp e).resolve_left za,(mul_eq_zero.mp f).resolve_left zb⟩
    rw [score_affine]
    have v := ps (fun u bad => (both u bad).1)
    have w := qs (fun u bad => (both u bad).2)
    calc
      _≤a*2+b*2 := by gcongr
      _=2 := by linarith
  exact ((convexHull_min base cv) hc).2 hp

theorem outside : data∉convexHull ℝ {p | Classical p} := by
  intro h
  have bad := supported_hull h data_supported
  rw [data_score] at bad
  norm_num at bad

#print axioms outside
end FractionalBellThree

