import RationalEdgeWalk

/-! A topological obstruction to perfect edge-state transfer. After removing
the source and target edges, neither edge's endpoints can remain connected.
This also covers bipartite incidence structures with parallel edges. -/
noncomputable section
namespace BipartiteEdgeWalk.Cuts
open Finset Function Decision SimpleGraph
open scoped BigOperators
variable {E L R : Type*} [Fintype E] [DecidableEq E] [Fintype L] [DecidableEq L]
variable [Fintype R] [DecidableEq R]

def residual (l : E→L) (r : E→R) (a b : E) : SimpleGraph (L⊕R) :=
  incidenceGraph (fun e : {e : E // e≠a ∧ e≠b} => l e.val) (fun e => r e.val)

private def balance (l : E→L) (r : E→R) (f : E→ℂ) : L⊕R→ℂ :=
  Sum.elim (mass l f) (fun j => -mass r f j)

private def unit (x y : L⊕R) : ℂ := if x=y then 1 else 0

private theorem bal_delta (l : E→L) (r : E→R) (e : E) (x : L⊕R) :
    balance l r (delta e) x=unit (.inl (l e)) x-unit (.inr (r e)) x := by
  cases x <;> simp [balance,mass_delta,unit]

private theorem bal_add (l : E→L) (r : E→R) (f g : E→ℂ) (x : L⊕R) :
    balance l r (f+g) x=balance l r f x+balance l r g x := by
  cases x <;> simp [balance,mass,Finset.sum_add_distrib] <;> ring

private theorem bal_neg (l : E→L) (r : E→R) (f : E→ℂ) (x : L⊕R) :
    balance l r (-f) x= -balance l r f x := by cases x <;> simp [balance,mass]

private theorem adjacent_flow {l : E→L} {r : E→R} {a b : E} {u v : L⊕R}
    (h : (residual l r a b).Adj u v) :
    ∃ f : E→ℂ, f a=0 ∧ f b=0 ∧ ∀ x,balance l r f x=unit u x-unit v x := by
  rcases u with u|u <;> rcases v with v|v
  · exact h.elim
  · obtain ⟨e,hl,hr⟩ := h
    refine ⟨delta e.val,by simp [delta,Ne.symm e.property.1],by simp [delta,Ne.symm e.property.2],?_⟩
    change l e.val=u at hl
    change r e.val=v at hr
    intro x
    rw [bal_delta,hl,hr]
  · obtain ⟨e,hl,hr⟩ := h
    refine ⟨-(delta e.val),by simp [delta,Ne.symm e.property.1],by simp [delta,Ne.symm e.property.2],?_⟩
    change l e.val=v at hl
    change r e.val=u at hr
    intro x
    rw [bal_neg,bal_delta,hl,hr]
    ring
  · exact h.elim

private theorem walk_flow {l : E→L} {r : E→R} {a b : E} {u v : L⊕R}
    (w : (residual l r a b).Walk u v) :
    ∃ f : E→ℂ, f a=0 ∧ f b=0 ∧ ∀ x,balance l r f x=unit u x-unit v x := by
  induction w with
  | nil =>
    exact ⟨0,rfl,rfl,fun x => by cases x <;> simp [balance,mass]⟩
  | cons h _ ih =>
    obtain ⟨f,fa,fb,hf⟩:=adjacent_flow h
    obtain ⟨g,ga,gb,hg⟩:=ih
    exact ⟨f+g,by simp [fa,ga],by simp [fb,gb],fun x => by rw [bal_add,hf,hg];ring⟩

private theorem endpoint_cut {l : E→L} {r : E→R} {a b : E} (ne : a≠b)
    (invariant : ∀ f : E→ℂ, (∀ u,mass l f u=0) → (∀ v,mass r f v=0) → f a=f b) :
    ¬(residual l r a b).Reachable (.inl (l a)) (.inr (r a)) := by
  intro path
  obtain ⟨f,fa,fb,hf⟩:=walk_flow path.some
  let g : E→ℂ := delta a+(-f)
  have zero (x : L⊕R) : balance l r g x=0 := by
    rw [show g=delta a+(-f) from rfl,bal_add,bal_neg,bal_delta,hf]
    ring
  have eq := invariant g (fun u => zero (.inl u)) (fun v => by
    have hz := zero (.inr v)
    simpa [balance] using hz)
  simpa [g,delta,fa,fb,ne.symm] using eq

/-- A perfect transfer from a to b forces both endpoint pairs to disconnect when
the two edges are deleted. There is no restriction on the integer time. -/
theorem separating_pair (l : E→L) (r : E→R) (hl : Surjective l) (hr : Surjective r)
    {a b : E} (ne : a≠b) {k : ℕ} (hit : PerfectAt l r a b k) :
    (¬(residual l r a b).Reachable (.inl (l a)) (.inr (r a))) ∧
    (¬(residual l r b a).Reachable (.inl (l b)) (.inr (r b))) := by
  obtain ⟨z,_,eq⟩:=hit
  have h (f : E→ℂ) (hL : ∀ u,mass l f u=0) (hR : ∀ v,mass r f v=0) :=
    circulation_equal hl hr f hL hR eq
  exact ⟨endpoint_cut ne h,endpoint_cut ne.symm (fun f u v => (h f u v).symm)⟩

/-- No perfect transfer between distinct edges of a graph that remains
connected after any two edges are removed. -/
theorem no_transfer_if_three_edge_connected (l : E→L) (r : E→R) (hl : Surjective l) (hr : Surjective r)
    (robust : ∀ a b : E, a≠b → (residual l r a b).Connected) {a b : E} (ne : a≠b) (k : ℕ) :
    ¬PerfectAt l r a b k := fun hit => (separating_pair l r hl hr ne hit).1 ((robust a b ne) _ _)

#print axioms separating_pair
#print axioms no_transfer_if_three_edge_connected
end BipartiteEdgeWalk.Cuts
