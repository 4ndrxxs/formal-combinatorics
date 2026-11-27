module
public import Quantum.Pandiagonal

/-! Embedded orthogonal families on the toroidal board, including additional
orthonormal bases at orders eight and nine. -/
@[expose] public section
noncomputable section
namespace QuantumCertificate.Pandiagonal
open scoped BigOperators

def Attack {n : ℕ} (p q : ZMod n × ZMod n) : Prop :=
  p.1=q.1 ∨ p.2=q.2 ∨ p.2-p.1=q.2-q.1 ∨ p.2+p.1=q.2+q.1
instance {n : ℕ} (p q : ZMod n × ZMod n) : Decidable (Attack p q) := by
  unfold Attack
  infer_instance

private theorem line_zero {n : ℕ} [NeZero n] {v : ZMod n → Space n}
    (hb : ∃ b : OrthonormalBasis (ZMod n) ℂ (Space n), ⇑b=v)
    {i j : ZMod n} (h : i≠j) : inner ℂ (v i) (v j)=0 := by
  obtain ⟨b,hb⟩ := hb
  simpa only [hb,ite_eq_right_iff.mpr (fun e => (h e).elim)] using b.inner_eq_ite i j

theorem Array.orth_of_attack {n : ℕ} [NeZero n] (g : Array n) {p q : ZMod n × ZMod n}
    (ne : p≠q) (atq : Attack p q) :
    inner ℂ (g.entry p.1 p.2) (g.entry q.1 q.2)=0 := by
  obtain ⟨r,c⟩ := p
  obtain ⟨s,d⟩ := q
  change r=s ∨ c=d ∨ c-r=d-s ∨ c+r=d+s at atq
  change inner ℂ (g.entry r c) (g.entry s d)=0
  rcases atq with eq|eq|eq|eq
  · subst s
    exact line_zero (g.row r) (fun e => ne (Prod.ext rfl e))
  · subst d
    exact line_zero (g.col c) (fun e => ne (Prod.ext e rfl))
  · have hrs : r≠s := by
      rintro rfl
      exact ne (Prod.ext rfl (sub_left_inj.mp eq))
    have e := line_zero (g.up (c-r)) hrs
    change inner ℂ (g.entry r (c-r+r)) (g.entry s (c-r+s))=0 at e
    rwa [sub_add_cancel,eq,sub_add_cancel] at e
  · have hrs : r≠s := by
      rintro rfl
      exact ne (Prod.ext rfl (add_right_cancel eq))
    have e := line_zero (g.down (c+r)) hrs
    change inner ℂ (g.entry r (c+r-r)) (g.entry s (c+r-s))=0 at e
    rwa [add_sub_cancel_right,eq,add_sub_cancel_right] at e

theorem Array.clique {n : ℕ} [NeZero n] (g : Array n) {ι : Type} (p : ι → ZMod n × ZMod n)
    (inj : Function.Injective p) (atk : ∀ i j, Attack (p i) (p j)) :
    Orthonormal ℂ (fun i => g.entry (p i).1 (p i).2) :=
  ⟨fun _ => g.unit _ _,fun i j e => g.orth_of_attack (fun h => e (inj h)) (atk i j)⟩

theorem Array.clique_bound {n : ℕ} [NeZero n] (g : Array n) {ι : Type} [Fintype ι]
    (p : ι → ZMod n × ZMod n) (inj : Function.Injective p) (atk : ∀ i j, Attack (p i) (p j)) :
    Fintype.card ι≤n := by
  simpa using (g.clique p inj atk).linearIndependent.fintype_card_le_finrank

private theorem add_attack {n : ℕ} (v p q : ZMod n × ZMod n)
    (h : Attack p q) : Attack (v+p) (v+q) := by
  rcases h with h|h|h|h
  · exact Or.inl (congrArg (v.1+·) h)
  · exact Or.inr (Or.inl (congrArg (v.2+·) h))
  · apply Or.inr <| Or.inr <| Or.inl ?_
    change v.2+p.2-(v.1+p.1)=v.2+q.2-(v.1+q.1)
    rwa [add_sub_add_comm,add_sub_add_comm,add_right_inj]
  · apply Or.inr <| Or.inr <| Or.inr ?_
    change v.2+p.2+(v.1+p.1)=v.2+q.2+(v.1+q.1)
    calc
      _ = (v.2+v.1)+(p.2+p.1) := by abel
      _ = (v.2+v.1)+(q.2+q.1) := by rw [h]
      _ = _ := by abel

theorem Array.clique_basis {n : ℕ} [NeZero n] (g : Array n) {ι : Type} [Fintype ι] [Nonempty ι]
    (p : ι → ZMod n × ZMod n) (inj : Function.Injective p) (atk : ∀ i j, Attack (p i) (p j))
    (size : Fintype.card ι=n) (v : ZMod n × ZMod n) :
    ∃ b : OrthonormalBasis ι ℂ (Space n), ⇑b=(fun i => g.entry (v.1+(p i).1) (v.2+(p i).2)) := by
  have h := g.clique (fun i => v+p i) (fun _ _ e => inj (add_left_cancel e))
    (fun i j => add_attack v _ _ (atk i j))
  exact ⟨OrthonormalBasis.mk h
    (h.linearIndependent.span_eq_top_of_card_eq_finrank (by simpa using size)).ge,
    OrthonormalBasis.coe_mk _ _⟩

theorem no_order_two : IsEmpty (Array 2) := by
  refine ⟨fun g => ?_⟩
  have b := g.clique_bound (id (α := ZMod 2 × ZMod 2)) Function.injective_id (by decide +kernel)
  norm_num [Fintype.card_prod,ZMod.card] at b

/-- Eight cells already form a clique on the sixteen-cell board. -/
def fourClique (i : Fin 4 × Fin 2) : ZMod 4 × ZMod 4 :=
  (i.1.val,i.1.val+2*(i.2.val:ZMod 4))

theorem no_order_four : IsEmpty (Array 4) := by
  refine ⟨fun g => ?_⟩
  have b := g.clique_bound fourClique (by decide +kernel) (by decide +kernel)
  norm_num [Fintype.card_prod] at b

def eightClique (i : Fin 4 × Fin 2) : ZMod 8 × ZMod 8 :=
  (2*(i.1.val:ZMod 8),2*(i.1.val:ZMod 8)+4*(i.2.val:ZMod 8))

theorem Array.eight_extra_bases (g : Array 8) (v : ZMod 8 × ZMod 8) :
    ∃ b : OrthonormalBasis (Fin 4 × Fin 2) ℂ (Space 8),
      ⇑b=(fun i => g.entry (v.1+(eightClique i).1) (v.2+(eightClique i).2)) :=
  g.clique_basis eightClique (by decide +kernel) (by decide +kernel) (by decide) v

def nineClique (i : Fin 3 × Fin 3) : ZMod 9 × ZMod 9 :=
  (3*(i.1.val:ZMod 9),3*(i.2.val:ZMod 9))

theorem Array.nine_extra_bases (g : Array 9) (v : ZMod 9 × ZMod 9) :
    ∃ b : OrthonormalBasis (Fin 3 × Fin 3) ℂ (Space 9),
      ⇑b=(fun i => g.entry (v.1+(nineClique i).1) (v.2+(nineClique i).2)) :=
  g.clique_basis nineClique (by decide +kernel) (by decide +kernel) (by decide) v

#print axioms no_order_four
#print axioms Array.nine_extra_bases
end QuantumCertificate.Pandiagonal
