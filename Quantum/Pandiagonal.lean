module
public import Quantum.Diagonal
public import Mathlib.Data.ZMod.Basic

/-! The four line classes of a toroidal quantum Latin square induce uniform
mass on the nine pairs of residues modulo three. -/
@[expose] public section
noncomputable section
namespace QuantumCertificate.Pandiagonal
open scoped BigOperators
open Finset

/-- Both slopes run through all translates, with columns indexed modulo the order. -/
structure Array (n : ℕ) [NeZero n] where
  entry : ZMod n → ZMod n → Space n
  row : ∀ i, ∃ b : OrthonormalBasis (ZMod n) ℂ (Space n), ⇑b=entry i
  col : ∀ j, ∃ b : OrthonormalBasis (ZMod n) ℂ (Space n), ⇑b=fun i => entry i j
  up : ∀ k, ∃ b : OrthonormalBasis (ZMod n) ℂ (Space n), ⇑b=fun i => entry i (k+i)
  down : ∀ k, ∃ b : OrthonormalBasis (ZMod n) ℂ (Space n), ⇑b=fun i => entry i (k-i)

structure Mass {G : Type} [Fintype G] [AddCommGroup G] (f : G → G → ℝ) (z : ℝ) : Prop where
  row : ∀ r, ∑ c, f r c=z
  col : ∀ c, ∑ r, f r c=z
  up : ∀ d, ∑ r, f r (d+r)=z
  down : ∀ d, ∑ r, f r (d-r)=z

def weight {n : ℕ} [NeZero n] (g : Array n) (v : Space n) (i j : ZMod n) : ℝ :=
  ‖inner ℂ v (g.entry i j)‖^2

theorem Array.mass {n : ℕ} [NeZero n] (g : Array n) (v : Space n) :
    Mass (weight g v) (‖v‖^2) := by
  have line {f : ZMod n → Space n} (h : ∃ b : OrthonormalBasis (ZMod n) ℂ (Space n), ⇑b=f) :
      ∑ i, ‖inner ℂ v (f i)‖^2=‖v‖^2 := by
    obtain ⟨b,hb⟩ := h
    simpa only [hb] using b.sum_sq_norm_inner_left v
  exact ⟨fun r => line (g.row r),fun c => line (g.col c),fun k => line (g.up k),
    fun k => line (g.down k)⟩

theorem Array.unit {n : ℕ} [NeZero n] (g : Array n) (r c : ZMod n) : ‖g.entry r c‖=1 := by
  obtain ⟨b,hb⟩ := g.row r
  simpa only [hb] using b.orthonormal.1 c

private theorem incidence (r c a b : ZMod 3) (x : ℝ) :
    (if r=a then x else 0)+(if c=b then x else 0)+
    (if c-r=b-a then x else 0)+(if c+r=b+a then x else 0)=
    x+3*(if r=a ∧ c=b then x else 0) := by
  have facts : ∀ r c a b : ZMod 3,
      (if r=a then 1 else 0)+(if c=b then 1 else 0)+
      (if c-r=b-a then 1 else 0)+(if c+r=b+a then 1 else 0)=
      1+3*(if r=a ∧ c=b then 1 else 0 : ℕ) := by decide +kernel
  have gate (p : Prop) [Decidable p] :
      ((if p then 1 else 0 : ℕ):ℝ)*x=(if p then x else 0) := by split <;> simp
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,add_mul,mul_assoc,
    gate,one_mul] using congrArg (fun m : ℕ => (m:ℝ)*x) (facts r c a b)

def tile {G : Type} [Fintype G] (h : G → ZMod 3) (f : G → G → ℝ) (a b : ZMod 3) :=
  ∑ r, ∑ c, if h r=a ∧ h c=b then f r c else 0

private theorem select {G : Type} [Fintype G] (h : G → ZMod 3) (a : ZMod 3) (z : ℝ) :
    (∑ x, if h x=a then z else 0)=(univ.filter (fun x => h x=a)).card*z := by
  rw [← sum_filter]
  simp

private theorem grouped {G : Type} [Fintype G] (h : G → ZMod 3) (q : ZMod 3)
    (f : G → G → ℝ) (z : ℝ) (hline : ∀ i, ∑ t, f i t=z) :
    (∑ i, ∑ t, if h i=q then f i t else 0)=(univ.filter (fun i => h i=q)).card*z := by
  rw [← select]
  apply sum_congr rfl
  intro i _
  by_cases hi : h i=q <;> simp [hi,hline]

theorem residue_three {G : Type} [Fintype G] [AddCommGroup G] (h : G →+ ZMod 3)
    (f : G → G → ℝ) (z : ℝ) (m : ℕ)
    (hm : ∀ a, (univ.filter (fun x => h x=a)).card=m)
    (hg : Fintype.card G=3*m) (hf : Mass f z) (a b : ZMod 3) :
    3*tile h f a b=m*z := by
  have rows := grouped h a f z hf.row
  have cols := grouped h b (fun c r => f r c) z hf.col
  rw [sum_comm] at cols
  have up := grouped h (b-a) (fun d r => f r (d+r)) z hf.up
  have down := grouped h (b+a) (fun d r => f r (d-r)) z hf.down
  rw [sum_comm] at up down
  have u (r : G) : (∑ d, if h d=b-a then f r (d+r) else 0)=
      ∑ c, if h c-h r=b-a then f r c else 0 := by
    simpa only [Equiv.coe_addRight,map_add,add_sub_cancel_right] using
      (Equiv.sum_comp (Equiv.addRight r) (fun c => if h c-h r=b-a then f r c else 0))
  have v (r : G) : (∑ d, if h d=b+a then f r (d-r) else 0)=
      ∑ c, if h c+h r=b+a then f r c else 0 := by
    simpa only [Equiv.coe_addRight,map_add,map_neg,neg_add_cancel_right,neg_add_rev,
      sub_eq_add_neg,add_neg_cancel_right] using
      (Equiv.sum_comp (Equiv.addRight (-r)) (fun c => if h c+h r=b+a then f r c else 0))
  simp_rw [u] at up
  simp_rw [v] at down
  rw [hm] at rows cols up down
  have e : (∑ r, ∑ c, ((if h r=a then f r c else 0)+(if h c=b then f r c else 0)+
      (if h c-h r=b-a then f r c else 0)+(if h c+h r=b+a then f r c else 0))) =
      ∑ r, ∑ c, (f r c+3*(if h r=a ∧ h c=b then f r c else 0)) := by
    apply sum_congr rfl
    intro r _
    exact sum_congr rfl (fun c _ => incidence (h r) (h c) a b (f r c))
  simp only [sum_add_distrib,← mul_sum,hf.row,sum_const,card_univ,nsmul_eq_mul,hg,Nat.cast_mul,
    Nat.cast_ofNat] at e
  unfold tile
  linarith

private theorem equal_fibers {G H : Type} [Fintype G] [AddCommGroup G] [AddCommGroup H]
    [DecidableEq H] (h : G →+ H) (onto : Function.Surjective h) (a b : H) :
    (univ.filter (fun x => h x=a)).card=(univ.filter (fun x => h x=b)).card := by
  obtain ⟨t,ht⟩ := onto (b-a)
  refine card_bij (fun x _ => x+t) ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter,mem_univ,true_and] at hx ⊢
    rw [map_add,hx,ht]
    abel
  · intro x _ y _ he
    exact add_right_cancel he
  · intro y hy
    simp only [mem_filter,mem_univ,true_and] at hy
    refine ⟨y-t,?_,sub_add_cancel _ _⟩
    simp only [mem_filter,mem_univ,true_and,map_sub,hy,ht]
    abel

theorem fiber_count {G H : Type} [Fintype G] [Fintype H] [AddCommGroup G]
    [AddCommGroup H] [DecidableEq H] (h : G →+ H) (onto : Function.Surjective h) (m : ℕ)
    (ht : Fintype.card G=Fintype.card H*m) (a : H) :
    (univ.filter (fun x => h x=a)).card=m := by
  have allsum : (∑ b : H, (univ.filter (fun x => h x=b)).card)=Fintype.card G := by
    calc
      _ = ∑ b : H, ∑ x : G, if h x=b then 1 else 0 := by
        apply sum_congr rfl
        intro b _
        rw [← sum_filter]
        simp
      _ = _ := by rw [sum_comm]; simp
  have eq (b : H) := equal_fibers h onto b a
  simp_rw [eq] at allsum
  simp only [sum_const,card_univ,nsmul_eq_mul,ht] at allsum
  exact Nat.eq_of_mul_eq_mul_left Fintype.card_pos allsum

def modThree {n : ℕ} (p : 3∣n) : ZMod n →+ ZMod 3 := (ZMod.castHom p (ZMod 3)).toAddMonoidHom

theorem Array.uniform_three {n : ℕ} [NeZero n] (g : Array n) (v : Space n) (m : ℕ)
    (hn : n=3*m) (a b : ZMod 3) :
    3*tile (modThree ⟨m,hn⟩) (weight g v) a b=m*‖v‖^2 := by
  let p : 3∣n := ⟨m,hn⟩
  have hc : Fintype.card (ZMod n)=Fintype.card (ZMod 3)*m := by simpa only [ZMod.card] using hn
  exact residue_three (modThree p) _ _ m
    (fiber_count _ (ZMod.castHom_surjective p) m hc) (by simpa only [ZMod.card] using hn) (g.mass v) a b

theorem weight_self {n : ℕ} [NeZero n] (g : Array n) (r c : ZMod n) :
    weight g (g.entry r c) r c=1 := by
  simp [weight,inner_self_eq_norm_sq_to_K,g.unit]

private theorem term_le_tile {G : Type} [Fintype G] (h : G → ZMod 3) (f : G → G → ℝ)
    (hf : ∀ x y, 0≤f x y) (r c : G) : f r c≤tile h f (h r) (h c) := by
  let term (x y : G) := if h x=h r ∧ h y=h c then f x y else 0
  have nn (x y : G) : 0≤term x y := by
    dsimp only [term]
    split
    · exact hf x y
    · exact le_rfl
  calc
    f r c = term r c := by simp [term]
    _ ≤ ∑ y, term r y := single_le_sum (f := term r) (fun i _ => nn r i) (mem_univ c)
    _ ≤ _ := single_le_sum (f := fun x => ∑ y, term x y)
      (fun x _ => sum_nonneg (fun y _ => nn x y)) (mem_univ r)

theorem Array.three_divisor_bound {n : ℕ} [NeZero n] (g : Array n) (m : ℕ) (hn : n=3*m) :
    3≤m := by
  let h := modThree (show 3∣n from ⟨m,hn⟩)
  let v := g.entry 0 0
  have eqn := g.uniform_three v m hn (h 0) (h 0)
  have low := term_le_tile h (weight g v) (fun x y => sq_nonneg _) 0 0
  rw [show weight g v 0 0=1 from weight_self g 0 0] at low
  rw [show ‖v‖=1 from g.unit 0 0] at eqn
  change 3*tile h (weight g v) (h 0) (h 0)=_ at eqn
  have : (3:ℝ)≤m := by nlinarith
  exact_mod_cast this

theorem no_order_three : IsEmpty (Array 3) := ⟨fun g => by have := g.three_divisor_bound 1 rfl; omega⟩
theorem no_order_six : IsEmpty (Array 6) := ⟨fun g => by have := g.three_divisor_bound 2 rfl; omega⟩

#print axioms Array.uniform_three
#print axioms no_order_six
end QuantumCertificate.Pandiagonal
