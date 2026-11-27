import UniversalBipartiteWalk
import Quantum.OrbitPeriodic

/-! Rational coordinates, preservation of the Euclidean norm, and the exact relation
between the published complex edge walk and its rational matrix powers. -/
noncomputable section
namespace BipartiteEdgeWalk.Decision
open Finset Function
open scoped BigOperators
variable {E V L R : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
variable [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

def amplitude (a : E) (b : E) : ℚ := if b=a then 1 else 0

def scatter (s : E → V) : Module.End ℚ (E → ℚ) where
  toFun f a := 2*(∑ b ∈ fiber s (s a), f b)/(degree s (s a):ℚ)-f a
  map_add' f g := by
    funext a
    simp only [Pi.add_apply,Finset.sum_add_distrib]
    ring
  map_smul' c f := by
    funext a
    simp only [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum,RingHom.id_apply]
    ring

def step (l : E → L) (r : E → R) : Module.End ℚ (E → ℚ) := scatter l * scatter r

private theorem degree_nonzero (s : E → V) (hs : Surjective s) (u : V) : degree s u≠0 := by
  obtain ⟨e,he⟩ := hs u
  exact Finset.card_ne_zero.mpr ⟨e,by simp [fiber,he]⟩

private theorem on_fiber (s : E → V) (hs : Surjective s) (f : E → ℚ) (u : V) :
    (∑ a ∈ fiber s u, scatter s f a)=(∑ a ∈ fiber s u, f a) ∧
    (∑ a ∈ fiber s u, (scatter s f a)^2)=(∑ a ∈ fiber s u, (f a)^2) := by
  let B := fiber s u
  let total := ∑ a ∈ B, f a
  let mean2 := 2*total/(degree s u:ℚ)
  have ha (a : E) (mem : a∈B) : scatter s f a=mean2-f a := by
    have eq : s a=u := (mem_filter.mp mem).2
    change 2*(∑ b ∈ fiber s (s a), f b)/(degree s (s a):ℚ)-f a=_
    rw [eq]
  have pos : (degree s u:ℚ)≠0 := by exact_mod_cast degree_nonzero s hs u
  have card : B.card=degree s u := rfl
  constructor
  · calc
      _ = ∑ a ∈ B, (mean2-f a) := sum_congr rfl ha
      _ = (B.card:ℚ)*mean2-total := by simp [total,sum_sub_distrib]
      _ = _ := by rw [card]; dsimp [mean2,total,B]; field_simp; ring
  · calc
      _ = ∑ a ∈ B, (mean2^2-(2*mean2)*f a+(f a)^2) := by
        apply sum_congr rfl
        intro a mem
        rw [ha a mem]
        ring
      _ = (B.card:ℚ)*mean2^2-(2*mean2)*total+∑ a ∈ B, (f a)^2 := by
        simp [total,sum_add_distrib,sum_sub_distrib,Finset.mul_sum]
      _ = _ := by rw [card]; dsimp [mean2,total,B]; field_simp; ring

private theorem regroup (s : E → V) (f : E → ℚ) :
    (∑ u, ∑ a ∈ fiber s u, f a)=∑ a, f a :=
  Finset.sum_fiberwise_of_maps_to (s:=univ) (t:=univ) (g:=s) (fun _ _ => mem_univ _) f

private theorem scatter_preserves (s : E → V) (hs : Surjective s) (f : E → ℚ) :
    (∑ e, scatter s f e)=∑ e, f e ∧ (∑ e, (scatter s f e)^2)=∑ e, (f e)^2 := by
  constructor
  · rw [← regroup s (scatter s f),← regroup s f]
    exact sum_congr rfl (fun u _ => (on_fiber s hs f u).1)
  · rw [← regroup s (fun e => (scatter s f e)^2),← regroup s (fun e => (f e)^2)]
    exact sum_congr rfl (fun u _ => (on_fiber s hs f u).2)

theorem scatter_involutive (s : E → V) (hs : Surjective s) : Involutive (scatter s) := by
  intro f
  funext e
  change 2*(∑ b ∈ fiber s (s e), scatter s f b)/(degree s (s e):ℚ)-scatter s f e=f e
  rw [(on_fiber s hs f (s e)).1]
  change _-(2*(∑ b ∈ fiber s (s e),f b)/(degree s (s e):ℚ)-f e)=f e
  ring

theorem step_preserves (l : E → L) (r : E → R) (hl : Surjective l) (hr : Surjective r)
    (f : E → ℚ) : (∑ e, step l r f e)=∑ e, f e ∧ (∑ e, (step l r f e)^2)=∑ e, (f e)^2 := by
  change (∑ e, scatter l (scatter r f) e)=_ ∧ (∑ e, (scatter l (scatter r f) e)^2)=_
  exact ⟨(scatter_preserves l hl _).1.trans (scatter_preserves r hr _).1,
    (scatter_preserves l hl _).2.trans (scatter_preserves r hr _).2⟩

theorem step_injective (l : E → L) (r : E → R) (hl : Surjective l) (hr : Surjective r) :
    Injective (step l r) := by
  intro f g eq
  have h := (step_preserves l r hl hr (f-g)).2
  rw [map_sub,eq,sub_self] at h
  simp only [Pi.zero_apply,zero_pow (by decide : 2≠0),sum_const_zero] at h
  funext e
  have le := single_le_sum (s:=univ) (fun i _ => sq_nonneg ((f-g) i)) (mem_univ e)
  rw [← h] at le
  simp only [Pi.sub_apply] at le
  nlinarith [sq_nonneg (f e-g e)]

theorem orbit_invariant (l : E → L) (r : E → R) (hl : Surjective l) (hr : Surjective r)
    (a : E) (k : ℕ) :
    (∑ e, ((step l r)^k) (amplitude a) e)=1 ∧ (∑ e, (((step l r)^k) (amplitude a) e)^2)=1 := by
  induction k with
  | zero => simp [amplitude]
  | succ k ih =>
    rw [pow_succ',mul_apply_eq_comp]
    exact ⟨(step_preserves l r hl hr _).1.trans ih.1,(step_preserves l r hl hr _).2.trans ih.2⟩

theorem coordinate_bound (l : E → L) (r : E → R) (hl : Surjective l) (hr : Surjective r)
    (a : E) (k : ℕ) (e : E) : |((step l r)^k) (amplitude a) e|≤1 := by
  have le := single_le_sum (s:=univ) (fun j _ => sq_nonneg (((step l r)^k) (amplitude a) j)) (mem_univ e)
  rw [(orbit_invariant l r hl hr a k).2] at le
  rw [abs_le]
  constructor <;> nlinarith

def toComplex (f : E → ℚ) (e : E) : ℂ := f e

private theorem complex_scatter (s : E → V) (f : E → ℚ) :
    toComplex (scatter s f)=reflect s (toComplex f) := by
  funext e
  change ((2*(∑ b ∈ fiber s (s e), f b)/(degree s (s e):ℚ)-f e:ℚ):ℂ)=_
  push_cast
  simp [reflect,mass,toComplex]

theorem complex_orbit (l : E → L) (r : E → R) (a : E) (k : ℕ) :
    toComplex (((step l r)^k) (amplitude a))=(walk l r)^[k] (delta a) := by
  induction k with
  | zero => funext e; simp [toComplex,amplitude,delta,apply_ite]
  | succ k ih =>
    rw [pow_succ',mul_apply_eq_comp,iterate_succ_apply']
    change toComplex (scatter l (scatter r _))=_
    rw [complex_scatter,complex_scatter,ih]
    rfl

/-- A transfer in the original complex walk, allowing an arbitrary unit phase. -/
def PerfectAt (l : E → L) (r : E → R) (a b : E) (k : ℕ) :=
  ∃ z : ℂ, ‖z‖=1 ∧ (walk l r)^[k] (delta a)=z • delta b

theorem perfectAt_iff (l : E → L) (r : E → R) (hl : Surjective l) (hr : Surjective r)
    (a b : E) (k : ℕ) : PerfectAt l r a b k ↔ ((step l r)^k) (amplitude a)=amplitude b := by
  constructor
  · rintro ⟨z,_,eq⟩
    rw [← complex_orbit] at eq
    have hs := congrArg (fun f : E → ℂ => ∑ e, f e) eq
    have sumc : (∑ e, toComplex (((step l r)^k) (amplitude a)) e)=1 := by
      simpa [toComplex] using congrArg (fun x : ℚ => (x:ℂ)) (orbit_invariant l r hl hr a k).1
    have same : (1:ℂ)=z := by simpa [sumc,delta] using hs
    rw [← same,one_smul] at eq
    funext e
    have e' := congrFun eq e
    change ((((step l r)^k) (amplitude a) e:ℚ):ℂ)=delta b e at e'
    have emb : (amplitude b e:ℂ)=delta b e := by simp [amplitude,delta,apply_ite]
    rw [← emb] at e'
    exact_mod_cast e'
  · intro h
    refine ⟨1,by simp,?_⟩
    rw [← complex_orbit,h,one_smul]
    funext e
    simp [toComplex,amplitude,delta,apply_ite]

#print axioms perfectAt_iff
#print axioms coordinate_bound
#print axioms step_injective
end BipartiteEdgeWalk.Decision
