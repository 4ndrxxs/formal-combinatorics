import PermanentWitnesses
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic

/-! An integral affine plane in the three-row singular space of the five-by-five
permanent, its lower Hessian block, and exact low-degree interpolation. -/
noncomputable section
open Polynomial Matrix Finset PermanentFive
namespace PermanentCurve
def base : Matrix Idx Idx ℤ :=
  !![1, 1, 1, 1, 1;
    1, -1, 1, 1, 1;
    1, 1, -1, -1, 0;
    0, 0, 0, 0, 0;
    0, 0, 0, 0, 0]
def slope : Matrix Idx Idx ℤ :=
  !![-1, -1, -2, 0, 1;
    1, 1, -2, 0, 1;
    0, 0, -2, 1, 2;
    0, 0, 0, 0, 0;
    0, 0, 0, 0, 0]
variable {R S : Type*} [CommRing R] [CommRing S]

def plane (t u : R) (c : Cell) : R := base c.1 c.2 + (slope c.1 c.2 : R)*t +
  if c=(2,0) then u else 0

def block (t u : R) : Matrix Idx Idx R :=
  !![0, (-4)*t^3 + (-10)*t^2 + 2*t + (-4), 2*t + 2, (-4)*t^2 + (-2)*t + 2, (-4)*t + 2;
     (-4)*t^3 + (-10)*t^2 + 2*t + (-4), 0, 2*t^2 + 2*t*u + 6*t + 2*u, (-4)*t^2*u + (-16)*t^2 + (-2)*t*u + (-4)*t + 2*u, (-4)*t^2 + (-4)*t*u + (-2)*t + 2*u + (-2);
     2*t + 2, 2*t^2 + 2*t*u + 6*t + 2*u, 0, (-4)*t^3 + 4*t^2 + 2*t + 2, (-2)*t^3 + 4*t^2 + (-2)*t + 2;
     (-4)*t^2 + (-2)*t + 2, (-4)*t^2*u + (-16)*t^2 + (-2)*t*u + (-4)*t + 2*u, (-4)*t^3 + 4*t^2 + 2*t + 2, 0, 4*t^3 + (-2)*t^2 + (-6)*t + 2;
     (-4)*t + 2, (-4)*t^2 + (-4)*t*u + (-2)*t + 2*u + (-2), (-2)*t^3 + 4*t^2 + (-2)*t + 2, 4*t^3 + (-2)*t^2 + (-6)*t + 2, 0]

theorem plane_map (f : R →+* S) (t u : R) : f ∘ plane t u = plane (f t) (f u) := by
  funext c
  by_cases eq : c=(2,0) <;> simp [plane,eq]

theorem block_map (f : R →+* S) (t u : R) : (block t u).map f = block (f t) (f u) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block,Matrix.map_apply,map_ofNat]

def actual (t u : R) (i j : Idx) : R := secondAt (plane t u) (3,i) (4,j)

theorem actual_map (f : R →+* S) (t u : R) (i j : Idx) :
    f (actual t u i j) = actual (f t) (f u) i j := by
  rw [actual,←second_map,plane_map]
  rfl

theorem actual_degree (t u : R[X]) (ht : t.natDegree ≤ 1) (hu : u.natDegree ≤ 1) (i j : Idx) :
    (actual t u i j).natDegree ≤ 3 := by
  classical
  have cells (c : Cell) : (plane t u c).natDegree ≤ 1 := by
    by_cases h : c=(2,0) <;> simp only [plane,h,ite_true,ite_false,add_zero] <;>
      compute_degree <;> omega
  unfold actual secondAt
  apply natDegree_sum_le_of_forall_le
  intro p _
  split_ifs with h
  · refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ 1 (fun x _ ↦ cells (p x,x))).trans ?_
    have he : i ∈ (univ.erase j : Finset Idx) := mem_erase.mpr ⟨h.2.1,mem_univ _⟩
    simp [card_erase_of_mem he,card_erase_of_mem (mem_univ j),Idx]
  · simp

theorem block_degree (t u : R[X]) (ht : t.natDegree ≤ 1) (hu : u.natDegree ≤ 1) (i j : Idx) :
    ((block t u) i j).natDegree ≤ 3 := by
  fin_cases i <;> fin_cases j <;> simp [block] <;> compute_degree <;> omega

variable {K : Type*} [Field K] [CharZero K]

theorem grid_eq {d : ℕ} (p q : K[X]) (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d)
    (agree : ∀ a : Fin (d+1), p.eval (a.val : K) = q.eval (a.val : K)) : p=q := by
  classical
  let S := (univ : Finset (Fin (d+1))).image (fun a ↦ (a.val : K))
  have card : S.card = d+1 := by
    rw [show S.card = _ from Finset.card_image_of_injective _ (Nat.cast_injective.comp Fin.val_injective)]
    simp
  apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq S
  · rw [card]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast (show p.natDegree < d+1 by omega))
  · rw [card]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast (show q.natDegree < d+1 by omega))
  · intro x hx
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
    exact agree a

#print axioms actual_degree
end PermanentCurve
