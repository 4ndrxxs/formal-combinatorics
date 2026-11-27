module
public import Quantum.OrbitRecurrence

/-! A monic integral annihilator makes a bounded injective rational orbit periodic.
Polynomial division bounds all coordinate denominators at once. -/
@[expose] public section
noncomputable section
open Polynomial Finset
namespace RationalOrbit

variable {E : Type*} [Fintype E]

private theorem coordinate_formula (T : Module.End ℚ (E → ℚ)) (v : E → ℚ) (P : ℤ[X]) (e : E) :
    act T v (P.map castQ) e =
      ∑ i ∈ range (P.natDegree+1), (P.coeff i:ℚ)*((T^i) v e) := by
  conv_lhs => rw [P.as_sum_range_C_mul_X_pow]
  simp [act,Polynomial.map_sum,LinearMap.sum_apply,Finset.sum_apply,
    mul_apply_eq_comp,Module.algebraMap_end_apply,castQ]

private theorem reduce_power (T : Module.End ℚ (E → ℚ)) (v : E → ℚ) {D : ℤ[X]}
    (ann : act T v (D.map castQ)=0) (k : ℕ) :
    (T^k) v = act T v (((X^k:ℤ[X]) %ₘ D).map castQ) := by
  let Q := (X^k:ℤ[X]) /ₘ D
  have eq := modByMonic_add_div (X^k:ℤ[X]) D
  change _ + D*Q = _ at eq
  rw [mul_comm D Q] at eq
  have z : act T v ((Q*D).map castQ)=0 := by
    simpa [act,mul_apply_eq_comp] using congrArg (aeval T (Q.map castQ)) ann
  have g := congrArg (fun P : ℤ[X] => act T v (P.map castQ)) eq
  have g' : act T v (((X^k:ℤ[X]) %ₘ D).map castQ) + act T v ((Q*D).map castQ) = (T^k) v := by
    simpa [act] using g
  rw [z,add_zero] at g'
  exact g'.symm

private def gridded (B : ℕ) (x : ℚ) : Prop := ∃ a : ℤ, (a:ℚ)=(B:ℚ)*x

private theorem grid_sum {B : ℕ} (s : Finset ℕ) (z : ℕ → ℤ) (f : ℕ → ℚ)
    (h : ∀ i ∈ s, gridded B (f i)) : gridded B (∑ i ∈ s, (z i:ℚ)*f i) := by
  classical
  choose a ha using fun i (hi : i∈s) => h i hi
  let g (i : ℕ) : ℤ := if hi : i∈s then a i hi else 0
  refine ⟨∑ i ∈ s, z i*g i, ?_⟩
  push_cast
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro i hi
  simp [g,hi,ha,mul_left_comm]

private theorem common_grid (T : Module.End ℚ (E → ℚ)) (v : E → ℚ) {D : ℤ[X]}
    (mon : D.Monic) (ann : act T v (D.map castQ)=0) :
    ∃ B : ℕ, 0<B ∧ ∀ k e, gridded B ((T^k) v e) := by
  classical
  let J := Fin (D.natDegree+1) × E
  let q (j : J) : ℚ := (T^(j.1:ℕ)) v j.2
  let B := univ.lcm (fun j : J => (q j).den)
  have pos : 0<B := Nat.pos_of_ne_zero ((Finset.lcm_ne_zero_iff).mpr (fun j _ => (q j).den_pos.ne'))
  have clears (j : J) : gridded B (q j) := by
    obtain ⟨t,ht⟩ : (q j).den∣B := dvd_lcm (mem_univ j)
    refine ⟨(q j).num*(t:ℤ), ?_⟩
    push_cast
    rw [ht,Nat.cast_mul,← Rat.mul_den_eq_num]
    ring
  refine ⟨B,pos,fun k e => ?_⟩
  let P := (X^k:ℤ[X]) %ₘ D
  have sz : P.natDegree≤D.natDegree := natDegree_modByMonic_le _ mon
  rw [reduce_power T v ann k,coordinate_formula]
  apply grid_sum
  intro i hi
  change i∈range (P.natDegree+1) at hi
  exact clears (⟨i,by have := mem_range.mp hi; omega⟩,e)

/-- The bound H is a uniform coordinate bound on the given rational orbit. -/
theorem periodic_of_monic (T : Module.End ℚ (E → ℚ)) (hinj : Function.Injective T)
    (v : E → ℚ) {D : ℤ[X]} (mon : D.Monic) (ann : act T v (D.map castQ)=0)
    (H : ℕ) (bound : ∀ k e, |(T^k) v e|≤H) :
    ∃ k : ℕ, 0<k ∧ (T^k) v=v := by
  classical
  obtain ⟨B,hB,hg⟩ := common_grid T v mon ann
  choose z hz using hg
  let F := {n : ℤ // n∈Set.Icc (-((B:ℤ)*H)) ((B:ℤ)*H)}
  letI : Finite F := (Set.finite_Icc (-((B:ℤ)*H)) ((B:ℤ)*H)).to_subtype
  have inside (k : ℕ) (e : E) : z k e∈Set.Icc (-((B:ℤ)*H)) ((B:ℤ)*H) := by
    have h := mul_le_mul_of_nonneg_left (bound k e) (by positivity : (0:ℚ)≤B)
    have h' : |(z k e:ℚ)|≤(B:ℚ)*H := by simpa [hz,abs_mul,abs_of_nonneg (by positivity : (0:ℚ)≤B)] using h
    have h'' := abs_le.mp h'
    constructor
    · exact_mod_cast h''.1
    · exact_mod_cast h''.2
  let code (k : ℕ) (e : E) : F := ⟨z k e,inside k e⟩
  obtain ⟨a,b,ne,eq⟩ := Finite.exists_ne_map_eq_of_infinite code
  have repeatEq : (T^a) v=(T^b) v := by
    funext e
    have ze : z a e=z b e := congrArg Subtype.val (congrFun eq e)
    have h : (B:ℚ)*((T^a) v e)=(B:ℚ)*((T^b) v e) := by rw [← hz,← hz,ze]
    exact mul_left_cancel₀ (by exact_mod_cast hB.ne' : (B:ℚ)≠0) h
  wlog lt : a<b generalizing a b
  · exact this b a ne.symm eq.symm repeatEq.symm (by omega)
  refine ⟨b-a,by omega,?_⟩
  have inj := hinj.iterate a
  apply inj
  have eb : b=a+(b-a) := by omega
  simpa only [← pow_apply_eq_iterate,← mul_apply_eq_comp,← pow_add,← eb] using repeatEq.symm

end RationalOrbit
