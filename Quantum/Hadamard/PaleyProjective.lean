import Quantum.Hadamard.PaleyGeometry

/-! The projective point/hyperplane incidence matrix gives modular Hadamard
extenders. Its step has an arithmetic expression which can be odd or twice odd. -/
noncomputable section
namespace Hadamard.PG
open Finset HadamardMod

theorem geom_succ_last (q n : ℕ) : geom q (n+1) = geom q n+q^n := by
  exact sum_range_succ _ _

theorem geom_at_one (q m d : ℕ) (h : (q : ZMod m) = 1) :
    (geom q d : ZMod m) = d := by simp [geom,h]

theorem geom_zero_mod {p q d : ℕ} [Fact p.Prime] (h : (q:ZMod p)^d=1)
    (ne : (q : ZMod p) ≠ 1) : (geom q d : ZMod p)=0 := by
  have e := congrArg (fun z : ℤ => (z : ZMod p)) (geom_int q d)
  simp only [Int.cast_mul, Int.cast_natCast, Int.cast_sub, Int.cast_one, Int.cast_pow,
    h, sub_self] at e
  exact (mul_eq_zero.mp e).resolve_right (sub_ne_zero.mpr ne)

private theorem points_extender {p q n : ℕ} [Fact p.Prime] [Fact q.Prime]
    {E : Type} [Field E] [Algebra (ZMod q) E] [Fintype E] [DecidableEq E] [FiniteDimensional (ZMod q) E]
    (L : E →ₗ[ZMod q] ZMod q) (hnz : L ≠ 0) (rank : Module.finrank (ZMod q) E=n+2)
    (unit : (q:ZMod p)^(n+1)=1) (ne : (q:ZMod p) ≠ 1) :
    Nonempty (Extender p (Fin (geom q (n+2))) (4*(q:ZMod p)^n)) := by
  classical
  let G := Additive (Projective (ZMod q) E)
  let s : G → ℤ := addWord (sectionOn L)
  have hc : Fintype.card G=geom q (n+2) := by
    rw [← Nat.card_eq_fintype_card]
    exact (Nat.card_congr Additive.toMul).trans (by rw [projective_card, ZMod.card, rank])
  have hzero := geom_zero_mod unit ne
  have dim : (Fintype.card G : ZMod p) = 1 := by
    rw [hc, show n+2=n+1+1 by omega,geom_succ]
    push_cast
    simp [hzero]
  have binary (x : G) : s x=0 ∨ s x=1 := by
    dsimp [s,addWord,sectionOn,sec]
    split_ifs <;> simp
  have raw (t : G) : corr s t = (if t=0 then (q:ℤ)^n else 0)+(geom q n:ℤ) := by
    simpa only [ZMod.card] using section_corr L hnz n rank t
  have tot : (∑ x:G,s x) = (geom q (n+1):ℤ) := by
    have h := raw 0
    have ss (x : G) : s x*s x=s x := by rcases binary x with hx|hx <;> simp [hx]
    simp only [corr, add_zero, ss, ite_true, geom_succ_last, Nat.cast_add, Nat.cast_pow] at h ⊢
    rw [h,add_comm]
  let f : G → ZMod p := fun x => 1-2*(s x:ZMod p)
  have sm : ∑ x : G, (s x : ZMod p)=0 := by
    simpa only [Int.cast_sum,Int.cast_natCast,hzero] using congrArg (fun z : ℤ => (z:ZMod p)) tot
  have row0 : ∑ x : G, f x=1 := by
    simp [f,sum_sub_distrib,←mul_sum,sm,dim]
  have off0 (a:G) (ha:a≠0) : ∑ x:G,f x*f (x+a) = 1-4*(q:ZMod p)^n := by
    have sm' : ∑ x:G,((s (x+a):ℤ):ZMod p)=0 :=
      (Equiv.sum_comp (Equiv.addRight a) (fun x => (s x:ZMod p))).trans sm
    have h := raw a
    rw [ite_eq_right ha,zero_add] at h
    have c : ∑ x:G,(s x:ZMod p)*(s (x+a):ZMod p)=(geom q n:ZMod p) := by
      simpa only [corr,Int.cast_sum,Int.cast_mul,Int.cast_natCast] using congrArg (fun y:ℤ => (y:ZMod p)) h
    have gx : (geom q n:ZMod p)+(q:ZMod p)^n=0 := by
      simpa only [geom_succ_last,Nat.cast_add,Nat.cast_pow] using hzero
    have term (x:G) : f x*f (x+a)=1-2*(s x:ZMod p)-2*(s (x+a):ZMod p)+
        4*((s x:ZMod p)*(s (x+a):ZMod p)) := by dsimp [f]; ring
    simp only [term,sum_add_distrib,sum_sub_distrib,←mul_sum,sm,sm',c,sum_const,card_univ,
      nsmul_eq_mul,mul_one,dim,mul_zero,sub_zero]
    linear_combination 4*gx
  let e := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨{entry := fun i j => f (e j-e i), sign := ?_, row := ?_, off := ?_, dim := ?_, pos := ?_}⟩
  · intro i j
    rcases binary (e j-e i) with h|h
    · exact Or.inl (by simp [f,h])
    · exact Or.inr (by simp [f,h]; ring)
  · intro i
    exact (e.sum_comp (fun x => f (x-e i))).trans (((Equiv.subRight (e i)).sum_comp f).trans row0)
  · intro i k hk
    have d : e i-e k≠0 := sub_ne_zero.mpr (fun h => hk (e.injective h))
    have H := ((Equiv.subRight (e i)).sum_comp (fun x => f x*f (x+(e i-e k)))).trans (off0 _ d)
    have eq (x:G) : x-e i+(e i-e k)=x-e k := by abel
    change (∑ x:G,f (x-e i)*f (x-e i+(e i-e k)))=_ at H
    rw [show (∑ j, f (e j-e i)*f (e j-e k)) = ∑ x:G,f (x-e i)*f (x-e k) from
      e.sum_comp (fun x => f (x-e i)*f (x-e k))]
    simpa only [eq] using H
  · simpa [hc] using dim
  · rw [Fintype.card_fin, ←hc]; exact Fintype.card_pos

/-- Projective space of dimension `n+1` supplies an extender at residue `4*q^n`. -/
theorem prime_extender {p q n : ℕ} [Fact p.Prime] [Fact q.Prime]
    (unit : (q:ZMod p)^(n+1)=1) (ne : (q:ZMod p)≠1) :
    Nonempty (Extender p (Fin (geom q (n+2))) (4*(q:ZMod p)^n)) := by
  let E := GaloisField q (n+2)
  let : Fintype E := Fintype.ofFinite E
  classical
  exact points_extender (Algebra.trace (ZMod q) E) (Algebra.trace_ne_zero (ZMod q) E)
    (GaloisField.finrank q (show n+2≠0 by omega)) unit ne

#print axioms prime_extender
end Hadamard.PG

