import Quantum.Hadamard.PaleyProjective

/-! Exact row sums and pairwise inner products of projective incidence sign
matrices over any residue ring, including the integers at modulus zero. -/
noncomputable section
namespace Hadamard.PG
open Finset HadamardMod

private theorem sign_over_extension {p q n : ℕ} [Fact q.Prime] {E : Type}
    [Field E] [Algebra (ZMod q) E] [Fintype E] [DecidableEq E] [FiniteDimensional (ZMod q) E]
    (L : E →ₗ[ZMod q] ZMod q) (hnz : L≠0) (rank : Module.finrank (ZMod q) E=n+2) :
    ∃ A : RowMatrix p (Fin (geom q (n+2))), (∀ i j, Sign (A i j)) ∧
      (∀ i, ∑ j, A i j = (geom q (n+2):ZMod p)-2*(geom q (n+1):ZMod p)) ∧
      (∀ i k, i≠k → ∑ j, A i j*A k j = (geom q (n+2):ZMod p)-4*(q:ZMod p)^n) := by
  classical
  let G := Additive (Projective (ZMod q) E)
  let s : G → ℤ := addWord (sectionOn L)
  have hc : Fintype.card G=geom q (n+2) := by
    rw [← Nat.card_eq_fintype_card]
    exact (Nat.card_congr Additive.toMul).trans (by rw [projective_card, ZMod.card, rank])
  have binary (x:G) : s x=0 ∨ s x=1 := by dsimp [s,addWord,sectionOn,sec]; split_ifs <;> simp
  have raw (t:G) : corr s t = (if t=0 then (q:ℤ)^n else 0)+(geom q n:ℤ) := by
    simpa only [ZMod.card] using section_corr L hnz n rank t
  have tot : (∑ x:G,s x)=(q:ℤ)^n+(geom q n:ℤ) := by
    have ss (x:G) : s x*s x=s x := by rcases binary x with h|h <;> simp [h]
    simpa only [corr,add_zero,ss,ite_true] using raw 0
  have sum0 : ∑ x:G,(s x:ZMod p)=(q:ZMod p)^n+(geom q n:ZMod p) := by
    simpa only [Int.cast_sum,Int.cast_add,Int.cast_pow,Int.cast_natCast] using
      congrArg (fun z:ℤ => (z:ZMod p)) tot
  let f : G → ZMod p := fun x => 1-2*(s x:ZMod p)
  let e := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨fun i j => f (e j-e i),?_,?_,?_⟩
  · intro i j
    rcases binary (e j-e i) with h|h
    · exact Or.inl (by simp [f,h])
    · exact Or.inr (by simp [f,h]; ring)
  · intro i
    rw [e.sum_comp (fun x:G => f (x-e i))]
    have translate : (∑ x:G,f (x-e i))=∑ x:G,f x := (Equiv.subRight (e i)).sum_comp f
    rw [translate]
    simp [f,sum_sub_distrib,←mul_sum,sum0,hc,geom_succ_last q n]
    ring
  · intro i k ne
    have t : e i-e k≠0 := sub_ne_zero.mpr (fun h => ne (e.injective h))
    have shifted : ∑ x:G, (s (x+(e i-e k)):ZMod p)=∑ x:G,(s x:ZMod p) :=
      Equiv.sum_comp (Equiv.addRight (e i-e k)) (fun x => (s x:ZMod p))
    have h := raw (e i-e k)
    rw [ite_eq_right t,zero_add] at h
    have cr : ∑ x:G,(s x:ZMod p)*(s (x+(e i-e k)):ZMod p)=(geom q n:ZMod p) := by
      simpa only [corr,Int.cast_sum,Int.cast_mul,Int.cast_natCast] using
        congrArg (fun z:ℤ => (z:ZMod p)) h
    have eq (u:G) : u-e i+(e i-e k)=u-e k := by abel
    calc
      _ = ∑ x:G,f x*f (x+(e i-e k)) := by
        rw [e.sum_comp (fun x:G => f (x-e i)*f (x-e k))]
        have hh := (Equiv.subRight (e i)).sum_comp (fun x => f x*f (x+(e i-e k)))
        change (∑ u:G, f (u-e i)*f (u-e i+(e i-e k))) = _ at hh
        simpa only [eq] using hh
      _ = _ := by
        have term (x:G) : f x*f (x+(e i-e k))=1-2*(s x:ZMod p)-2*(s (x+(e i-e k)):ZMod p)+
            4*((s x:ZMod p)*(s (x+(e i-e k)):ZMod p)) := by dsimp [f]; ring
        simp only [term,sum_add_distrib,sum_sub_distrib,←mul_sum,shifted,sum0,cr,sum_const,
          card_univ,nsmul_eq_mul,mul_one,hc]
        ring

/-- The signed point-hyperplane incidence matrix of PG(n+1,q), ordered on a single Fin type. -/
theorem projective_sign (p q n : ℕ) [Fact q.Prime] :
    ∃ A : RowMatrix p (Fin (geom q (n+2))), (∀ i j, Sign (A i j)) ∧
      (∀ i, ∑ j, A i j = (geom q (n+2):ZMod p)-2*(geom q (n+1):ZMod p)) ∧
      (∀ i k, i≠k → ∑ j, A i j*A k j = (geom q (n+2):ZMod p)-4*(q:ZMod p)^n) := by
  let E := GaloisField q (n+2)
  let : Fintype E := Fintype.ofFinite E
  classical
  exact sign_over_extension (Algebra.trace (ZMod q) E) (Algebra.trace_ne_zero (ZMod q) E)
    (GaloisField.finrank q (show n+2≠0 by omega))

#print axioms projective_sign
end Hadamard.PG

