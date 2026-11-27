import Quantum.Hadamard.ComplementaryProduct
import Quantum.Hadamard.PaleyProjective

/-! A constant word and the signed Singer hyperplane word form a periodic complementary pair
when the projective cardinality is twice the size of a nontrivial linear fiber. -/
noncomputable section
namespace HadamardMod.Periodic
open Finset Hadamard.PG

private theorem over_field {m q n : ℕ} [Fact q.Prime] {E : Type}
    [Field E] [Algebra (ZMod q) E] [Fintype E] [DecidableEq E] [FiniteDimensional (ZMod q) E]
    (L : E →ₗ[ZMod q] ZMod q) (hnz : L≠0) (rank : Module.finrank (ZMod q) E=n+2)
    (mass : (geom q (n+2):ZMod m)=2*(q:ZMod m)^n) : HasLength m (geom q (n+2)) := by
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
  have sum0 : ∑ x:G,(s x:ZMod m)=(q:ZMod m)^n+(geom q n:ZMod m) := by
    simpa only [Int.cast_sum,Int.cast_add,Int.cast_pow,Int.cast_natCast] using
      congrArg (fun z:ℤ => (z:ZMod m)) tot
  let f : G → ZMod m := fun x => 1-2*(s x:ZMod m)
  refine ⟨G,inferInstance,inferInstance,hc,⟨⟨fun _ => 1,f,fun _ => Or.inl rfl,?_,?_⟩⟩⟩
  · intro i
    rcases binary i with h|h
    · exact Or.inl (by simp [f,h])
    · exact Or.inr (by simp [f,h]; ring)
  · intro t nz
    have shifted := Equiv.sum_comp (Equiv.addRight t) (fun x:G => (s x:ZMod m))
    change (∑ x:G,(s (x+t):ZMod m))=∑ x:G,(s x:ZMod m) at shifted
    have h := raw t
    rw [ite_eq_right nz,zero_add] at h
    have cr : ∑ x:G,(s x:ZMod m)*(s (x+t):ZMod m)=(geom q n:ZMod m) := by
      simpa only [corr,Int.cast_sum,Int.cast_mul,Int.cast_natCast] using
        congrArg (fun z:ℤ => (z:ZMod m)) h
    have term (x:G) : f x*f (x+t)=1-2*(s x:ZMod m)-2*(s (x+t):ZMod m)+
        4*((s x:ZMod m)*(s (x+t):ZMod m)) := by dsimp [f]; ring
    simp only [cyclicCorr,term,sum_add_distrib,sum_sub_distrib,←mul_sum,shifted,sum0,cr,sum_const,
      card_univ,nsmul_eq_mul,mul_one,hc,mass]
    ring

theorem singer {m q n : ℕ} [Fact q.Prime]
    (mass : (geom q (n+2):ZMod m)=2*(q:ZMod m)^n) : HasLength m (geom q (n+2)) := by
  let E := GaloisField q (n+2)
  let : Fintype E := Fintype.ofFinite E
  classical
  exact over_field (Algebra.trace (ZMod q) E) (Algebra.trace_ne_zero (ZMod q) E)
    (GaloisField.finrank q (show n+2≠0 by omega)) mass

#print axioms singer
end HadamardMod.Periodic
