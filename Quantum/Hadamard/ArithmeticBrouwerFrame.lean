import Quantum.Hadamard.ArithmeticBrouwerGeometry

/-! The small two-column deletion used in Brouwer's design. Doubling a
Paley matrix gives a direct parametrization by a sign and a field element. -/
noncomputable section
namespace Hadamard.Brouwer
open HadamardMod Finset

structure Frame (q : ℕ) [Fact q.Prime] (T V : Type) [Fintype T] [Fintype V] where
  top : T → ZMod q → ℤ
  bot : T → V → ℤ
  cardT : Fintype.card T=2*q
  cardV : Fintype.card V=q+1
  topSign : ∀ t x, Sign (top t x)
  botSign : ∀ t x, Sign (bot t x)
  topRow : ∀ t, (∑ x,top t x)= -1
  botRow : ∀ t, (∑ x,bot t x)=0
  joint : ∀ t s, t≠s →
    (∑ u,top t u*top s u)+(∑ v,bot t v*bot s v)= -1

theorem frame {q : ℕ} [Fact q.Prime] (h : q%4=3) :
    Nonempty (Frame q (Bool × ZMod q) (Option (ZMod q))) := by
  let C := (paleySkew 0 q h).inner
  let K (i j:ZMod q) : ℤ := -C.entry i j
  let e (b:Bool) : ℤ := if b then -1 else 1
  let B (i:ZMod q) (v:Option (ZMod q)) : ℤ := v.elim 1 (K i)
  have ks (x y) : Sign (K x y) := by
    rcases C.sign x y with hh|hh <;> simp [K,hh,Sign]
  have kr (x) : (∑ y,K x y)= -1 := by
    change (∑ y,-C.entry x y)= -1
    rw [sum_neg_distrib,C.row]
  have ko (x y) (ne:x≠y) : (∑ z,K x z*K y z)= -1 := by
    have fac (z) : K x z*K y z=C.entry x z*C.entry y z := by
      change (-(C.entry x z : ℤ))*(-(C.entry y z : ℤ))=(C.entry x z:ℤ)*(C.entry y z:ℤ)
      ring
    simp only [fac]
    exact C.off x y ne
  have es (b) : Sign (e b) := by cases b <;> simp [e,Sign]
  have bs (i v) : Sign (B i v) := by cases v <;> simp [B,Sign] <;> exact ks _ _
  have br (i) : (∑ v,B i v)=0 := by rw [Fintype.sum_option]; simp [B,kr]
  have bd (i j) : (∑ v,B i v*B j v)=1+∑ u,K i u*K j u := by rw [Fintype.sum_option]; simp [B]
  refine ⟨⟨fun t => K t.2,fun t v => e t.1*B t.2 v,by simp,by simp,fun _ _ => ks _ _,
    fun t v => sign_mul (es _) (bs _ _),fun _ => kr _,?_,?_⟩⟩
  · intro t
    rw [← mul_sum,br,mul_zero]
  · rintro ⟨a,i⟩ ⟨b,j⟩ ne
    dsimp only
    have fac (v) : e a*B i v*(e b*B j v)=(e a*e b)*(B i v*B j v) := by ring
    simp only [fac,← mul_sum,bd]
    by_cases hsame : a=b
    · subst b
      have nij : i≠j := fun hh => ne (Prod.ext rfl hh)
      rw [ko i j nij,sign_sq (es a)]
      norm_num
    · have ab : e a*e b= -1 := by cases a <;> cases b <;> simp_all [e]
      rw [ab]
      ring

end Hadamard.Brouwer
