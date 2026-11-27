import Quantum.Hadamard.GoethalsTwo

/-! Turyn multiplication of periodic complementary binary pairs over an odd modulus.
The abelian group supporting the product is the direct product of the two groups. -/
noncomputable section
namespace HadamardMod.Periodic
open Finset
variable {m : ℕ} {G K : Type} [Fintype G] [AddCommGroup G] [Fintype K] [AddCommGroup K]

structure Pair (m : ℕ) (G : Type) [Fintype G] [AddCommGroup G] where
  a : Seq m G
  b : Seq m G
  pos : ∀ i, Sign (a i)
  neg : ∀ i, Sign (b i)
  off : ∀ s:G, s≠0 → cyclicCorr a a s+cyclicCorr b b s=0

def HasLength (m k : ℕ) : Prop :=
  ∃ (G : Type) (f : Fintype G) (g : AddCommGroup G),
    @Fintype.card G f=k ∧ Nonempty (@Pair m G f g)

theorem matrix {k:ℕ} (h : HasLength m k) : AtOrder m (2*k) := by
  obtain ⟨G,f,g,card,⟨P⟩⟩ := h
  letI := f
  letI := g
  rw [← card]
  exact two_circulants P.a P.b P.pos P.neg P.off

private def tensor (a : Seq m G) (b : Seq m K) : Seq m (G×K) := fun p => a p.1*b p.2
private def rev (a : Seq m G) : Seq m G := fun x => a (-x)

private theorem corr_tensor (a b : Seq m G) (c d : Seq m K) (s:G) (t:K) :
    cyclicCorr (tensor a c) (tensor b d) (s,t) = cyclicCorr a b s*cyclicCorr c d t := by
  rw [cyclicCorr,Fintype.sum_prod_type]
  change (∑ i:G, ∑ j:K, a i*c j*(b (i+s)*d (j+t)))=_
  have eq (i:G) (j:K) : a i*c j*(b (i+s)*d (j+t))=a i*b (i+s)*(c j*d (j+t)) := by ring
  simp only [eq,← mul_sum,← sum_mul,cyclicCorr]

private theorem corr_rev (a b : Seq m G) (s:G) : cyclicCorr (rev a) (rev b) s=cyclicCorr b a s := by
  have h := (Equiv.subLeft (-s)).sum_comp (fun y => b y*a (y+s))
  change (∑ x:G,b (-s-x)*a (-s-x+s))=_ at h
  have e (x:G) : -s-x+s= -x := by abel
  change (∑ x:G, a (-x)*b (-(x+s)))=∑ x:G,b x*a (x+s)
  rw [←h]
  apply Finset.sum_congr rfl
  intro j _
  change a (-j)*b (-(j+s))=b (-s-j)*a (-s-j+s)
  rw [e]
  have d : -(j+s)= -s-j := by abel
  rw [d,mul_comm]

private theorem plusL (a b c : Seq m G) (s:G) :
    cyclicCorr (a+b) c s=cyclicCorr a c s+cyclicCorr b c s := by simp [cyclicCorr,add_mul,sum_add_distrib]
private theorem plusR (a b c : Seq m G) (s:G) :
    cyclicCorr a (b+c) s=cyclicCorr a b s+cyclicCorr a c s := by simp [cyclicCorr,mul_add,sum_add_distrib]
private theorem minusL (a b c : Seq m G) (s:G) :
    cyclicCorr (a-b) c s=cyclicCorr a c s-cyclicCorr b c s := by simp [cyclicCorr,sub_mul,sum_sub_distrib]
private theorem minusR (a b c : Seq m G) (s:G) :
    cyclicCorr a (b-c) s=cyclicCorr a b s-cyclicCorr a c s := by simp [cyclicCorr,mul_sub,sum_sub_distrib]

def multiply (odd : (2:ℕ).Coprime m) (A : Pair m G) (B : Pair m K) : Pair m (G×K) := by
  classical
  let p : Seq m G := fun i => if A.a i=A.b i then A.a i else 0
  let q : Seq m G := fun i => if A.a i=A.b i then 0 else A.a i
  let x := tensor p B.a+tensor q B.b
  let y := tensor (rev p) B.b-tensor (rev q) B.a
  have aeq : p+q=A.a := by
    funext i
    by_cases e : A.a i=A.b i <;> simp [p,q,e]
  have beq : p-q=A.b := by
    funext i
    by_cases eq : A.a i=A.b i
    · simp [p,q,eq]
    · have opp : A.b i= -A.a i := by
        rcases A.pos i with hp|hp <;> rcases A.neg i with hq|hq
        · exact (eq (hp.trans hq.symm)).elim
        · rw [hp,hq]
        · rw [hp,hq,neg_neg]
        · exact (eq (hp.trans hq.symm)).elim
      simpa only [Pi.sub_apply,p,q,if_neg eq,zero_sub] using opp.symm
  have hneg {z : ZMod m} (h : Sign z) : Sign (-z) := by rcases h with h|h <;> simp [h,Sign]
  refine ⟨x,y,?_,?_,?_⟩
  · rintro ⟨i,j⟩
    by_cases e : A.a i=A.b i
    · simpa [x,p,q,tensor,e] using sign_mul (A.pos i) (B.pos j)
    · simpa [x,p,q,tensor,e] using sign_mul (A.pos i) (B.neg j)
  · rintro ⟨i,j⟩
    by_cases e : A.a (-i)=A.b (-i)
    · simpa [y,p,q,rev,tensor,e] using sign_mul (A.pos (-i)) (B.neg j)
    · simpa [y,p,q,rev,tensor,e] using hneg (sign_mul (A.pos (-i)) (B.pos j))
  · rintro ⟨s,t⟩ nz
    have identity : cyclicCorr x x (s,t)+cyclicCorr y y (s,t)=
        (cyclicCorr p p s+cyclicCorr q q s)*(cyclicCorr B.a B.a t+cyclicCorr B.b B.b t) := by
      simp only [x,y,plusL,plusR,minusL,minusR,corr_tensor,corr_rev]
      ring
    rw [identity]
    by_cases t0 : t=0
    · have s0 : s≠0 := fun e => nz (Prod.ext e t0)
      have z := A.off s s0
      rw [←aeq,←beq] at z
      simp only [plusL,plusR,minusL,minusR] at z
      have unit : IsUnit (2 : ZMod m) := by simpa using (ZMod.isUnit_iff_coprime 2 m).mpr odd
      have two : 2*(cyclicCorr p p s+cyclicCorr q q s)=0 := by linear_combination z
      rw [(unit.mul_right_eq_zero).mp two,zero_mul]
    · rw [B.off _ t0,mul_zero]

theorem mul_length {a b:ℕ} (odd : (2:ℕ).Coprime m) (h : HasLength m a) (k : HasLength m b) :
    HasLength m (a*b) := by
  obtain ⟨G,f,g,card,⟨A⟩⟩ := h
  obtain ⟨K,f',g',card',⟨B⟩⟩ := k
  letI := f
  letI := g
  letI := f'
  letI := g'
  exact ⟨G×K,inferInstance,inferInstance,by simp [card,card'],⟨multiply odd A B⟩⟩

#print axioms mul_length
end HadamardMod.Periodic
