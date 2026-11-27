module
public import Quantum.DiagonalSixSectors

/-! A diagonal quantum Latin square of order six must repeat a projective state. -/
@[expose] public section
noncomputable section
namespace DiagonalSix
open Complex Matrix Finset QuantumCertificate
open scoped Matrix BigOperators

theorem compression (v : Space 6) (H : M) : ∃ z : ℂ, proj v*H*proj v=z • proj v := by
  unfold proj
  rw [Matrix.vecMulVec_mul,Matrix.vecMulVec_mul_vecMulVec,Matrix.vecMulVec_smul]
  exact ⟨_,rfl⟩

namespace Model
variable (g : Model)

theorem Xidem (i : Tri) : g.X i*g.X i=g.X i := by
  calc
    _ = (1-g.P i)*g.X i := rfl
    _ = _ := by rw [sub_mul,one_mul,g.PX,sub_zero]

theorem binary (r c : Idx) (k : Tri) : g.p r c*g.X k=0 ∨ g.p r c*g.X k=g.p r c := by
  obtain ⟨v,hv⟩ := g.rankOne r c
  obtain ⟨z,hz⟩ := compression v (g.X k)
  rw [← hv] at hz
  have h : g.p r c*g.X k=z • g.p r c := by
    rw [mul_assoc,← g.commutes,← mul_assoc,g.idem] at hz
    exact hz
  have sq : (z*z) • g.p r c=z • g.p r c := by
    calc
      _ = z • (g.p r c*g.X k) := by rw [h,mul_smul]
      _ = (z • g.p r c)*g.X k := (smul_mul_assoc _ _ _).symm
      _ = (g.p r c*g.X k)*g.X k := by rw [h]
      _ = _ := by rw [mul_assoc,g.Xidem,h]
  have sc := congrArg Matrix.trace sq
  simp only [Matrix.trace_smul,g.trace,smul_eq_mul,mul_one] at sc
  have dis : z=0 ∨ z=1 := by
    have : z*(z-1)=0 := by linear_combination sc
    simpa only [sub_eq_zero] using mul_eq_zero.mp this
  rcases dis with he | he <;> simp [h,he]

/-- In a row, column, or either diagonal a rank-two sector contains precisely
two rank-one states. Their projectors add up to that sector. -/
theorem slice_of_coverage {α : Type} [Fintype α] {f : α → M} (k : Tri)
    (hf : (∑ i, f i)*g.X k=g.X k) (ht : ∀ i, (f i).trace=1)
    (hd : ∀ i, f i*g.X k=0 ∨ f i*g.X k=f i) :
    ∃ a b : α, a≠b ∧ f a+f b=g.X k ∧ (∀ c, f c*g.X k=f c ↔ c=a ∨ c=b) := by
  classical
  let s := Finset.univ.filter (fun i => f i*g.X k=f i)
  have eq : ∑ i ∈ s, f i=g.X k := by
    calc
      _ = ∑ i, f i*g.X k := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : f i*g.X k=f i
        · simp [h]
        · rw [if_neg h,(hd i).resolve_right h]
      _ = _ := by rw [← Finset.sum_mul,hf]
  have tr := congrArg Matrix.trace eq
  simp only [Matrix.trace_sum,ht,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,g.Xtrace] at tr
  have hc : s.card=2 := by exact_mod_cast tr
  obtain ⟨a,b,hab,hs⟩ := Finset.card_eq_two.mp hc
  refine ⟨a,b,hab,?_,?_⟩
  · simpa [hs,hab] using eq
  · intro c
    have h : f c*g.X k=f c ↔ c∈s := by simp [s]
    simp [h,hs]

theorem slice {f : Idx → M} (hf : ∑ i, f i=1) (ht : ∀ i, (f i).trace=1)
    (k : Tri) (hd : ∀ i, f i*g.X k=0 ∨ f i*g.X k=f i) :
    ∃ a b : Idx, a≠b ∧ f a+f b=g.X k ∧ (∀ c, f c*g.X k=f c ↔ c=a ∨ c=b) :=
  g.slice_of_coverage k (by rw [hf,one_mul]) ht hd

theorem repeat_projector : ∃ r s c d : Idx, r≠s ∧ c≠d ∧ g.p r c=g.p s d := by
  let r : Idx := (0,0)
  obtain ⟨c,d,hcd,sumR,memR⟩ := g.slice (g.row r) (g.trace r) 0 (fun j => g.binary r j 0)
  obtain ⟨u,v,huv,sumC,memC⟩ := g.slice (g.col d) (fun i => g.trace i d) 0
    (fun i => g.binary i d 0)
  have mem := (memC r).mp ((memR d).mpr (Or.inr rfl))
  rcases mem with h | h
  · subst u
    refine ⟨r,v,c,d,huv,hcd,?_⟩
    have q := sumR.trans sumC.symm
    linear_combination (norm := abel) q
  · subst v
    refine ⟨r,u,c,d,huv.symm,hcd,?_⟩
    exact add_right_cancel (sumR.trans sumC.symm)
end Model

theorem same_ray {v w : Space 6} (nv : v≠0) (nw : w≠0) (tr : (proj v).trace=1)
    (h : proj v=proj w) : Projectivization.mk ℂ v nv=Projectivization.mk ℂ w nw := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  have norm : inner ℂ v v=1 := by
    rw [proj,Matrix.trace_vecMulVec,dotProduct_comm,ip_inner] at tr
    exact tr
  have hv := congrArg (fun m : M => m *ᵥ (⇑v : V)) h
  simp only [proj,Matrix.vecMulVec_mulVec,ip_inner,norm,op_smul_eq_smul,one_smul] at hv
  exact ⟨inner ℂ w v,by ext i; exact (congrFun hv i).symm⟩

/-- Huang and Li's maximality condition means 36 pairwise distinct complex rays. -/
theorem not_maximal : ¬MaximalDiagonal 6 := by
  rintro ⟨a,main,anti⟩
  let g := toModel a.entry a.rows a.cols main anti
  obtain ⟨r,s,c,d,hrs,_,e⟩ := g.repeat_projector
  have rays := same_ray (a.nz (ord r,ord c)) (a.nz (ord s,ord d)) (g.trace r c) e
  exact hrs (ord.injective (congrArg Prod.fst (a.distinct rays)))

#print axioms not_maximal
end DiagonalSix
