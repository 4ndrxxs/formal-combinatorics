import Quantum.Hadamard.ArithmeticSingularNecessity

/-! The row code of an integral Gram similitude of valuation v is
self-dual modulo p^v when the divided Gram matrix remains nonsingular
modulo p. This applies even for odd valuations greater than one. -/
noncomputable section
namespace HadamardMod
open Matrix

private theorem row_code_of_scaled {P n : ℕ} (hp : 1 < P)
    (A B : Matrix (Fin n) (Fin n) ℤ)
    (gram : A*A.transpose=(P:ℤ) • B) (bu : IsUnit (B.det:ZMod P)) :
    let D := A.map (fun t:ℤ => (t:ZMod P))
    D*D.transpose=0 ∧ ∀ x : Fin n → ZMod P, D *ᵥ x=0 ↔ ∃ y, D.transpose *ᵥ y=x := by
  classical
  let : Fact (1 < P) := ⟨hp⟩
  let : NeZero P := ⟨by omega⟩
  let D := A.map (fun t:ℤ => (t:ZMod P))
  change D*D.transpose=0 ∧ _
  have detB : B.det ≠ 0 := by rintro h; rw [h,Int.cast_zero] at bu; exact bu.ne_zero rfl
  have hdet := congrArg Matrix.det gram
  rw [Matrix.det_smul,Matrix.det_mul,Matrix.det_transpose,Fintype.card_fin] at hdet
  have detA : A.det≠0 := by
    rintro h
    rw [h,mul_zero] at hdet
    exact (mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (by omega:P≠0))) detB) hdet.symm
  have cast_dot (X : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
      (fun i => ((X *ᵥ x) i:ZMod P))=X.map (fun t:ℤ => (t:ZMod P)) *ᵥ (fun i => (x i:ZMod P)) := by
    funext i
    simp [Matrix.mulVec,dotProduct]
  have dg : D*D.transpose=0 := by
    ext i j
    have h := congrArg (fun G : Matrix (Fin n) (Fin n) ℤ => (G i j:ZMod P)) gram
    change (((A*A.transpose) i j:ℤ):ZMod P)=(((P:ℤ)*B i j:ℤ):ZMod P) at h
    simpa [D,Matrix.mul_apply] using h
  refine ⟨dg,?_⟩
  intro x
  constructor
  · intro dx
    let X (i:Fin n) : ℤ := (x i).val
    have ex : (fun i => (X i:ZMod P))=x := by funext i; simp [X]
    have ax : ∀ i, (P:ℤ)∣(A *ᵥ X) i := by
      intro i
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      have h := cast_dot A X
      rw [ex,show A.map (fun t:ℤ => (t:ZMod P))=D from rfl] at h
      exact (congrFun h i).trans (congrFun dx i)
    choose w hw using ax
    have eq : A *ᵥ X=(P:ℤ) • w := funext hw
    have exactVec : A.transpose *ᵥ (B.adjugate *ᵥ w)=B.det • X := by
      apply Matrix.mulVec_injective_of_det_ne_zero detA
      rw [Matrix.mulVec_mulVec,gram,Matrix.smul_mulVec,Matrix.mulVec_mulVec,Matrix.mul_adjugate,
        Matrix.smul_mulVec,Matrix.one_mulVec,Matrix.mulVec_smul,eq,smul_comm]
    let W := fun i => ((B.adjugate *ᵥ w) i:ZMod P)
    have modVec : D.transpose *ᵥ W=(B.det:ZMod P) • x := by
      calc
        D.transpose *ᵥ W = fun i => ((A.transpose *ᵥ (B.adjugate *ᵥ w)) i:ZMod P) :=
          (cast_dot A.transpose _).symm
        _ = (B.det:ZMod P) • x := by
          rw [exactVec,←ex]
          funext i
          simp [Pi.smul_apply]
    obtain ⟨a,ha⟩ := bu
    refine ⟨(a⁻¹: (ZMod P)ˣ) • W,?_⟩
    rw [Units.smul_def,Matrix.mulVec_smul,modVec,←ha,smul_smul]
    simp
  · rintro ⟨y,rfl⟩
    rw [Matrix.mulVec_mulVec,dg,Matrix.zero_mulVec]

theorem singular_self_dual {p v n u : ℕ} (pp:p.Prime) (vp:0 < v)
    (hn:n=p^v*u) (cu:u.Coprime p) (H:IntegralSolution (p^(v+1)) n) :
    ∃ D : Matrix (Fin n) (Fin n) (ZMod (p^v)), D*D.transpose=0 ∧
      ∀ x : Fin n → ZMod (p^v), D *ᵥ x=0 ↔ ∃ y, D.transpose *ᵥ y=x := by
  classical
  let : Fact p.Prime := ⟨pp⟩
  obtain ⟨A,_,gram⟩ := H
  choose K hK using gram
  let P := p^v
  let B : Matrix (Fin n) (Fin n) ℤ := fun i j => (if i=j then (u:ℤ) else 0)+(p:ℤ)*K i j
  have scale : A*A.transpose=(P:ℤ) • B := by
    ext i j
    change (A*A.transpose) i j=(P:ℤ)*B i j
    have h := hK i j
    have hu : (n:ℤ)=(P:ℤ)*u := by exact_mod_cast hn
    rw [pow_succ] at h
    change ((A*A.transpose) i j-(if i=j then (n:ℤ) else 0))=((P*p:ℕ):ℤ)*K i j at h
    by_cases eq : i=j
    · subst j; simp [B,hu] at h ⊢; linear_combination h
    · simp [B,eq] at h ⊢; linear_combination h
  have rd : B.map (fun x : ℤ => (x:ZMod p)) =
      (u:ZMod p) • (1:Matrix (Fin n) (Fin n) (ZMod p)) := by
    ext i j
    change ((B i j:ℤ):ZMod p)=(u:ZMod p)*(1:Matrix (Fin n) (Fin n) (ZMod p)) i j
    by_cases eq:i=j
    · subst j; simp [B]
    · simp [B,Matrix.one_apply_ne eq,eq]
  have db : (B.det:ZMod p)=(u:ZMod p)^n := by rw [Int.cast_det,rd,Matrix.det_smul]; simp
  have dbu : IsUnit (B.det:ZMod p) := by rw [db]; exact ((ZMod.isUnit_iff_coprime _ _).mpr cu).pow _
  have bcp := (ZMod.isUnit_intCast_iff_isCoprime B.det p).mp dbu
  have fu : IsUnit (B.det:ZMod P) :=
    (ZMod.isUnit_intCast_iff_isCoprime _ _).mpr (by
      change IsCoprime ((p^v:ℕ):ℤ) B.det
      rw [Nat.cast_pow]; exact bcp.pow_left)
  exact ⟨A.map (fun t:ℤ => (t:ZMod P)),
    row_code_of_scaled (one_lt_pow₀ pp.one_lt vp.ne') A B scale fu⟩

#print axioms singular_self_dual
end HadamardMod
