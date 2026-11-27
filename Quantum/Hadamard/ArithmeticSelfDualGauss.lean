import Quantum.Hadamard.ArithmeticSelfDual

/-! A self-dual row code forces the standard quadratic Gauss sum raised
to its length to be a positive integer. All sums here are finite. -/
noncomputable section
namespace HadamardMod
open Matrix Finset

private theorem char_sum {R:Type*} [AddCommMonoid R] (ψ:AddChar R ℂ)
    {I:Type*} (s:Finset I) (f:I→R) : ψ (∑ i∈s,f i)=∏i∈s,ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [ha,ψ.map_add_eq_mul,ih]

theorem code_gauss {P n : ℕ} [NeZero P] (two : IsUnit (2:ZMod P))
    (D : Matrix (Fin n) (Fin n) (ZMod P)) (dg : D*D.transpose=0)
    (ker : ∀ x : Fin n → ZMod P, D *ᵥ x=0 ↔ ∃ y, D.transpose *ᵥ y=x)
    (ψ:AddChar (ZMod P) ℂ) (prim:ψ.IsPrimitive) :
    ∃ k : ℕ, 0 < k ∧ (∑ a:ZMod P,ψ (a*a))^n=(k:ℂ) := by
  classical
  let V := Fin n → ZMod P
  let C := univ.filter (fun x:V => D *ᵥ x=0)
  have pos : 0 < C.card := Finset.card_pos.mpr ⟨0,by simp [C]⟩
  let N := Fintype.card V
  let G := ∑ a:ZMod P,ψ (a*a)
  have inc (y:V) : (D.transpose *ᵥ y) ⬝ᵥ (D.transpose *ᵥ y)=0 := by
    rw [Matrix.dotProduct_transpose_mulVec,Matrix.mulVec_mulVec,dg,Matrix.zero_mulVec,dotProduct_zero]
  have expand (x y:V) :
      (x+D.transpose *ᵥ y) ⬝ᵥ (x+D.transpose *ᵥ y)=x ⬝ᵥ x+y ⬝ᵥ ((2:ZMod P) • (D *ᵥ x)) := by
    rw [add_dotProduct,dotProduct_add,dotProduct_add,inc,add_zero,
      dotProduct_comm (D.transpose *ᵥ y) x,Matrix.dotProduct_transpose_mulVec]
    rw [dotProduct_smul,smul_eq_mul]
    ring
  have inner (x:V) : (∑ y:V, ψ (y ⬝ᵥ ((2:ZMod P) • (D *ᵥ x)))) =
      if D *ᵥ x=0 then (N:ℂ) else 0 := by
    change (∑ y:V, ψ (∑ i, y i*((2:ZMod P) • (D *ᵥ x)) i))=_
    simp_rw [char_sum]
    rw [←Fintype.prod_sum (fun (i:Fin n) (t:ZMod P) => ψ (t*(((2:ZMod P) • (D *ᵥ x)) i)))]
    simp_rw [AddChar.sum_mulShift _ prim]
    by_cases h:D *ᵥ x=0
    · simp [h,N,V]
    · obtain ⟨i,hi⟩ : ∃i, (D *ᵥ x) i≠0 := by contrapose! h; exact funext h
      rw [ite_eq_right h]
      apply Finset.prod_eq_zero (mem_univ i)
      have ne : ((2:ZMod P) • (D *ᵥ x)) i ≠ 0 := by
        simp only [Pi.smul_apply,smul_eq_mul]
        exact fun hn => hi (two.mul_right_inj.mp (hn.trans (mul_zero 2).symm))
      simp only [ite_eq_right ne,Nat.cast_zero]
  have total : (∑ x:V,ψ (x ⬝ᵥ x))=G^n := by
    change (∑ x:V,ψ (∑ i,x i*x i))=G^n
    simp_rw [char_sum]
    exact (Fintype.sum_pow (fun t:ZMod P => ψ (t*t)) n).symm
  have shift (y:V) : (∑ x:V,ψ ((x+D.transpose *ᵥ y) ⬝ᵥ (x+D.transpose *ᵥ y)))=G^n :=
    (Equiv.sum_comp (Equiv.addRight (D.transpose *ᵥ y)) (fun x:V => ψ (x ⬝ᵥ x))).trans total
  have zero_char (x:V) (hx : D *ᵥ x=0) : ψ (x ⬝ᵥ x)=1 := by
    obtain ⟨y,rfl⟩ := (ker x).mp hx
    rw [inc,ψ.map_zero_eq_one]
  have val (x:V) : ψ (x ⬝ᵥ x)*(if D *ᵥ x=0 then (N:ℂ) else 0)=
      (if D *ᵥ x=0 then (1:ℂ) else 0)*N := by
    by_cases hx:D *ᵥ x=0 <;> simp [hx,zero_char]
  have full : (N:ℂ)*G^n=C.card*N := by
    calc
      (N:ℂ)*G^n = ∑ y:V,∑ x:V,ψ ((x+D.transpose *ᵥ y) ⬝ᵥ (x+D.transpose *ᵥ y)) := by
        simp only [shift,sum_const,card_univ,nsmul_eq_mul,N]
      _ = ∑ x:V, ψ (x ⬝ᵥ x)*(∑ y:V,ψ (y ⬝ᵥ ((2:ZMod P) • (D *ᵥ x)))) := by
        rw [sum_comm]
        simp only [expand,ψ.map_add_eq_mul,Finset.mul_sum]
      _ = ∑ x:V,(if D *ᵥ x=0 then (1:ℂ) else 0)*N := by simp only [inner,val]
      _ = C.card*N := by rw [←Finset.sum_mul]; simp [C,Finset.sum_boole]
  refine ⟨C.card,pos,?_⟩
  apply mul_left_cancel₀ (show (N:ℂ) ≠ 0 by exact_mod_cast (Fintype.card_pos (α:=V)).ne')
  simpa [mul_comm (C.card:ℂ) (N:ℂ)] using full

#print axioms code_gauss
end HadamardMod
