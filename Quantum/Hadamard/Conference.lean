import Quantum.Hadamard.Paley

/-! A conference matrix joins row-balanced sign blocks to produce a modular
Hadamard matrix. Paley's conference construction supplies an even outer order. -/
noncomputable section
namespace HadamardMod
open Finset
variable {m : ℕ} {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]

structure Conference (m : ℕ) (I : Type*) [Fintype I] where
  entry : RowMatrix m I
  diag : ∀ i, entry i i=0
  sign : ∀ i j, i≠j → Sign (entry i j)
  off : ∀ i k, i≠k → ∑ j, entry i j*entry k j=0

private def conferenceBlock (C : Conference m I) (A : RowMatrix m J) (i j : I×J) : ZMod m :=
  C.entry i.1 j.1 + if i.1=j.1 then A i.2 j.2 else 0

theorem conference_block_good (C : Conference m I) (A : RowMatrix m J)
    (sign : ∀ i j, Sign (A i j)) (zero : ∀ i, ∑ j, A i j=0)
    (off : ∀ i k, i≠k → ∑ j, A i j*A k j =
      -((Fintype.card I:ZMod m)-1)*(Fintype.card J:ZMod m)) :
    Good (conferenceBlock C A) := by
  constructor
  · rintro ⟨i,a⟩ ⟨j,b⟩
    by_cases e : i=j
    · subst j; simpa [conferenceBlock,C.diag] using sign a b
    · simpa [conferenceBlock,e] using C.sign i j e
  · rintro ⟨i,a⟩ ⟨k,b⟩ ne
    rw [Fintype.sum_prod_type]
    have expand (j : I) (u : J) :
        conferenceBlock C A (i,a) (j,u)*conferenceBlock C A (k,b) (j,u) =
        C.entry i j*C.entry k j +
        (if k=j then C.entry i k*A b u else 0)+
        (if i=j then C.entry k i*A a u else 0)+
        (if i=k ∧ i=j then A a u*A b u else 0) := by
      dsimp [conferenceBlock]
      by_cases h : i=j <;> by_cases e : k=j
      · subst j; subst k; simp; ring
      · subst j; simp [e,Ne.symm e];ring
      · subst j; simp [h,Ne.symm h];ring
      · simp [h,e]
    let v : ZMod m := Fintype.card J
    have inner (j : I) :
        (∑ u : J, conferenceBlock C A (i,a) (j,u)*conferenceBlock C A (k,b) (j,u)) =
          v*(C.entry i j*C.entry k j) + (if i=j then
            (if i=k then ∑ u,A a u*A b u else 0) else 0) := by
      simp only [expand,Finset.sum_add_distrib,Finset.sum_ite_irrel,Finset.sum_const_zero,
        ←Finset.mul_sum,zero,mul_zero,ite_self,add_zero,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      by_cases h : i=j <;> by_cases e : i=k <;> simp [h,e,v] <;> ring
    simp only [inner,Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    by_cases e : i=k
    · subst k
      have nd : a≠b := fun eq => ne (Prod.ext rfl eq)
      have sq (j : I) : C.entry i j*C.entry i j=1-(if i=j then 1 else 0) := by
        by_cases ij : i=j
        · subst j; simp [C.diag]
        · simp [ij,sign_sq (C.sign _ _ ij)]
      simp [sq,Finset.sum_sub_distrib,off a b nd,v]
      ring
    · simp [e,C.off _ _ e]

private def paleyConfEntry (m s : ℕ) [Fact s.Prime] : RowMatrix m (Option (ZMod s))
  | none,none => 0
  | some _,none | none,some _ => 1
  | some i,some j => (Hadamard.Paley.Q s i j:ZMod m)

def paleyConference (m s : ℕ) [Fact s.Prime] (odd : s≠2) : Conference m (Option (ZMod s)) where
  entry := paleyConfEntry m s
  diag i := by cases i <;> simp [paleyConfEntry]
  sign := by
    intro i k ne
    cases i <;> cases k
    · exact (ne rfl).elim
    · exact Or.inl rfl
    · exact Or.inl rfl
    · rename_i i k
      rcases Hadamard.Paley.Q_sign_of_ne s (fun e : i=k => ne (congrArg some e)) with h|h <;>
        simp [paleyConfEntry,h,Sign]
  off := by
    have hc : ringChar (ZMod s)≠2 := by simpa only [ZMod.ringChar_zmod_n] using odd
    have row (i : ZMod s) : ∑ j, (Hadamard.Paley.Q s i j:ZMod m)=0 := by
      have raw : ∑ j, Hadamard.Paley.Q s i j=0 := by
        calc
          _ = ∑ z : ZMod s,quadraticChar (ZMod s) z :=
            Fintype.sum_equiv (Equiv.addRight (-i)) _ _ (fun j => by simp [Hadamard.Paley.Q,sub_eq_add_neg])
          _ = 0 := quadraticChar_sum_zero hc
      simpa only [Int.cast_sum,Int.cast_zero] using congrArg (fun z:ℤ => (z:ZMod m)) raw
    have dot (i k : ZMod s) (ne : i≠k) :
        (∑ j, (Hadamard.Paley.Q s i j:ZMod m)*(Hadamard.Paley.Q s k j:ZMod m))= -1 := by
      have raw : (∑ j, Hadamard.Paley.Q s i j*Hadamard.Paley.Q s k j)= -1 := by
        calc
          _ = ∑ z : ZMod s,quadraticChar (ZMod s) z*quadraticChar (ZMod s) (z+(i-k)) := by
            apply Fintype.sum_equiv (Equiv.addRight (-i))
            intro j
            change _ = quadraticChar (ZMod s) (j+ -i)*quadraticChar (ZMod s) (j+ -i+(i-k))
            rw [show j+ -i+(i-k)=j-k by abel]
            simp [Hadamard.Paley.Q,sub_eq_add_neg]
          _ = -1 := by simpa [sub_ne_zero.mpr ne] using Hadamard.Paley.character_corr hc (i-k)
      simpa only [Int.cast_sum,Int.cast_mul,Int.cast_neg,Int.cast_one] using congrArg (fun z:ℤ => (z:ZMod m)) raw
    intro i k ne
    cases i <;> cases k
    · exact (ne rfl).elim
    · rename_i k
      simp [Fintype.sum_option,paleyConfEntry,row]
    · rename_i i
      simp [Fintype.sum_option,paleyConfEntry,row]
    · rename_i i k
      have nd : i≠k := fun e => ne (congrArg some e)
      simp [Fintype.sum_option,paleyConfEntry,dot i k nd]

theorem conference_join {s v : ℕ} [Fact s.Prime] (odd : s≠2)
    (A : RowMatrix m (Fin v)) (sign : ∀ i j, Sign (A i j)) (zero : ∀ i, ∑ j, A i j=0)
    (off : ∀ i k, i≠k → ∑ j, A i j*A k j = -(s:ZMod m)*(v:ZMod m)) :
    AtOrder m ((s+1)*v) := by
  apply of_card (conference_block_good (paleyConference m s odd) A sign zero _) (by simp)
  simpa using off

#print axioms conference_join
end HadamardMod
