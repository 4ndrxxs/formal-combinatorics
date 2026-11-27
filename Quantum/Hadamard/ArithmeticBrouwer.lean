import Quantum.Hadamard.ArithmeticBrouwerFrame
import Quantum.Hadamard.ArithmeticOneStep

/-! Brouwer's signed incidence array. Geometry and the small Hadamard
frame are combined over the integers before reduction modulo an arbitrary
modulus. -/
noncomputable section
namespace Hadamard.Brouwer
open Finset Hadamard.PG HadamardMod
variable {q n : ℕ} [Fact q.Prime] {E P T V : Type}
  [Fintype E] [Fintype P] [Fintype T] [Fintype V]

def bottom (G : Geometry q n E P) (F : Frame q T V) (j:P) (t:T) (i:P) (v:V) : ℤ :=
  G.weight i j*F.bot t v-G.zero i j

def array (G : Geometry q n E P) (F : Frame q T V) : Option (P×T) → (E ⊕ P×V) → ℤ
  | none, .inl _ => 1
  | none, .inr _ => -1
  | some (j,t), .inl x => F.top t (G.value j x)
  | some (j,t), .inr (i,v) => bottom G F j t i v

private theorem botrow (G : Geometry q n E P) (F : Frame q T V) (j:P) (t:T) :
    (∑ i:P×V,bottom G F j t i.1 i.2)= -(q+1:ℤ)*(geom q (n+1):ℤ) := by
  rw [Fintype.sum_prod_type]
  simp only [bottom,sum_sub_distrib,← mul_sum,F.botRow,mul_zero,zero_sub,sum_const,card_univ,
    F.cardV,nsmul_eq_mul,sum_neg_distrib,G.zerosum,Nat.cast_add,Nat.cast_one]
  ring

private theorem botdot (G : Geometry q n E P) (F : Frame q T V) (j k:P) (t s:T) :
    (∑ i:P×V,bottom G F j t i.1 i.2*bottom G F k s i.1 i.2)=
      (∑ i,G.weight i j*G.weight i k)*(∑ v,F.bot t v*F.bot s v)+
        (q+1:ℤ)*(∑ i,G.zero i j*G.zero i k) := by
  rw [Fintype.sum_prod_type]
  have term (i:P) (v:V) :
      bottom G F j t i v*bottom G F k s i v=
        (G.weight i j*G.weight i k)*(F.bot t v*F.bot s v)-
        (G.weight i j*G.zero i k)*F.bot t v-
        (G.zero i j*G.weight i k)*F.bot s v+G.zero i j*G.zero i k := by
    dsimp [bottom]; ring
  simp only [term,sum_add_distrib,sum_sub_distrib,← mul_sum,F.botRow,mul_zero,sub_zero,
    sum_const,card_univ,F.cardV,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,← sum_mul]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  ring

private theorem weightnorm (G : Geometry q n E P) (j:P) :
    (∑ i,G.weight i j*G.weight i j)=(q:ℤ)^(n+1) := by
  have eq (i:P) : G.weight i j*G.weight i j=1-G.zero i j := by
    rcases G.values i j with ⟨w,z⟩|⟨w,z⟩
    · simp [w,z]
    · rcases w with w|w <;> simp [w,z]
  simp only [eq,sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,mul_one,G.cardP,G.zerosum,
    show n+2=n+1+1 by omega,geom_succ_last q (n+1),Nat.cast_add,Nat.cast_pow]
  ring

private theorem zeronorm (G : Geometry q n E P) (j:P) :
    (∑ i,G.zero i j*G.zero i j)=(geom q (n+1):ℤ) := by
  have eq (i:P) : G.zero i j*G.zero i j=G.zero i j := by
    rcases G.values i j with ⟨_,z⟩|⟨_,z⟩ <;> simp [z]
  simpa only [eq] using G.zerosum j

private theorem array_sign (G : Geometry q n E P) (F : Frame q T V) (i j) : Sign (array G F i j) := by
  cases i with
  | none => cases j <;> simp [array,Sign]
  | some t =>
    obtain ⟨a,t⟩ := t
    cases j with
    | inl x => exact F.topSign _ _
    | inr u =>
      obtain ⟨k,v⟩ := u
      rcases G.values k a with ⟨w,z⟩|⟨w,z⟩
      · simp [array,bottom,w,z,Sign]
      · simpa [array,bottom,z] using sign_mul w (F.botSign _ _)

private theorem array_row (G : Geometry q n E P) (F : Frame q T V) (i) :
    (∑ j,array G F i j)=1-2*(geom q (n+2):ℤ) := by
  have eq := geom_int q (n+2)
  cases i with
  | none =>
    rw [Fintype.sum_sum_type]
    simp only [array,sum_const,card_univ,nsmul_eq_mul,mul_one,Fintype.card_prod,G.cardE,G.cardP,
      F.cardV,Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_pow,mul_neg]
    linear_combination -eq
  | some t =>
    obtain ⟨j,t⟩ := t
    rw [Fintype.sum_sum_type]
    change (∑ x:E,F.top t (G.value j x))+(∑ i:P×V,bottom G F j t i.1 i.2)=_
    rw [G.oneform,F.topRow,botrow]
    have step : (geom q (n+2):ℤ)=(geom q (n+1):ℤ)+(q:ℤ)^(n+1) := by
      rw [show n+2=n+1+1 by omega,geom_succ_last]; push_cast; rfl
    rw [show n+2=n+1+1 by omega,pow_succ] at eq
    linear_combination (q+1)*step-eq

private theorem first_dot (G : Geometry q n E P) (F : Frame q T V) (k:P) (s:T) :
    (∑ j,array G F none j*array G F (some (k,s)) j)=
      -(q:ℤ)^(n+1)+(q+1:ℤ)*(geom q (n+1):ℤ) := by
  rw [Fintype.sum_sum_type]
  simp only [array,one_mul,neg_one_mul,sum_neg_distrib,G.oneform,F.topRow,botrow]
  ring

private theorem array_dot (G : Geometry q n E P) (F : Frame q T V) (i k) (ne:i≠k) :
    (∑ j,array G F i j*array G F k j)=1+2*q*(geom q (n+2):ℤ)-2*(q+1:ℤ)*q^(n+1) := by
  have eq := geom_int q (n+2)
  have step : (geom q (n+2):ℤ)=(geom q (n+1):ℤ)+(q:ℤ)^(n+1) := by
    rw [show n+2=n+1+1 by omega,geom_succ_last]; push_cast; rfl
  have num : -(q:ℤ)^(n+1)+(q+1:ℤ)*(geom q (n+1):ℤ)=
       1+2*q*(geom q (n+2):ℤ)-2*(q+1:ℤ)*q^(n+1) := by
    rw [show n+2=n+1+1 by omega,pow_succ] at eq
    linear_combination -(q+1)*step-eq
  apply Eq.trans _ num
  cases i with
  | none =>
    cases k with
    | none => exact (ne rfl).elim
    | some z => exact first_dot G F z.1 z.2
  | some y =>
    cases k with
    | none =>
      simpa only [mul_comm] using first_dot G F y.1 y.2
    | some z =>
      obtain ⟨j,t⟩ := y
      obtain ⟨k,s⟩ := z
      rw [Fintype.sum_sum_type]
      change (∑ x:E,F.top t (G.value j x)*F.top s (G.value k x))+
        (∑ i:P×V,bottom G F j t i.1 i.2*bottom G F k s i.1 i.2)=_
      rw [botdot]
      by_cases h:j=k
      · subst k
        have ts : t≠s := fun H => ne (by rw [H])
        rw [weightnorm,zeronorm,G.oneform j (fun x => F.top t x*F.top s x)]
        linear_combination (q:ℤ)^(n+1)*F.joint t s ts
      · rw [G.weightpair j k h,G.zeropair j k h,G.twoform j k h,F.topRow,F.topRow,
          geom_succ_last q n,Nat.cast_add,Nat.cast_pow,pow_succ]
        ring

theorem extender_geometry {m : ℕ} (G : Geometry q n E P) (F : Frame q T V)
    (zero : 2*(geom q (n+2):ZMod m)=0) :
    Nonempty (Extender m (Fin (1+2*q*geom q (n+2))) (2*((q:ZMod m)+1)*q^(n+1))) := by
  classical
  have call : Fintype.card (Option (P×T))=1+2*q*geom q (n+2) := by
    rw [Fintype.card_option,Fintype.card_prod,F.cardT,G.cardP]; ring
  have catt : Fintype.card (E ⊕ P×V)=1+2*q*geom q (n+2) := by
    rw [Fintype.card_sum,Fintype.card_prod,F.cardV,G.cardE,G.cardP]
    have eq := geom_int q (n+2)
    zify
    linear_combination -eq
  let l := (Fintype.equivFinOfCardEq call).symm
  let r := (Fintype.equivFinOfCardEq catt).symm
  let H (i j : Fin (1+2*q*geom q (n+2))) : ZMod m := (array G F (l i) (r j):ℤ)
  refine ⟨{entry := H,sign := ?_,row := ?_,off := ?_,dim := ?_,pos := ?_}⟩
  · intro i j
    rcases array_sign G F (l i) (r j) with h|h <;> simp [H,h,Sign]
  · intro i
    have row := congrArg (fun z:ℤ => (z:ZMod m)) (array_row G F (l i))
    push_cast at row
    rw [zero,sub_zero] at row
    exact (r.sum_comp (fun z => ((array G F (l i) z:ℤ):ZMod m))).trans row
  · intro i k ne
    have corr := congrArg (fun z:ℤ => (z:ZMod m)) (array_dot G F (l i) (l k) (fun h => ne (l.injective h)))
    push_cast at corr
    apply (r.sum_comp (fun z => ((array G F (l i) z:ℤ):ZMod m)*((array G F (l k) z:ℤ):ZMod m))).trans
    rw [corr]
    linear_combination (q:ZMod m)*zero
  · rw [Fintype.card_fin]
    push_cast
    linear_combination (q:ZMod m)*zero
  · simp

set_option maxHeartbeats 350000 in
/-- Kline's Brouwer step for any odd prime q congruent to three modulo
four. The single modulus condition is twice the geometric sum vanishing. -/
theorem extender {m q n : ℕ} [Fact q.Prime] (q4 : q%4=3)
    (zero : 2*(geom q (n+2):ZMod m)=0) :
    Nonempty (Extender m (Fin (1+2*q*geom q (n+2))) (2*((q:ZMod m)+1)*q^(n+1))) := by
  classical
  let E := GaloisField q (n+2)
  let : Fintype E := Fintype.ofFinite E
  let : DecidableEq E := Classical.decEq E
  have gx : Nonempty (Geometry q n E (Projective (ZMod q) E)) := geometry (q := q) (n := n) (E := E) q4
    (Algebra.trace (ZMod q) E) (Algebra.trace_ne_zero (ZMod q) E)
    (GaloisField.finrank q (show n+2≠0 by omega))
  obtain ⟨G⟩ := gx
  obtain ⟨F⟩ := frame q4
  exact extender_geometry G F zero

#print axioms extender
end Hadamard.Brouwer
