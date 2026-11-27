import Quantum.Hadamard.Basic

/-! The Goethals–Seidel sign array over a finite abelian group, over any
modulus including zero. The construction uses forward and reversed translates
of four sequences. It reduces every nontrivial Gram entry to either one
complementary autocorrelation or two cancellation identities. -/
namespace HadamardMod
open Finset
variable {I : Type*} [Fintype I] [AddCommGroup I] {m : ℕ}
abbrev Seq (m : ℕ) (I : Type*) := I → ZMod m

def cyclicCorr (f g : Seq m I) (s : I) : ZMod m := ∑ j, f j * g (j+s)
private def conv (f g : Seq m I) (s : I) : ZMod m := ∑ j, f j * g (s-j)
private def dot (f g : Seq m I) : ZMod m := ∑ j, f j * g j
private def tr (f : Seq m I) (u : I) : Seq m I := fun j => f (j+u)
private def rev (f : Seq m I) (u : I) : Seq m I := fun j => f (u-j)

private theorem addRight_at (a t : I) : Equiv.addRight a t = t+a := rfl

private theorem corr_swap (f g : Seq m I) (s : I) :
    cyclicCorr f g s=cyclicCorr g f (-s) := by
  have h := Equiv.sum_comp (Equiv.addRight s) (fun j => g j*f (j+ -s))
  simpa [cyclicCorr, addRight_at, mul_comm] using h

private theorem conv_swap (f g : Seq m I) (s : I) :
    conv f g s=conv g f s := by
  have h := (Equiv.subLeft s).sum_comp (fun j => g j*f (s-j))
  simpa [conv, Equiv.subLeft_apply, mul_comm] using h

private theorem dot_tt (f g : Seq m I) (u v : I) :
    dot (tr f u) (tr g v)=cyclicCorr f g (v-u) := by
  have h := Equiv.sum_comp (Equiv.addRight u) (fun j => f j*g (j+(v-u)))
  unfold dot cyclicCorr
  refine Eq.trans (Finset.sum_congr rfl ?_) h
  intro j _
  simp only [tr,addRight_at,Equiv.subLeft_apply]
  congr 2 <;> abel

private theorem dot_rr (f g : Seq m I) (u v : I) :
    dot (rev f u) (rev g v)=cyclicCorr f g (v-u) := by
  have h := Equiv.sum_comp (Equiv.subLeft u) (fun j => f j*g (j+(v-u)))
  unfold dot cyclicCorr
  refine Eq.trans (Finset.sum_congr rfl ?_) h
  intro j _
  simp only [rev,addRight_at,Equiv.subLeft_apply]
  congr 2 <;> abel

private theorem dot_tr (f g : Seq m I) (u v : I) :
    dot (tr f u) (rev g v)=conv f g (u+v) := by
  have h := Equiv.sum_comp (Equiv.addRight u) (fun j => f j*g (u+v-j))
  unfold dot conv
  refine Eq.trans (Finset.sum_congr rfl ?_) h
  intro j _
  simp only [tr,rev,addRight_at,Equiv.subLeft_apply]
  congr 2 <;> abel

private theorem dot_rt (f g : Seq m I) (u v : I) :
    dot (rev f u) (tr g v)=conv f g (u+v) := by
  have h := Equiv.sum_comp (Equiv.subLeft u) (fun j => f j*g (u+v-j))
  unfold dot conv
  refine Eq.trans (Finset.sum_congr rfl ?_) h
  intro j _
  simp only [tr,rev,addRight_at,Equiv.subLeft_apply]
  congr 2 <;> abel

omit [AddCommGroup I] in
private theorem dot_neg_l (f g : Seq m I) : dot (-f) g= -dot f g := by simp [dot]
omit [AddCommGroup I] in
private theorem dot_neg_r (f g : Seq m I) : dot f (-g)= -dot f g := by simp [dot]

private def block (f : Fin 4 → Seq m I) (u v : Fin 4) (x : I) : Seq m I :=
  ![![tr (f 0) (-x),rev (f 1) (-x),rev (f 2) (-x),rev (f 3) (-x)],
    ![-rev (f 1) (-x),tr (f 0) (-x),-tr (f 3) x,tr (f 2) x],
    ![-rev (f 2) (-x),tr (f 3) x,tr (f 0) (-x),-tr (f 1) x],
    ![-rev (f 3) (-x),-tr (f 2) x,tr (f 1) x,tr (f 0) (-x)]] u v

private theorem neg_sign {z : ZMod m} (h : Sign z) : Sign (-z) := by
  rcases h with h|h <;> simp [h,Sign]

omit [Fintype I] in
private theorem block_sign (f : Fin 4 → Seq m I) (hf : ∀ t z, Sign (f t z))
    (u v : Fin 4) (x y : I) : Sign (block f u v x y) := by
  fin_cases u <;> fin_cases v <;> simp [block,tr,rev] <;> first | apply hf | apply neg_sign; apply hf

private theorem row_gram (f : Fin 4 → Seq m I) (u v : Fin 4) (x y : I) :
    (∑ t, dot (block f u t x) (block f v t y)) =
    if u=v then ∑ t, cyclicCorr (f t) (f t) (x-y) else 0 := by
  have sw (i j : Fin 4) (z : I) := corr_swap (f i) (f j) z
  have cv (i j : Fin 4) (z : I) := conv_swap (f i) (f j) z
  have self (i : Fin 4) : cyclicCorr (f i) (f i) (y-x)=cyclicCorr (f i) (f i) (x-y) := by
    simpa using sw i i (y-x)
  fin_cases u <;> fin_cases v <;> simp [Fin.sum_univ_four,block,dot_neg_l,dot_neg_r,
    dot_tt,dot_rr,dot_tr,dot_rt,self] <;>
    (try simp only [cv 1 0,cv 2 0,cv 2 1,cv 3 0,cv 3 1,cv 3 2,
      sw 1 0,sw 2 0,sw 2 1,sw 3 0,sw 3 1,sw 3 2,neg_add_rev,neg_neg,neg_sub]) <;> abel

/-- Four complementary sign sequences give a modular Hadamard sign matrix. -/
theorem goethals_AtOrder (f : Fin 4 → Seq m I) (hf : ∀ t z, Sign (f t z))
    (hc : ∀ s : I, s ≠ 0 → ∑ t, cyclicCorr (f t) (f t) s=0) :
    AtOrder m (4*Fintype.card I) := by
  let A : RowMatrix m (Fin 4 × I) := fun i j => block f i.1 j.1 i.2 j.2
  apply of_card (I:=Fin 4 × I) (A:=A) _ (by simp)
  refine ⟨fun i j => block_sign f hf _ _ _ _,?_⟩
  rintro ⟨u,x⟩ ⟨v,y⟩ ne
  rw [Fintype.sum_prod_type]
  change (∑ t, dot (block f u t x) (block f v t y))=0
  rw [row_gram]
  split_ifs with uv
  · exact hc _ (sub_ne_zero.mpr fun he => ne (Prod.ext uv he))
  · rfl

/-- A checked packed binary sequence. A set bit represents a negative entry. -/
def bitSeq (m k : ℕ) (code : ℕ) (i : Fin k) : ZMod m :=
  if code.testBit i.val then -1 else 1

theorem of_bit_sequences {m k : ℕ} [NeZero k] (codes : Fin 4 → ℕ)
    (h : ∀ s : Fin k, s≠0 →
      ∑ t, cyclicCorr (bitSeq m k (codes t)) (bitSeq m k (codes t)) s=0) :
    AtOrder m (4*k) := by
  simpa only [Fintype.card_fin] using goethals_AtOrder
    (fun t => bitSeq m k (codes t))
    (fun t i => by unfold bitSeq; split <;> simp [Sign]) h

#print axioms goethals_AtOrder
end HadamardMod
