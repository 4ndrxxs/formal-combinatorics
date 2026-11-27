import SignedConcentration
import Signed39Analytic
import SignedRows

/-! The six remaining finite parameter possibilities at norm 12 and group order divisible by three. -/

namespace Signed39.SmallTwelve

open Finset Signed39.Contraction Signed39.Analytic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Three integral entries of mass zero and energy eight are a rearrangement of -2,0,2. -/
theorem three_levels (u : ZMod 3 → ℤ) (hs : mass u=0) (he : energy u=8) :
    ∃ i j l : ZMod 3, u i= -2 ∧ u j=0 ∧ u l=2 := by
  change (∑ i, u i)=0 at hs
  change (∑ i, (u i)^2)=8 at he
  rw [sum_three] at hs he
  have aux (a b d : ℤ) (h : a+b+d=0) (e : a^2+b^2+d^2=8) :
      (a= -2 ∧ b=0 ∧ d=2) ∨ (a= -2 ∧ b=2 ∧ d=0) ∨ (a=0 ∧ b= -2 ∧ d=2) ∨
      (a=0 ∧ b=2 ∧ d= -2) ∨ (a=2 ∧ b= -2 ∧ d=0) ∨ (a=2 ∧ b=0 ∧ d= -2) := by
    have bnd (z : ℤ) (h : z^2≤8) : -2≤z ∧ z≤2 := by
      constructor
      · by_contra! h'
        have h₂ : z≤ -3 := by omega
        nlinarith [sq_nonneg (z+3)]
      · by_contra! h'
        have h₂ : 3≤z := by omega
        nlinarith [sq_nonneg (z-3)]
    obtain ⟨a1,a2⟩ := bnd a (by nlinarith [sq_nonneg b,sq_nonneg d])
    obtain ⟨b1,b2⟩ := bnd b (by nlinarith [sq_nonneg a,sq_nonneg d])
    have hd : d= -a-b := by omega
    rw [hd] at e ⊢
    interval_cases a <;> interval_cases b <;> norm_num at *
  rcases aux _ _ _ hs he with h|h|h|h|h|h
  · exact ⟨0,1,2,h⟩
  · exact ⟨0,2,1,h.1,h.2.2,h.2.1⟩
  · exact ⟨1,0,2,h.2.1,h.1,h.2.2⟩
  · exact ⟨2,0,1,h.2.2,h.1,h.2.1⟩
  · exact ⟨1,2,0,h.2.1,h.2.2,h.1⟩
  · exact ⟨2,1,0,h.2.2,h.2.1,h.1⟩

private theorem sum_in_order (b : ZMod 3 → ℤ) (i j l : ZMod 3) (hij : i≠j) (hil : i≠l) (hjl : j≠l) :
    ∑ z, b z = b i + b j + b l := by
  have un : ({i,j,l} : Finset (ZMod 3))=univ := eq_univ_of_card _ (by simp [hij,hil,hjl,ZMod.card])
  rw [← un]
  simp [hij,hil,hjl]
  ring

def validWeight (m lam c a : ℤ) (b : ℤ) : Prop :=
  admissibleRow 3 m 4 lam c a b ∧ admissibleShift 3 m a b

instance (m lam c a b : ℤ) : Decidable (validWeight m lam c a b) := by unfold validWeight; infer_instance

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- Each level carries an admissible row weight and the three weights sum to k. -/
theorem row_profile {k lam c : ℤ} {f : ZMod 3 × H → ℤ} (hf : IsSDS k lam f)
    (hn : k-lam=12) (hmass : mass f=3*c) (hc : Nat.Coprime 3 (Fintype.card H)) :
    ∃ i j l : ZMod 3, rowMass f i=c-2 ∧ rowMass f j=c ∧ rowMass f l=c+2 ∧
      energy (row f i)+energy (row f j)+energy (row f l)=k ∧
      validWeight (Fintype.card H) lam c (c-2) (energy (row f i)) ∧
      validWeight (Fintype.card H) lam c c (energy (row f j)) ∧
      validWeight (Fintype.card H) lam c (c+2) (energy (row f l)) := by
  have hnorm : k-lam=(3:ℤ)*4 := by omega
  obtain ⟨c',hm,_,hzero,hcc⟩ := centered_row_corr hf hnorm
  have ec : c'=c := by norm_num at hm; omega
  subst c'
  have en : energy (fun i => rowMass f i-c)=8 := by simpa [energy_zero] using hcc 0
  obtain ⟨i,j,l,hi,hj,hl⟩ := three_levels _ hzero en
  change rowMass f i-c= -2 at hi
  change rowMass f j-c=0 at hj
  change rowMass f l-c=2 at hl
  have ai : rowMass f i=c-2 := by omega
  have aj : rowMass f j=c := by omega
  have al : rowMass f l=c+2 := by omega
  have valid (z : ZMod 3) : validWeight (Fintype.card H) lam c (rowMass f z) (energy (row f z)) :=
    ⟨row_admissible hf hnorm hmass hc z,row_shift_admissible hf hnorm (by decide) hc z⟩
  have sum := sum_in_order (fun z => energy (row f z)) i j l
    (fun e => by rw [e] at hi; omega) (fun e => by rw [e] at hi; omega) (fun e => by rw [e] at hj; omega)
  have total : (∑ z, energy (row f z))=k := by
    simpa [energy,row,corr,pow_two,Fintype.sum_prod_type] using hf.flat 0
  exact ⟨i,j,l,ai,aj,al,sum.symm.trans total,ai ▸ valid i,aj ▸ valid j,al ▸ valid l⟩

def localExclusion (m : ℕ) (k lam c : ℤ) : Prop :=
  ∀ b₁ b₂ b₃ : Fin (m+1),
    validWeight m lam c (c-2) b₁.val → validWeight m lam c c b₂.val →
    validWeight m lam c (c+2) b₃.val → (b₁.val:ℤ)+b₂.val+b₃.val≠k

instance (m : ℕ) (k lam c : ℤ) : Decidable (localExclusion m k lam c) := by unfold localExclusion; infer_instance

theorem local_false {k lam c : ℤ} {m : ℕ} {f : ZMod 3 × H → ℤ} (hf : IsSDS k lam f)
    (hn : k-lam=12) (hmass : mass f=3*c) (hc : Nat.Coprime 3 m) (hcard : Fintype.card H=m)
    (certificate : localExclusion m k lam c) : False := by
  obtain ⟨i,j,l,_,_,_,ht,hi,hj,hl⟩ := row_profile hf hn hmass (hcard ▸ hc)
  rw [hcard] at hi hj hl
  have fin {a b : ℤ} (h : validWeight m lam c a b) :
      ∃ v : Fin (m+1), (v.val:ℤ)=b := by
    have b0 := h.1.2.2.1
    have bm := h.1.2.2.2.1
    exact ⟨⟨b.toNat,by omega⟩,Int.toNat_of_nonneg b0⟩
  obtain ⟨u,hu⟩ := fin hi
  obtain ⟨v,hv⟩ := fin hj
  obtain ⟨w,hw⟩ := fin hl
  exact certificate u v w (hu ▸ hi) (hv ▸ hj) (hw ▸ hl) (by simpa only [hu,hv,hw] using ht)

private def sixRejected (w : BitVec 13) : Prop :=
  mass (fun x : ZMod 13 => bitInt w x)=6 →
  (∀ t : ZMod 13, 3 ∣ corr (fun x : ZMod 13 => bitInt w x) t) → False

private instance (w : BitVec 13) : Decidable (sixRejected w) := by unfold sixRejected; infer_instance

private def sixChunk (a : ℕ) : Prop := ∀ b : Fin 256, sixRejected (BitVec.ofNat 13 (256*a+b.val))
private instance (a : ℕ) : Decidable (sixChunk a) := by unfold sixChunk; infer_instance

private theorem sixChunk0 : sixChunk 0 := by decide +kernel
private theorem sixChunk1 : sixChunk 1 := by decide +kernel
private theorem sixChunk2 : sixChunk 2 := by decide +kernel
private theorem sixChunk3 : sixChunk 3 := by decide +kernel
private theorem sixChunk4 : sixChunk 4 := by decide +kernel
private theorem sixChunk5 : sixChunk 5 := by decide +kernel
private theorem sixChunk6 : sixChunk 6 := by decide +kernel
private theorem sixChunk7 : sixChunk 7 := by decide +kernel
private theorem sixChunk8 : sixChunk 8 := by decide +kernel
private theorem sixChunk9 : sixChunk 9 := by decide +kernel
private theorem sixChunk10 : sixChunk 10 := by decide +kernel
private theorem sixChunk11 : sixChunk 11 := by decide +kernel
private theorem sixChunk12 : sixChunk 12 := by decide +kernel
private theorem sixChunk13 : sixChunk 13 := by decide +kernel
private theorem sixChunk14 : sixChunk 14 := by decide +kernel
private theorem sixChunk15 : sixChunk 15 := by decide +kernel
private theorem sixChunk16 : sixChunk 16 := by decide +kernel
private theorem sixChunk17 : sixChunk 17 := by decide +kernel
private theorem sixChunk18 : sixChunk 18 := by decide +kernel
private theorem sixChunk19 : sixChunk 19 := by decide +kernel
private theorem sixChunk20 : sixChunk 20 := by decide +kernel
private theorem sixChunk21 : sixChunk 21 := by decide +kernel
private theorem sixChunk22 : sixChunk 22 := by decide +kernel
private theorem sixChunk23 : sixChunk 23 := by decide +kernel
private theorem sixChunk24 : sixChunk 24 := by decide +kernel
private theorem sixChunk25 : sixChunk 25 := by decide +kernel
private theorem sixChunk26 : sixChunk 26 := by decide +kernel
private theorem sixChunk27 : sixChunk 27 := by decide +kernel
private theorem sixChunk28 : sixChunk 28 := by decide +kernel
private theorem sixChunk29 : sixChunk 29 := by decide +kernel
private theorem sixChunk30 : sixChunk 30 := by decide +kernel
private theorem sixChunk31 : sixChunk 31 := by decide +kernel

/-- Exhaustive binary masks split into 32 independent kernel reductions. -/
private theorem six_binary_false (w : BitVec 13) : sixRejected w := by
  let a : Fin 32 := ⟨w.toNat/256,by have h:=w.isLt; omega⟩
  let b : Fin 256 := ⟨w.toNat%256,Nat.mod_lt _ (by decide)⟩
  have eq : BitVec.ofNat 13 (256*a.val+b.val)=w := by simp [a,b,Nat.div_add_mod]
  have done (x : Fin 32) : sixChunk x.val := by
    fin_cases x
    · exact sixChunk0
    · exact sixChunk1
    · exact sixChunk2
    · exact sixChunk3
    · exact sixChunk4
    · exact sixChunk5
    · exact sixChunk6
    · exact sixChunk7
    · exact sixChunk8
    · exact sixChunk9
    · exact sixChunk10
    · exact sixChunk11
    · exact sixChunk12
    · exact sixChunk13
    · exact sixChunk14
    · exact sixChunk15
    · exact sixChunk16
    · exact sixChunk17
    · exact sixChunk18
    · exact sixChunk19
    · exact sixChunk20
    · exact sixChunk21
    · exact sixChunk22
    · exact sixChunk23
    · exact sixChunk24
    · exact sixChunk25
    · exact sixChunk26
    · exact sixChunk27
    · exact sixChunk28
    · exact sixChunk29
    · exact sixChunk30
    · exact sixChunk31
  exact eq ▸ done a b

omit [AddCommGroup H] [DecidableEq H] in
theorem binary_of_mass_eq_energy (u : H → ℤ) (ht : ∀ x, u x= -1 ∨ u x=0 ∨ u x=1)
    (he : energy u = mass u) (x : H) : u x=0 ∨ u x=1 := by
  have sum : (∑ z, ((u z)^2-u z))=0 := by rw [sum_sub_distrib]; exact sub_eq_zero.mpr he
  have h0 := (sum_eq_zero_iff_of_nonneg (fun z _ => by
    rcases ht z with e|e|e <;> norm_num [e])).mp sum x (mem_univ x)
  rcases ht x with e|e|e <;> simp_all

theorem product_39_23_false {f : ZMod 3 × ZMod 13 → ℤ} (hf : IsSDS 23 11 f) (hmass : mass f=21) : False := by
  obtain ⟨i,j,l,_,ha,_,ht,hi,hj,hl⟩ := row_profile (c:=7) hf (by decide) hmass (by decide)
  have weights : ∀ b₁ b₂ b₃ : Fin 14,
      validWeight 13 11 7 5 b₁.val → validWeight 13 11 7 7 b₂.val →
      validWeight 13 11 7 9 b₃.val → (b₁.val:ℤ)+b₂.val+b₃.val=23 → b₂.val=7 := by decide +kernel
  have fin {a b : ℤ} (h : validWeight 13 11 7 a b) :
      ∃ v : Fin 14, (v.val:ℤ)=b := by
    have b0 := h.1.2.2.1
    have bm := h.1.2.2.2.1
    exact ⟨⟨b.toNat,by omega⟩,Int.toNat_of_nonneg b0⟩
  obtain ⟨u,hu⟩ := fin hi
  obtain ⟨v,hv⟩ := fin hj
  obtain ⟨w,hw⟩ := fin hl
  have seven := weights u v w (hu ▸ hi) (hv ▸ hj) (hw ▸ hl) (by simpa only [hu,hv,hw] using ht)
  have en : energy (row f j)=7 := by omega
  have binary := binary_of_mass_eq_energy (row f j) (fun x => hf.ternary (j,x)) (en.trans ha.symm)
  let mask := bits (fun x : Fin 13 => decide (row f j x = 0))
  have val (x : ZMod 13) : bitInt mask x = 1-row f j x := by
    have hbit : mask.getLsbD x.val = decide (row f j x=0) :=
      bits_get (fun z : Fin 13 => decide (row f j z=0)) (x:Fin 13)
    change (if mask.getLsbD x.val then (1:ℤ) else 0) = _
    rw [hbit]
    simp only [decide_eq_true_eq]
    rcases binary x with h|h <;> simp [h]
  apply six_binary_false mask
  · simp only [mass,val,sum_sub_distrib,sum_const,card_univ,ZMod.card,nsmul_eq_mul,mul_one]
    change 13-rowMass f j=6
    omega
  · intro t
    have hh := row_corr_dvd hf (by decide : (23:ℤ)-11=(3:ℤ)*4) (by decide) j t
    change 3 ∣ 4*corr (row f j) t+11*(rowMass f j)^2 at hh
    rw [ha] at hh
    simp only [val,complement_corr]
    change 3 ∣ 13-2*rowMass f j+corr (row f j) t
    omega

#print axioms product_39_23_false

end Signed39.SmallTwelve

