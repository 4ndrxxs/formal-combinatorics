import Quantum.Hadamard.PaleyProjective
import Quantum.Hadamard.ArithmeticBase

/-! Moving from orders divisible by four to the other allowed parities through projective
hyperplane extenders. For primes `p ≡ 3 (mod 4)`, the exponents are `(p-1)/2` and `p-1`. -/
noncomputable section
namespace Hadamard.PG
open Finset HadamardMod

private theorem choose_step {n s : ℕ} (h : s%2=1 ∨ s%4=2 ∧ n%2=0) :
    ∃ t : ℕ, t ≤ 3 ∧ (t*s)%4=n%4 := by
  have cert : ∀ x y : Fin 4, (x.val%2=1 ∨ x.val=2 ∧ y.val%2=0) →
      ∃ t : Fin 4, (t.val*x.val)%4=y.val := by decide
  let x : Fin 4 := ⟨s%4,Nat.mod_lt _ (by decide)⟩
  let y : Fin 4 := ⟨n%4,Nat.mod_lt _ (by decide)⟩
  have hh : x.val%2=1 ∨ x.val=2 ∧ y.val%2=0 := by dsimp [x,y]; omega
  obtain ⟨t,ht⟩ := cert x y hh
  refine ⟨t.val,by have := t.isLt; omega,?_⟩
  simpa [x,y,Nat.mul_mod_mod] using ht

/-- One odd step reaches all four possible orders modulo four; a twice-odd step
reaches both even orders. -/
theorem parity_from_four {p : ℕ} {r : ZMod p} {v : ℕ} (D : Extender p (Fin v) r)
    (four : ∃ B : ℕ, ∀ n : ℕ, n ≥ B → 4∣n → AtOrder p n) :
    ∃ B : ℕ, ∀ n : ℕ, n ≥ B → (n : ZMod p)=r →
      ((v-1)%2=1 ∨ (v-1)%4=2 ∧ n%2=0) → AtOrder p n := by
  obtain ⟨B,hB⟩ := four
  refine ⟨B+3*(v-1)+1, ?_⟩
  intro n large hr hstep
  obtain ⟨t,ht,hmod⟩ := choose_step hstep
  have b : t*(v-1) ≤ 3*(v-1) := Nat.mul_le_mul_right _ ht
  let a := n-t*(v-1)
  have eqn : a+t*(v-1)=n := by dsimp [a]; omega
  have ad : 4∣a := (Nat.modEq_iff_dvd' (show t*(v-1)≤n by omega)).mp hmod
  have dim : (v : ZMod p)=1 := by simpa using D.dim
  have posv : 0<v := by simpa using D.pos
  have st : ((v-1:ℕ):ZMod p)=0 := by rw [Nat.cast_sub (by omega),Nat.cast_one,dim,sub_self]
  have ar : (a:ZMod p) = r := by
    rw [←eqn,Nat.cast_add,Nat.cast_mul,st,mul_zero,add_zero] at hr
    exact hr
  have ha : 0<a := by dsimp [a]; omega
  have ab : B≤a := by dsimp [a]; omega
  simpa only [Fintype.card_fin,eqn] using D.iterate ha (hB a ab ad) ar t

theorem choose_base {p : ℕ} [Fact p.Prime] (hp : 2<p) {w : ZMod p} (hw : w≠0) :
    ∃ q : ℕ, q.Prime ∧ (q:ZMod p)=w ∧ (q:ZMod 4)=1 := by
  have cop : w.val.Coprime p := ZMod.val_coe_unit_coprime (Units.mk0 w hw)
  obtain ⟨q,_,hqa,hqb,hqc⟩ := Hadamard.Arithmetic.prime_crt (m:=p) (n:=4)
    (a:=w.val) (b:=1) (Fact.out : p.Prime).ne_zero (by decide)
    (Hadamard.Arithmetic.four_coprime_prime (m:=p) Fact.out hp).symm cop (by decide) 2
  refine ⟨q,hqa,?_,?_⟩
  · exact ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hqb).trans (ZMod.natCast_zmod_val _)
  · exact (ZMod.natCast_eq_natCast_iff _ 1 _).mpr hqc

theorem geometric_step {q d : ℕ} (h : (q : ZMod 4)=1) :
    (geom q (d+1)-1)%4=d%4 := by
  have e : geom q (d+1)-1=geom q d*q := by rw [geom_succ]; omega
  rw [e]
  apply (ZMod.natCast_eq_natCast_iff _ _ 4).mp
  rw [Nat.cast_mul,geom_at_one q 4 d h,h,mul_one]

private theorem at_residue {p : ℕ} [Fact p.Prime] (hp : p%4=3)
    (four : ∃ B : ℕ, ∀ n : ℕ, n ≥ B → 4∣n → AtOrder p n) (r : ZMod p) :
    ∃ B : ℕ, ∀ n : ℕ, n ≥ B → (n : ZMod p)=r → (Even n ∨ IsSquare r) → AtOrder p n := by
  have hp2 : 2<p := by omega
  have two : (2:ZMod p) ≠ 0 := by
    intro H
    have hp2' : p∣2 := (ZMod.natCast_eq_zero_iff _ _).mp H
    exact (Nat.not_dvd_of_pos_of_lt (by decide) hp2) hp2'
  have fourne : (4:ZMod p) ≠ 0 := by rw [show (4:ZMod p)=2*2 by norm_num]; exact mul_ne_zero two two
  by_cases r0 : r=0
  · exact ⟨0,fun n _ hr _ => ones (hr.trans r0)⟩
  by_cases r4 : r=4
  · exact ⟨0,fun n _ hr _ => offdiag_four (hr.trans r4)⟩
  let w : ZMod p := 4/r
  have wne : w≠0 := div_ne_zero fourne r0
  have w1 : w ≠ 1 := by
    intro H
    have eqr : (4:ZMod p)=r := by simpa using (div_eq_iff r0).mp H
    exact r4 eqr.symm
  obtain ⟨q,hq,qw,q4⟩ := choose_base hp2 wne
  let : Fact q.Prime := ⟨hq⟩
  have qne : (q:ZMod p)≠1 := qw ▸ w1
  have qnz : (q:ZMod p)≠0 := qw ▸ wne
  have prod : (q:ZMod p)*r=4 := by rw [qw]; exact div_mul_cancel₀ _ r0
  have bridge (d : ℕ) (hd : 0<d) (power : (q:ZMod p)^d=1) :
      ∃ B : ℕ, ∀ n : ℕ, n ≥ B → (n:ZMod p)=r → (d%2=1 ∨ d%4=2 ∧ n%2=0) → AtOrder p n := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
    have eqr : 4*(q:ZMod p)^k=r := by
      apply mul_left_cancel₀ qnz
      calc
        (q:ZMod p)*(4*(q:ZMod p)^k) = 4*(q:ZMod p)^(k+1) := by ring
        _ = (q:ZMod p)*r := by rw [power,prod,mul_one]
    obtain ⟨D⟩ := prime_extender power qne
    obtain ⟨B,hB⟩ := parity_from_four D four
    have step := geometric_step (d:=k+1) q4
    change (geom q (k+2)-1)%4=(k+1)%4 at step
    refine ⟨B,fun n hn hr hyp => hB n hn (hr.trans eqr.symm) ?_⟩
    change (k+1)%2=1 ∨ (k+1)%4=2 ∧ n%2=0 at hyp
    have step2 := congrArg (fun u:ℕ => u%2) step
    simp only [Nat.mod_mod_of_dvd _ (by decide : 2∣4)] at step2
    omega
  by_cases sq : IsSquare r
  · obtain ⟨x,hx⟩ := sq
    have xn : x≠0 := by rintro rfl; simp at hx; exact r0 hx
    have base : (q:ZMod p)=(2/x)^2 := by rw [qw]; dsimp [w]; rw [hx]; field_simp; ring
    have xp : (2/x:ZMod p)≠0 := div_ne_zero two xn
    have eqp : 2*((p-1)/2)=p-1 := by omega
    have eq := ZMod.pow_card_sub_one_eq_one xp
    have hqpow : (q:ZMod p)^((p-1)/2)=1 := by rw [base,←pow_mul,eqp,eq]
    obtain ⟨B,hB⟩ := bridge ((p-1)/2) (by omega) hqpow
    exact ⟨B,fun n hn hr _ => hB n hn hr (Or.inl (by omega))⟩
  · obtain ⟨B,hB⟩ := bridge (p-1) (by omega) (ZMod.pow_card_sub_one_eq_one qnz)
    exact ⟨B,fun n hn hr h => hB n hn hr (Or.inr ⟨by omega,Nat.even_iff.mp (h.resolve_right sq)⟩)⟩

/-- Kuperberg's sufficient condition for every prime `3 mod 4`, reduced to
eventual existence in orders divisible by four at the same prime. -/
theorem parity_bridge_three_mod_four {p : ℕ} [Fact p.Prime] (hp : p%4=3)
    (four : ∃ B : ℕ, ∀ n : ℕ, n ≥ B → 4∣n → AtOrder p n) :
    ∃ B : ℕ, ∀ n : ℕ, n ≥ B → (Even n ∨ IsSquare (n:ZMod p)) → AtOrder p n := by
  classical
  choose B hB using at_residue hp four
  refine ⟨univ.sup B,fun n hn h => hB (n:ZMod p) n ?_ rfl h⟩
  exact (le_sup (f:=B) (mem_univ (n:ZMod p))).trans hn

#print axioms parity_bridge_three_mod_four
end Hadamard.PG

