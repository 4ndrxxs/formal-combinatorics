import Quantum.Hadamard.ArithmeticPeriods
import Quantum.Hadamard.PaleyNecessity

/-! At every odd modulus, the determinant obstruction is sufficient for
all sufficiently large odd orders coprime to the modulus. -/
noncomputable section
namespace HadamardMod
open Hadamard.Arithmetic Hadamard.PG

theorem unit_square_dense {m a n s : ℕ} (mp : 1 < m) (odd : (2:ℕ).Coprime m)
    (ap : 0 < a) (ma : m ∣ a) (cs : s.Coprime m) (res : n ≡ 4*s^2 [MOD m]) (N : ℕ) :
    ∃ h > N, AtOrder m h ∧ h ≡ n [MOD a] := by
  have mla := Nat.le_of_dvd ap ma
  obtain ⟨q,hq,pq,qs⟩ := Nat.forall_exists_prime_gt_and_modEq (max a N) (by omega : m≠0) cs
  have : Fact q.Prime := ⟨pq⟩
  have qa : q.Coprime a := pq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ap (by omega))
  obtain ⟨i,_,hi⟩ := Nat.exists_mul_mod_eq_one_of_coprime (qa.pow_left 2) (by omega)
  have inv : q^2*i ≡ 1 [MOD a] := by
    simpa [Nat.ModEq,Nat.mod_eq_of_lt (by omega : 1 < a)] using hi
  let j := n*i+a
  have jm : j ≡ n*i [MOD a] := by simp [j,Nat.ModEq]
  have done : q^2*j ≡ n [MOD a] := calc
    q^2*j ≡ q^2*(n*i) [MOD a] := jm.mul_left _
    _ = (q^2*i)*n := by ring
    _ ≡ n [MOD a] := by simpa using inv.mul_right n
  have firm : q^2*j ≡ q^2*4 [MOD m] := by
    apply (done.of_dvd ma).trans
    apply res.trans
    simpa [mul_comm 4] using (qs.pow 2).symm.mul_right 4
  have jm4 := Nat.ModEq.cancel_left_of_coprime (qa.pow_left 2 |>.of_dvd_right ma).symm firm
  have J : AtOrder m j := offdiag_four (by simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr jm4)
  have A : AtOrder m (q^2) := by
    simpa using prime_power_affine (p := q) (e := 1) mp odd (by decide) (by simp; omega)
  have jp : 0 < j := by dsimp [j]; omega
  have qbig : q ≤ q^2 := by have := pq.pos; nlinarith
  exact ⟨q^2*j,(show N < q by omega).trans_le (qbig.trans (Nat.le_mul_of_pos_right _ jp)),at_mul A J,done⟩

theorem large_of_progression_seeds {m r : ℕ} {I : Type*} [Fintype I]
    (D : Extender m I (r:ZMod m)) (large : 1 < Fintype.card I)
    (seeds : ∀ a, 0 < a → m ∣ a → ∀ n, n ≡ r [MOD m] →
      ∃ h > 0, AtOrder m h ∧ h ≡ n [MOD a]) :
    ∃ B, ∀ n ≥ B, n ≡ r [MOD m] → AtOrder m n := by
  classical
  let a := Fintype.card I-1
  have ap : 0 < a := by dsimp [a]; omega
  have ma : m ∣ a := by
    apply (ZMod.natCast_eq_zero_iff a m).mp
    dsimp [a]
    rw [Nat.cast_sub (by omega),Nat.cast_one,D.dim,sub_self]
  have cls (i:Fin a) : ∃ B, ∀ n ≥ B, n ≡ i.val [MOD a] → n ≡ r [MOD m] → AtOrder m n := by
    by_cases ir : i.val ≡ r [MOD m]
    · obtain ⟨h,pos,H,hi⟩ := seeds a ap ma i.val ir
      refine ⟨h,?_⟩
      intro n le ni _
      obtain ⟨t,ht⟩ := (Nat.modEq_iff_dvd' le).mp (hi.trans ni.symm)
      have c := (ZMod.natCast_eq_natCast_iff _ _ _).mpr ((hi.of_dvd ma).trans ir)
      have next := D.iterate pos H c t
      change AtOrder m (h+t*a) at next
      rwa [show h+t*a=n by rw [Nat.mul_comm]; omega] at next
    · exact ⟨0,fun n _ ni nr => (ir ((ni.of_dvd ma).symm.trans nr)).elim⟩
  choose B hB using cls
  refine ⟨Finset.univ.sup B,?_⟩
  intro n hn nr
  let i : Fin a := ⟨n%a,Nat.mod_lt _ ap⟩
  exact hB i n ((Finset.le_sup (Finset.mem_univ i)).trans hn) (Nat.mod_modEq n a).symm nr

theorem large_unit_square_class {m r s : ℕ} (mp : 1 < m) (odd : (2:ℕ).Coprime m)
    (cs : s.Coprime m) (rs : r ≡ 4*s^2 [MOD m]) :
    ∃ B, ∀ n ≥ B, n ≡ r [MOD m] → AtOrder m n := by
  obtain ⟨i,_,hi⟩ := Nat.exists_mul_mod_eq_one_of_coprime (cs.pow_left 2) mp
  have inv : s^2*i ≡ 1 [MOD m] := by simpa [Nat.ModEq,Nat.mod_eq_of_lt mp] using hi
  have ci : i.Coprime m := Nat.coprime_of_mul_modEq_one (s^2) (by rwa [mul_comm i _])
  obtain ⟨q,hq,pq,qi⟩ := Nat.forall_exists_prime_gt_and_modEq 2 (by omega : m≠0) ci
  have : Fact q.Prime := ⟨pq⟩
  obtain ⟨d,zero,period⟩ := geom_period (by omega) (coprime_of_modEq qi ci)
  have qt : (q:ZMod m)*(s:ZMod m)^2=1 := by
    have qr : q*s^2 ≡ 1 [MOD m] := (qi.mul_right (s^2)).trans (by rw [Nat.mul_comm i _]; exact inv)
    simpa using (ZMod.natCast_eq_natCast_iff _ _ m).mpr qr
  have eq : 4*(q:ZMod m)^(d+1)=(r:ZMod m) := by
    have rt : (r:ZMod m)=4*(s:ZMod m)^2 := by simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr rs
    rw [rt]
    rw [show d+2=d+1+1 by omega,pow_succ] at period
    linear_combination 4*(s:ZMod m)^2*period-4*(q:ZMod m)^(d+1)*qt
  obtain ⟨D⟩ := projective_extender_at (d := d+1) zero
  rw [eq] at D
  apply large_of_progression_seeds D
  · rw [Fintype.card_fin,geom_succ]
    have z : 0 < geom q ((d+1)+1) := by rw [geom_succ]; omega
    exact Nat.lt_add_of_pos_right (Nat.mul_pos z pq.pos)
  · intro a ap ma n nr
    exact unit_square_dense mp odd ap ma cs (nr.trans rs) 0

theorem odd_unit_necessary {m n : ℕ} (cn : n.Coprime m) (on : Odd n)
    (h : AtOrder m n) : IsSquare (n:ZMod m) := by
  classical
  obtain ⟨D,hD⟩ := h
  let H : Matrix (Fin n) (Fin n) (ZMod m) := D
  let u := ZMod.unitOfCoprime n cn
  have gu : (u:ZMod m)=(n:ZMod m) := ZMod.coe_unitOfCoprime n cn
  have gram : H*H.transpose=(u:ZMod m) • (1:Matrix (Fin n) (Fin n) (ZMod m)) := by
    rw [gu]
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply]
    by_cases h : i=j
    · subst j
      simpa [H] using hD.norm_rows i
    · simpa [H,Matrix.one_apply_ne h] using hD.ortho i j h
  have det : H.det^2=(u:ZMod m)^n := by
    simpa [Matrix.det_mul,Matrix.det_transpose,Matrix.det_smul,pow_two] using congrArg Matrix.det gram
  obtain ⟨k,hk⟩ := on
  refine ⟨H.det*((u⁻¹: (ZMod m)ˣ):ZMod m)^k,?_⟩
  rw [← gu,← pow_two,mul_pow,det,hk,Nat.mul_comm 2 k,pow_succ,pow_mul,← pow_mul]
  rw [show (u:ZMod m)^(k*2)*(u:ZMod m)*((↑u⁻¹:ZMod m)^k)^2=
         (u:ZMod m)*(((u:ZMod m)*(↑u⁻¹:ZMod m))^(k*2)) by rw [mul_pow,←pow_mul]; ring]
  simp

theorem all_large_unit_squares {m : ℕ} (mp : 0 < m) (odd : (2:ℕ).Coprime m) :
    ∃ B : ℕ, ∀ n : ℕ, n ≥ B → n.Coprime m → IsSquare (n:ZMod m) → AtOrder m n := by
  classical
  by_cases m1 : m=1
  · subst m
    exact ⟨0,fun _ _ _ _ => ones (Subsingleton.elim _ _)⟩
  have mh : 1 < m := by omega
  let : NeZero m := ⟨by omega⟩
  obtain ⟨a,_,ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime odd mh
  have inv : 2*a ≡ 1 [MOD m] := by simpa [Nat.ModEq,Nat.mod_eq_of_lt mh] using ha
  have ca : a.Coprime m := Nat.coprime_of_mul_modEq_one 2 (by rw [mul_comm]; exact inv)
  have cls (i:Fin m) : ∃ B, ∀ n ≥ B, n ≡ i.val [MOD m] → n.Coprime m →
      IsSquare (n:ZMod m) → AtOrder m n := by
    by_cases h : i.val.Coprime m ∧ IsSquare (i.val:ZMod m)
    · obtain ⟨ci,z,hz⟩ := h
      have zr : z.val^2 ≡ i.val [MOD m] := (ZMod.natCast_eq_natCast_iff _ _ _).mp (by simp [pow_two,hz])
      have cz := (coprime_of_modEq zr ci).of_dvd_left (dvd_pow_self z.val (by decide : 2≠0))
      have rs : i.val ≡ 4*(z.val*a)^2 [MOD m] := by
        apply zr.symm.trans
        have H := (inv.pow 2).symm.mul_left (z.val^2)
        convert H using 1 <;> ring
      obtain ⟨B,hB⟩ := large_unit_square_class mh odd (cz.mul_left ca) rs
      exact ⟨B,fun n hn res _ _ => hB n hn res⟩
    · refine ⟨0,?_⟩
      intro n _ ni cn sq
      have cast := (ZMod.natCast_eq_natCast_iff _ _ _).mpr ni
      exact (h ⟨coprime_of_modEq ni.symm cn,cast ▸ sq⟩).elim
  choose B hB using cls
  refine ⟨Finset.univ.sup B,?_⟩
  intro n hn
  let i : Fin m := ⟨n%m,Nat.mod_lt _ mp⟩
  exact hB i n ((Finset.le_sup (Finset.mem_univ i)).trans hn) (Nat.mod_modEq n m).symm

/-- Exact eventual classification of all odd orders coprime to an
arbitrary positive odd modulus. -/
theorem odd_coprime_classification {m : ℕ} (mp : 0 < m) (odd : (2:ℕ).Coprime m) :
    ∃ B, ∀ n ≥ B, Odd n → n.Coprime m →
      (IntegralSolution m n ↔ IsSquare (n:ZMod m)) := by
  obtain ⟨B,hB⟩ := all_large_unit_squares mp odd
  exact ⟨B,fun n hn on cn => ⟨fun H => odd_unit_necessary cn on (atOrder_of_integral H),
    fun sq => integer_gram (hB n hn cn sq)⟩⟩

#print axioms odd_coprime_classification

end HadamardMod
