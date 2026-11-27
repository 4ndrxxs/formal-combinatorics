import Quantum.Hadamard.ArithmeticSingularSeeds

/-! The integral Gram identity proves that an odd order is a square
modulo every positive modulus, including at singular residues. -/
noncomputable section
namespace HadamardMod

private theorem scaled_gram_square {g M n u : ℕ} (gp : 0 < g) (hn : n=g*u)
    (cu : u.Coprime (g*M)) (on : Odd n) (H : IntegralSolution (g*M) n) :
    IsSquare (n:ZMod (g*M)) := by
  classical
  obtain ⟨A,_,gram⟩ := H
  choose K hK using gram
  let B : Matrix (Fin n) (Fin n) ℤ := fun i j => (if i=j then (u:ℤ) else 0)+(M:ℤ)*K i j
  have scale : A*A.transpose=(g:ℤ) • B := by
    ext i j
    change (A*A.transpose) i j=(g:ℤ)*B i j
    have h := hK i j
    have hu : (n:ℤ)=(g:ℤ)*u := by exact_mod_cast hn
    by_cases eq : i=j
    · subst j
      simp only [ite_true,Nat.cast_mul] at h
      simp [B,hu] at h ⊢
      linear_combination h
    · simp only [ite_eq_right eq,sub_zero,Nat.cast_mul] at h
      simp [B,eq]
      linear_combination h
  have det : A.det^2=(g:ℤ)^n*B.det := by
    have ds := congrArg Matrix.det scale
    rw [Matrix.det_smul,Matrix.det_mul,Matrix.det_transpose,Fintype.card_fin] at ds
    simpa only [pow_two] using ds
  have reduced : B.map (fun x : ℤ => (x:ZMod M)) =
      (u:ZMod M) • (1:Matrix (Fin n) (Fin n) (ZMod M)) := by
    ext i j
    change ((B i j:ℤ):ZMod M)=(u:ZMod M)*(1:Matrix (Fin n) (Fin n) (ZMod M)) i j
    by_cases eq : i=j
    · subst j; simp [B]
    · simp [B,Matrix.one_apply_ne eq,eq]
  have db : (B.det:ZMod M)=(u:ZMod M)^n := by
    rw [Int.cast_det,reduced,Matrix.det_smul]
    simp
  obtain ⟨l,hl⟩ : (M:ℤ)∣B.det-(u:ℤ)^n := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp
    (by simp only [Int.cast_sub,Int.cast_pow,Int.cast_natCast,db,sub_self])
  obtain ⟨k,hk⟩ := on
  have pwr : (g:ℤ)^n=((g:ℤ)^k)^2*g := by
    rw [hk,pow_succ,show 2*k=k*2 by ring,pow_mul]
  have gd : ((g:ℤ)^k)^2∣A.det^2 := by
    refine ⟨(g:ℤ)*B.det,?_⟩
    rw [det,pwr]
    ring
  obtain ⟨z,hz⟩ := (Int.pow_dvd_pow_iff two_ne_zero).mp gd
  have gs : ((g:ℤ)^k)^2 ≠ 0 := by positivity
  have zs : z^2=(g:ℤ)*B.det := by
    apply mul_left_cancel₀ gs
    calc
      ((g:ℤ)^k)^2*z^2 = A.det^2 := by rw [hz,mul_pow]
      _ = (g:ℤ)^n*B.det := det
      _ = ((g:ℤ)^k)^2*((g:ℤ)*B.det) := by
        rw [pwr]; ring
  have gu : (g:ℤ)*(u:ℤ)^n=(n:ℤ)*(u:ℤ)^(2*k) := by
    calc
      _ = (g:ℤ)*((u:ℤ)^(2*k)*u) := by rw [hk,pow_succ]
      _ = _ := by rw [show (n:ℤ)=(g:ℤ)*u by exact_mod_cast hn]; ring
  have modz : ((g*M:ℕ):ℤ)∣z^2-(n:ℤ)*(u:ℤ)^(2*k) := by
    refine ⟨l,?_⟩
    push_cast
    rw [zs,←gu,←mul_sub,hl]; ring
  let U := ZMod.unitOfCoprime u cu
  have eu : (U:ZMod (g*M))=(u:ZMod (g*M)) := ZMod.coe_unitOfCoprime _ _
  have zmod : (z:ZMod (g*M))^2=(n:ZMod (g*M))*(U:ZMod (g*M))^(2*k) := by
    rw [eu]
    apply sub_eq_zero.mp
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ (g*M)).mpr modz
  refine ⟨(z:ZMod (g*M))*(U⁻¹: (ZMod (g*M))ˣ)^k,?_⟩
  rw [←pow_two,mul_pow,zmod]
  push_cast
  rw [←pow_mul,show k*2=2*k by ring,mul_assoc,←mul_pow]
  simp

theorem odd_prime_power_necessary {p e n : ℕ} (pp : p.Prime) (on : Odd n)
    (H : IntegralSolution (p^e) n) : IsSquare (n:ZMod (p^e)) := by
  by_cases full : p^e∣n
  · rw [(ZMod.natCast_eq_zero_iff _ _).mpr full]
    exact ⟨0,by simp⟩
  have nz : n≠0 := by rintro rfl; simp at full
  let v := n.factorization p
  have ve : v<e := by
    by_contra! ge
    exact full ((pp.pow_dvd_iff_le_factorization nz).mpr ge)
  let g := p^v
  let u := n/g
  let M := p^(e-v)
  have mm : g*M=p^e := by dsimp [g,M]; rw [←pow_add, Nat.add_sub_of_le ve.le]
  have nu : n=g*u := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  have cu : u.Coprime (g*M) := by rw [mm]; exact (Nat.coprime_ordCompl pp nz).symm.pow_right e
  rw [← mm] at H ⊢
  exact scaled_gram_square (pow_pos pp.pos _) nu cu on H

/-- For an odd physical order the quadratic residue condition holds at
every positive modulus, with no coprimality hypothesis. -/
theorem odd_integral_necessary {m n : ℕ} (mp : 0 < m) (on : Odd n)
    (H : IntegralSolution m n) : IsSquare (n:ZMod m) := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p e pp _ => exact odd_prime_power_necessary pp on H
  | zero => omega
  | one => exact ⟨0,Subsingleton.elim _ _⟩
  | coprime a b ap bp cap ia ib =>
    obtain ⟨A,sg,gram⟩ := H
    have weak {c:ℕ} (cc:c∣a*b) : IntegralSolution c n :=
      ⟨A,sg,fun i j => (show (c:ℤ)∣((a*b:ℕ):ℤ) by exact_mod_cast cc).trans (gram i j)⟩
    obtain ⟨x,hx⟩ := ia (by omega) (weak (dvd_mul_right _ _))
    obtain ⟨y,hy⟩ := ib (by omega) (weak (dvd_mul_left _ _))
    let f := ZMod.chineseRemainder cap
    refine ⟨f.symm (x,y),f.injective ?_⟩
    rw [map_mul,map_natCast,f.apply_symm_apply]
    exact Prod.ext hx hy

/-- Exact eventual odd-order classification at all odd prime powers. -/
theorem odd_prime_power_classification {p : ℕ} (pp : p.Prime) (po : 2 < p) (e : ℕ) :
    ∃ B : ℕ, ∀ n≥B, Odd n → (IntegralSolution (p^e) n ↔ IsSquare (n:ZMod (p^e))) := by
  obtain ⟨B,hB⟩ := all_large_prime_power_squares pp po e
  exact ⟨B,fun n hn on => ⟨odd_prime_power_necessary pp on,fun sq => integer_gram (hB n hn sq)⟩⟩

#print axioms odd_integral_necessary
#print axioms odd_prime_power_classification
end HadamardMod
