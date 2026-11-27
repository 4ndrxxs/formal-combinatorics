import Mathlib

/-! An elementary primitive-root witness for the symmetric conference
construction. A square is a product of two primitive elements. Choosing
the square four pairs x with 4/x, which flips the character of 2-x. -/

namespace Hadamard.Arithmetic

theorem even_sum_units {N k : ℕ} (hN : 1 < N) (hk : Even k) :
    ∃ u v w : ℕ, u.Coprime N ∧ v.Coprime N ∧ u+v = k+w*N := by
  classical
  let a (s : ℕ) := if k%s=1 then 2 else 1
  have ppos (s : ℕ) (hs : s ∈ N.primeFactors) := (Nat.mem_primeFactors.mp hs).1
  have pp : Set.Pairwise (↑N.primeFactors : Set ℕ) (fun s t => s.Coprime t) := by
    intro s hs t ht ne
    exact (Nat.coprime_primes (ppos _ hs) (ppos _ ht)).mpr ne
  obtain ⟨u,hu⟩ := Nat.chineseRemainderOfFinset a id N.primeFactors
    (fun s hs => (ppos s hs).ne_zero) pp
  let v := k+(u+1)*N-u
  have bound : u ≤ k+(u+1)*N := by nlinarith
  have sum : u+v = k+(u+1)*N := by dsimp [v]; omega
  have sumMod : u+v ≡ k [MOD N] := by simp [Nat.ModEq,sum]
  have two (s : ℕ) (hs : s.Prime) (eq : k%s=1) : 2 < s := by
    have h := hs.two_le
    have ke := Nat.even_iff.mp hk
    by_contra! le
    have s2 : s=2 := by omega
    rw [s2, ke] at eq
    omega
  refine ⟨u,v,u+1,?_,?_,sum⟩
  · by_contra bad
    obtain ⟨s,hs,su,sN⟩ := Nat.Prime.not_coprime_iff_dvd.mp bad
    have H := hu s (Nat.mem_primeFactors.mpr ⟨hs,sN,by omega⟩)
    change u%s = a s%s at H
    have uz := Nat.mod_eq_zero_of_dvd su
    by_cases eq : k%s=1
    · simp [a,eq,Nat.mod_eq_of_lt (two s hs eq),uz] at H
    · simp [a,eq,Nat.mod_eq_of_lt hs.one_lt,uz] at H
  · by_contra bad
    obtain ⟨s,hs,sv,sN⟩ := Nat.Prime.not_coprime_iff_dvd.mp bad
    have H := hu s (Nat.mem_primeFactors.mpr ⟨hs,sN,by omega⟩)
    change u%s = a s%s at H
    have modk : u ≡ k [MOD s] := by
      simpa using (((Nat.modEq_zero_iff_dvd.mpr sv).add_left u).symm.trans (sumMod.of_dvd sN))
    change u%s=k%s at modk
    by_cases eq : k%s=1
    · simp [a,eq,Nat.mod_eq_of_lt (two s hs eq)] at H
      omega
    · simp [a,eq,Nat.mod_eq_of_lt hs.one_lt] at H
      omega

theorem prime_residue_bridge {p : ℕ} [Fact p.Prime] (odd : 2 < p) :
    p%8=1 ∨ p%4=3 ∨ ¬IsSquare (2 : ZMod p) := by
  by_cases h : p%8=1
  · exact Or.inl h
  by_cases h4 : p%4=3
  · exact Or.inr (Or.inl h4)
  refine Or.inr (Or.inr ?_)
  intro sq
  rcases (ZMod.exists_sq_eq_two_iff (by omega : p ≠ 2)).mp sq with a|a <;> omega

private theorem primitive_four_factors {p : ℕ} [Fact p.Prime] (odd : 2 < p) :
    ∃ x y : ZMod p, IsPrimitiveRoot x (p-1) ∧ IsPrimitiveRoot y (p-1) ∧ x*y=4 := by
  let : NeZero (p-1) := ⟨by omega⟩
  obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have G : IsPrimitiveRoot (g : ZMod p) (p-1) := by
    apply IsPrimitiveRoot.iff_orderOf.mpr
    rw [orderOf_units,hg,Nat.card_eq_fintype_card,Fintype.card_units,ZMod.card]
  have nz : (2 : ZMod p) ≠ 0 := by
    intro h
    exact (Nat.not_dvd_of_pos_of_lt (by decide) odd) ((ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h))
  obtain ⟨k,_,kg⟩ := G.eq_pow_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one nz)
  obtain ⟨u,v,w,cu,cv,uv⟩ := even_sum_units (N := p-1) (k := 2*k) (by omega) (by exact ⟨k,by omega⟩)
  refine ⟨(g:ZMod p)^u,(g:ZMod p)^v,G.pow_of_coprime _ cu,G.pow_of_coprime _ cv,?_⟩
  have period : (g : ZMod p)^(w*(p-1)) = 1 := by
    rw [Nat.mul_comm w _,pow_mul,G.pow_eq_one,one_pow]
  rw [← pow_add,uv,pow_add,period,mul_one,Nat.mul_comm 2 k,pow_mul,kg]
  norm_num

private theorem primitive_nonsquare {p : ℕ} [Fact p.Prime] (odd : 2 < p)
    {x : ZMod p} (h : IsPrimitiveRoot x (p-1)) : ¬IsSquare x := by
  intro sx
  have nx := (h.isUnit (by omega)).ne_zero
  have eq := (FiniteField.isSquare_iff (by simpa only [ZMod.ringChar_zmod_n] using (show p ≠ 2 by omega)) nx).mp sx
  rw [ZMod.card] at eq
  exact h.pow_ne_one_of_pos_of_lt (by omega) (by omega) eq

theorem primitive_linear_square {p : ℕ} [Fact p.Prime] (h8 : p%8=1) :
    ∃ x : ZMod p, IsPrimitiveRoot x (p-1) ∧ ¬IsSquare x ∧ IsSquare (2-x) := by
  have hp : p.Prime := Fact.out
  have odd : 2 < p := by have := hp.two_le; omega
  obtain ⟨x,y,px,py,xy⟩ := primitive_four_factors odd
  have nx := primitive_nonsquare odd px
  have ny := primitive_nonsquare odd py
  by_cases s : IsSquare (2-x)
  · exact ⟨x,px,nx,s⟩
  refine ⟨y,py,ny,?_⟩
  have sq2 := (ZMod.exists_sq_eq_two_iff (by omega : p≠2)).mpr (Or.inl h8)
  have negsq := (ZMod.exists_sq_eq_neg_two_iff (by omega : p≠2)).mpr (Or.inl h8)
  have two0 : (2 : ZMod p) ≠ 0 := by
    intro h
    exact (Nat.not_dvd_of_pos_of_lt (by decide) odd) ((ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h))
  have yn : 2-y ≠ 0 := by intro dis; exact ny ((sub_eq_zero.mp dis) ▸ sq2)
  have ident : (2-y)*x = (-2)*(2-x) := by linear_combination -xy
  have hc := congrArg (quadraticChar (ZMod p)) ident
  rw [map_mul,map_mul,quadraticChar_neg_one_iff_not_isSquare.mpr nx,
    (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr two0)).mpr negsq,
    quadraticChar_neg_one_iff_not_isSquare.mpr s] at hc
  apply (quadraticChar_one_iff_isSquare yn).mp
  omega

/-- For primes one modulo eight, a nonsquare whose positive even power
multiplies 2-x to one. -/
theorem linear_twist {p : ℕ} [Fact p.Prime] (h : p%8=1) :
    ∃ (x : ZMod p) (u : ℕ), ¬IsSquare x ∧ x^(2*u+2)*(2-x)=1 := by
  have hp : p.Prime := Fact.out
  have odd : 2 < p := by have := hp.two_le; omega
  let : NeZero (p-1) := ⟨by omega⟩
  obtain ⟨x,px,nx,z,hz⟩ := primitive_linear_square h
  have sq2 := (ZMod.exists_sq_eq_two_iff (by omega : p≠2)).mpr (Or.inl h)
  have zn : z≠0 := by
    intro z0
    rw [z0,zero_mul] at hz
    exact nx ((sub_eq_zero.mp hz) ▸ sq2)
  obtain ⟨j,_,ij⟩ := px.eq_pow_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one (inv_ne_zero zn))
  have hi : x^(j+(p-1)) = z⁻¹ := by rw [pow_add,px.pow_eq_one,mul_one,ij]
  refine ⟨x,j+(p-1)-1,nx,?_⟩
  rw [show 2*(j+(p-1)-1)+2 = (j+(p-1))*2 by omega,pow_mul,hi,hz]
  field_simp

#print axioms linear_twist
end Hadamard.Arithmetic
