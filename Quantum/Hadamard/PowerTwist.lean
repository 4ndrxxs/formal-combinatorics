import Quantum.Hadamard.PowerResidues

/-! An elementary linear-twist witness at every power of a prime one modulo eight. -/
noncomputable section
namespace Hadamard.Arithmetic.PowerResidues
variable {p a : ℕ} [Fact p.Prime]

private theorem power_generator {G : Type} [CommGroup G] [Finite G] {g:G}
    (gen : ∀ z, ∃ k:ℕ, g^k=z) (big : 1<Nat.card G) {u:ℕ} (cop:u.Coprime (Nat.card G)) :
    ∀ z, ∃ k:ℕ, (g^u)^k=z := by
  obtain ⟨i,_,hi⟩ := Nat.exists_mul_mod_eq_one_of_coprime cop big
  have congr : u*i ≡ 1 [MOD Nat.card G] := by simpa [Nat.ModEq,Nat.mod_eq_of_lt big] using hi
  have gi : g^(u*i)=g := by
    simpa using (pow_eq_pow_iff_modEq (x:=g)).mpr (congr.of_dvd (orderOf_dvd_iff_pow_eq_one.mpr pow_card_eq_one'))
  intro z
  obtain ⟨k,hk⟩ := gen z
  exact ⟨i*k,by rw [pow_mul (g^u) i k,←pow_mul g u i,gi,hk]⟩

theorem twist {p : ℕ} [Fact p.Prime] (a : ℕ) (one : p%8=1) :
    ∃ (x : (ZMod (p^(a+1)))ˣ) (u : ℕ),
      ¬IsSquare (red p a (x:ZMod (p^(a+1)))) ∧
      IsUnit ((x:ZMod (p^(a+1)))-1) ∧
      (x:ZMod (p^(a+1)))^(2*u+2)*(2-x)=1 := by
  have hp : p.Prime := Fact.out
  have po : 2<p := by have := hp.two_le; omega
  let M := p^(a+1)
  let G := (ZMod M)ˣ
  letI : NeZero M := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : IsCyclic G := ZMod.isCyclic_units_of_prime_pow p hp (by omega) _
  let N := Nat.card G
  have card : N=p^a*(p-1) := by
    rw [show N=Nat.card (ZMod (p^(a+1)))ˣ from rfl,Nat.card_eq_fintype_card,ZMod.card_units_eq_totient,
      Nat.totient_prime_pow_succ hp]
  have big : 1<N := by rw [card]; have := pow_pos hp.pos a; nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ p)]
  obtain ⟨g,gg⟩ := IsCyclic.exists_monoid_generator (α:=G)
  have gen (z:G) : ∃ k:ℕ, g^k=z := (Submonoid.mem_powers_iff _ _).mp (gg z)
  have twou : IsUnit (2:ZMod M) := by
    simpa [M] using (ZMod.isUnit_iff_coprime 2 M).mpr ((two_coprime_prime hp po).pow_right (a+1))
  obtain ⟨k,kg⟩ := gen twou.unit
  obtain ⟨i,j,w,ci,cj,ij⟩ := even_sum_units big (show Even (2*k) from ⟨k,by omega⟩)
  let x := g^i
  let y := g^j
  have gx : ∀ z:G, ∃ t:ℕ, x^t=z := power_generator gen big ci
  have gy : ∀ z:G, ∃ t:ℕ, y^t=z := power_generator gen big cj
  have nx := red_generator_nonsquare po gx
  have ny := red_generator_nonsquare po gy
  have per : g^N=1 := pow_card_eq_one'
  have four : x*y=twou.unit^2 := by
    dsimp [x,y]
    rw [←pow_add,ij,pow_add,Nat.mul_comm w N,pow_mul g N w,per,one_pow,mul_one,Nat.mul_comm 2 k,pow_mul,kg]
  let f := red p a
  have xy : f (x:ZMod M)*f (y:ZMod M)=4 := by
    have eq := congrArg (fun t:G => f (t:ZMod M)) four
    change f ((x:ZMod M)*(y:ZMod M))=f ((twou.unit:ZMod M)^2) at eq
    rw [map_mul,twou.unit_spec] at eq
    rw [map_pow,map_ofNat] at eq
    norm_num at eq ⊢
    exact eq
  have sq2 := (ZMod.exists_sq_eq_two_iff (by omega : p≠2)).mpr (Or.inl one)
  have neg2 := (ZMod.exists_sq_eq_neg_two_iff (by omega : p≠2)).mpr (Or.inl one)
  have nz2 : (2:ZMod p)≠0 := by
    intro h
    exact (Nat.not_dvd_of_pos_of_lt (by decide) po) ((ZMod.natCast_eq_zero_iff 2 _).mp h)
  have choose : ∃ z:G, (∀ t:G,∃ e:ℕ, z^e=t) ∧ ¬IsSquare (f (z:ZMod M)) ∧ IsSquare (2-f (z:ZMod M)) := by
    by_cases s : IsSquare (2-f (x:ZMod M))
    · exact ⟨x,gx,nx,s⟩
    have nz : 2-f (y:ZMod M)≠0 := by intro h; exact ny ((sub_eq_zero.mp h) ▸ sq2)
    have iden : (2-f (y:ZMod M))*f (x:ZMod M)=(-2)*(2-f (x:ZMod M)) := by linear_combination -xy
    have hc := congrArg (quadraticChar (ZMod p)) iden
    rw [map_mul,map_mul,quadraticChar_neg_one_iff_not_isSquare.mpr nx,
      (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr nz2)).mpr neg2,
      quadraticChar_neg_one_iff_not_isSquare.mpr s] at hc
    exact ⟨y,gy,ny,(quadraticChar_one_iff_isSquare nz).mp (by omega)⟩
  obtain ⟨z,gz,zn,sq⟩ := choose
  have nz : 2-f (z:ZMod M)≠0 := by intro h; exact zn ((sub_eq_zero.mp h) ▸ sq2)
  have sc : IsSquare (f (2-(z:ZMod M))) := by simpa only [map_sub,map_ofNat] using sq
  have zu : IsUnit (2-(z:ZMod M)) := unit_of_red (by simpa only [map_sub,map_ofNat] using nz)
  obtain ⟨v,hv⟩ := square_of_red po zu sc
  have vu : IsUnit v := isUnit_of_mul_isUnit_left (hv ▸ zu : IsUnit (v*v))
  obtain ⟨t,ht⟩ := gz vu.unit⁻¹
  have t2 : (z:ZMod M)^(t+N)=(↑vu.unit⁻¹:ZMod M) := by
    have H : z^(t+N)=vu.unit⁻¹ := by rw [pow_add,show z^N=1 from pow_card_eq_one',mul_one,ht]
    exact congrArg Units.val H
  refine ⟨z,t+N-1,zn,unit_of_red ?_,?_⟩
  · intro h
    have z1 : f (z:ZMod M)=1 := sub_eq_zero.mp (by simpa [f] using h)
    exact zn (z1 ▸ ⟨1,by simp⟩)
  · rw [show 2*(t+N-1)+2=(t+N)*2 by omega,pow_mul,t2,hv]
    have vv : (↑vu.unit⁻¹:ZMod M)*v=1 := calc
      _ = (↑vu.unit⁻¹:ZMod M)*↑vu.unit := congrArg ((↑vu.unit⁻¹:ZMod M)*·) vu.unit_spec.symm
      _ = 1 := by simp
    linear_combination ((↑vu.unit⁻¹:ZMod M)*v+1)*vv

#print axioms twist
end Hadamard.Arithmetic.PowerResidues
