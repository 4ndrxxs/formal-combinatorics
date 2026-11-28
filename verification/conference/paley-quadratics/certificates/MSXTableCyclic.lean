import Quantum.Hadamard.NonsplitCharacterProduct

/-! The cyclic parameters in row (4) of Momihara–Suda–Xiang, Table 1.6. -/

noncomputable section
open Hadamard.LinPhoa
namespace Hadamard.NonsplitTorus.MSXTable

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {d : F} [Fact (¬ IsSquare d)]

noncomputable local instance (d : F) : Fintype (Ext d) :=
  Fintype.ofEquiv (F × F) (QuadraticAlgebra.equivProd d 0).symm

noncomputable local instance (h : (Ext d)ˣ) : NeZero (orderOf h) :=
  ⟨(orderOf_pos h).ne'⟩

/-- The generator of the odd norm-one subgroup, as a power of a primitive element. -/
def torusGen (ω : (Ext d)ˣ) : (Ext d)ˣ := ω ^ (2 * (Fintype.card F - 1))

/-- The trace-zero point used to normalize the quartic phase. -/
def phasePoint (ω : (Ext d)ˣ) : Ext d := (ω : Ext d) ^ ((Fintype.card F + 1) / 2)

omit [DecidableEq F] [Fact (¬ IsSquare d)] in
private theorem ext_card : Fintype.card (Ext d) = (Fintype.card F)^2 := by
  simpa only [Fintype.card_prod, pow_two] using Fintype.card_congr (QuadraticAlgebra.equivProd d 0)

private theorem unit_card : Nat.card (Ext d)ˣ = (Fintype.card F - 1) * (Fintype.card F + 1) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_units, ext_card]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := F))
  rw [hn]
  simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
  exact Nat.sub_eq_of_eq_add (by ring)

private theorem generator_zpowers {K : Type*} [Group K] [Finite K] {g : K}
    (hg : orderOf g = Nat.card K) (x : K) : x ∈ Subgroup.zpowers g := by
  have top : Subgroup.zpowers g = ⊤ :=
    (Subgroup.zpowers g).eq_top_of_card_eq ((Nat.card_zpowers g).trans hg)
  rw [top]
  exact Subgroup.mem_top x

private theorem eval_order {K : Type*} [Field K] [Finite K] (χ : MulChar K ℂ)
    (g : Kˣ) (hg : orderOf g = Nat.card Kˣ) : orderOf (χ (g : K)) = orderOf χ := by
  apply orderOf_eq_orderOf_iff.mpr
  intro n
  rw [MulChar.eq_iff (generator_zpowers hg) (χ^n) 1, MulChar.pow_apply_coe, MulChar.one_apply_coe]

private theorem half_coprime (q : ℕ) (q4 : q % 4 = 1) :
    ((q+1)/2).Coprime (2*(q-1)) := by
  let t := q/4
  have v : (q+1)/2=2*t+1 := by dsimp [t]; omega
  have m : 2*(q-1)=4*(2*t) := by dsimp [t]; omega
  have odd : Odd (2*t+1) := ⟨t, rfl⟩
  rw [v,m,show 4=(2:ℕ)*2 by decide]
  apply Nat.Coprime.mul_right
  · exact odd.coprime_two_right.mul_right odd.coprime_two_right
  · exact Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _)

theorem torusGen_order (q4 : Fintype.card F % 4 = 1) (ω : (Ext d)ˣ)
    (hω : orderOf ω = Nat.card (Ext d)ˣ) :
    orderOf (torusGen ω) = (Fintype.card F+1)/2 := by
  let q := Fintype.card F
  have qpos : 1 < q := Fintype.one_lt_card
  have full : orderOf ω = (2*(q-1))*((q+1)/2) := by
    rw [hω,unit_card]
    change (q-1)*(q+1) = (2*(q-1))*((q+1)/2)
    have two : 2*((q+1)/2)=q+1 := by dsimp [q] at *; omega
    rw [mul_comm 2 (q-1),mul_assoc,two]
  have pos : 0<2*(q-1) := by omega
  change orderOf (ω^(2*(q-1)))=_
  rw [orderOf_pow_of_dvd pos.ne' (by rw [full]; exact dvd_mul_right ..),full,
      Nat.mul_div_cancel_left _ pos]

omit [DecidableEq F] in
theorem torusGen_norm (ω : (Ext d)ˣ) : (torusGen ω : Ext d).norm = 1 := by
  have nz : (ω : Ext d).norm ≠ 0 :=
    fun e ↦ ω.ne_zero (QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp e)
  change QuadraticAlgebra.norm ((ω : Ext d)^(2*(Fintype.card F-1)))=1
  rw [map_pow, mul_comm 2, pow_mul, FiniteField.pow_card_sub_one_eq_one _ nz, one_pow]

/-- Restrict the indicated power of a multiplicative character to the cyclic index. -/
def torusMode (h : (Ext d)ˣ) (ν : MulChar (Ext d) ℂ) (j : ℕ) :
    AddChar (Fin (orderOf h)) ℂ where
  toFun i := (ν (spin h i)) ^ j
  map_zero_eq_one' := by simp [spin]
  map_add_eq_mul' i k := by
    have p : h^(i+k).val = h^i.val*h^k.val := by rw [Fin.val_add,pow_mod_orderOf,pow_add]
    have sp : spin h (i+k) = spin h i * spin h k :=
      congrArg Units.val p
    rw [sp,map_mul,mul_pow]

/-- All the torus characters appear exactly once among the powers of a character of order
`(q+1)/2` of the quadratic extension. -/
def modeEquiv (q4 : Fintype.card F%4=1) (ω : (Ext d)ˣ)
    (hω : orderOf ω = Nat.card (Ext d)ˣ) (ν : MulChar (Ext d) ℂ)
    (hν : orderOf ν = (Fintype.card F+1)/2) :
    Fin ((Fintype.card F+1)/2) ≃ AddChar (Fin (orderOf (torusGen ω))) ℂ := by
  classical
  let h := torusGen ω
  have ho : orderOf h = (Fintype.card F+1)/2 := torusGen_order q4 ω hω
  have vo : orderOf (ν (ω : Ext d)) = (Fintype.card F+1)/2 := (eval_order ν ω hω).trans hν
  have cop : (orderOf (ν (ω : Ext d))).Coprime (2*(Fintype.card F-1)) := by
    rw [vo]; exact half_coprime _ q4
  have valo : orderOf (ν (h : Ext d)) = (Fintype.card F+1)/2 := by
    change orderOf (ν ((ω : Ext d)^(2*(Fintype.card F-1))))=_
    rw [map_pow,cop.orderOf_pow,vo]
  refine Equiv.ofBijective (fun j ↦ torusMode h ν j.val) ?_
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro a b eqn
    have qpos := Fintype.one_lt_card (α:=F)
    let i : Fin (orderOf h) := ⟨1, by omega⟩
    have ev := congrArg (fun θ : AddChar (Fin (orderOf h)) ℂ ↦ θ i) eqn
    change (ν ((h : Ext d)^1))^a.val = (ν ((h : Ext d)^1))^b.val at ev
    rw [pow_one] at ev
    exact Fin.ext (pow_injOn_Iio_orderOf (x:=ν (h : Ext d)) (by change a.val < _; rw [valo]; exact a.isLt) (by change b.val < _; rw [valo]; exact b.isLt) ev)
  · simpa only [AddChar.card_eq,Fintype.card_fin] using ho.symm

@[simp] theorem modeEquiv_apply (q4 : Fintype.card F%4=1) (ω : (Ext d)ˣ)
    (hω : orderOf ω = Nat.card (Ext d)ˣ) (ν : MulChar (Ext d) ℂ)
    (hν : orderOf ν = (Fintype.card F+1)/2) (j : Fin ((Fintype.card F+1)/2))
    (i : Fin (orderOf (torusGen ω))) :
    modeEquiv q4 ω hω ν hν j i = (ν (spin (torusGen ω) i))^j.val := rfl

omit [DecidableEq F] in
private theorem char_ne_two (q4 : Fintype.card F%4=1) : ringChar F ≠ 2 := by
  intro h
  have e := FiniteField.even_card_of_char_two h
  omega

private theorem chars_on_generator {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (hc : ringChar K ≠ 2) (g : Kˣ) (hg : orderOf g = Nat.card Kˣ) :
    eta K (g : K) = -1 := by
  have ne : quadraticChar K (g : K) ≠ 1 := by
    intro e
    apply quadraticChar_ne_one hc
    apply (MulChar.eq_iff (generator_zpowers hg) _ _).mpr
    simpa only [MulChar.one_apply_coe] using e
  change (quadraticChar K (g : K) : ℂ) = -1
  rw [(quadraticChar_dichotomy g.ne_zero).resolve_left ne, Int.cast_neg, Int.cast_one]

private theorem quartic_at_generator {K : Type*} [Field K] [Finite K]
    (g : Kˣ) (hg : orderOf g = Nat.card Kˣ) (τ : MulChar K ℂ) (hτ : orderOf τ = 4) :
    (τ (g : K))^2 = -1 := by
  have o : orderOf (τ (g : K)) = 4 := (eval_order τ g hg).trans hτ
  apply (CharP.orderOf_eq_two_iff 0 (by decide)).mp
  rw [orderOf_pow_of_dvd (by decide : (2:ℕ)≠0) (by rw [o]; decide),o]

/-- The square of either quartic character is the quadratic character of the extension. -/
theorem quartic_square (q4 : Fintype.card F%4=1) (ω : (Ext d)ˣ)
    (hω : orderOf ω = Nat.card (Ext d)ˣ) (τ : MulChar (Ext d) ℂ) (hτ : orderOf τ = 4) :
    τ^2 = eta (Ext d) := by
  have hc : ringChar (Ext d) ≠ 2 := by rw [← Algebra.ringChar_eq F (Ext d)]; exact char_ne_two q4
  apply (MulChar.eq_iff (generator_zpowers hω) _ _).mpr
  rw [MulChar.pow_apply_coe, quartic_at_generator ω hω τ hτ, chars_on_generator hc ω hω]

omit [DecidableEq F] [Fact (¬ IsSquare d)] in
/-- The order-`v` character is trivial at the trace-zero phase point. -/
theorem indexChar_phase (ω : (Ext d)ˣ) (ν : MulChar (Ext d) ℂ)
    (hν : orderOf ν = (Fintype.card F+1)/2) : ν (phasePoint ω) = 1 := by
  change ν ((ω : Ext d)^((Fintype.card F+1)/2))=1
  rw [map_pow, ← hν, ← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe]

omit [DecidableEq F] [Fact (¬ IsSquare d)] in
/-- The order-`v` character restricts trivially to nonzero base-field scalars. -/
theorem indexChar_base (q4 : Fintype.card F%4=1) (ν : MulChar (Ext d) ℂ)
    (hν : orderOf ν = (Fintype.card F+1)/2) (s : Fˣ) :
    ν (algebraMap F (Ext d) (s:F)) = 1 := by
  let u : (Ext d)ˣ := Units.map (algebraMap F (Ext d)).toMonoidHom s
  have p : (ν (u : Ext d)) ^ ((Fintype.card F+1)/2) = 1 := by
    rw [← hν, ← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe]
  have r : (ν (u : Ext d))^(Fintype.card F-1) = 1 := by
    change (ν (algebraMap F (Ext d) (s:F)))^(Fintype.card F-1)=1
    rw [← map_pow, ← map_pow, FiniteField.pow_card_sub_one_eq_one _ s.ne_zero, map_one, map_one]
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    ((half_coprime _ q4).of_dvd_right (dvd_mul_left _ 2))
    (orderOf_dvd_of_pow_eq_one p) (orderOf_dvd_of_pow_eq_one r))

/-- Frobenius on the quadratic model agrees with the coordinate involution. -/
theorem pow_card_eq_star (q4 : Fintype.card F%4=1) (z : Ext d) :
    z^(Fintype.card F) = star z := by
  let root : Ext d := QuadraticAlgebra.omega
  have ns : quadraticChar F d = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr Fact.out
  have half : d^(Fintype.card F/2) = -1 := by
    rw [← quadraticChar_eq_pow_of_char_ne_two' (char_ne_two q4), ns, Int.cast_neg, Int.cast_one]
  have rootSq : root^2 = algebraMap F (Ext d) d := by
    rw [pow_two]; simpa [root] using (QuadraticAlgebra.omega_mul_omega_eq_algebraMap (R:=F) (a:=d) (b:=0))
  have starRoot : star root = -root := by
    apply QuadraticAlgebra.ext <;> simp [root,QuadraticAlgebra.re_star,QuadraticAlgebra.im_star]
  have hom : FiniteField.frobeniusAlgHom F (Ext d) =
      (QuadraticAlgebra.starAlgEquiv : Ext d ≃ₐ[F] Ext d).toAlgHom := by
    apply QuadraticAlgebra.algHom_ext
    change root^(Fintype.card F) = star root
    calc
      _ = root^(2*(Fintype.card F/2)+1) := congrArg (root^·) (by omega)
      _ = -root := by rw [pow_succ,pow_mul,rootSq,← map_pow,half,map_neg,map_one,neg_one_mul]
      _ = _ := starRoot.symm
  exact DFunLike.congr_fun hom z

/-- The base norm of a primitive element is its `(q+1)`st power. -/
theorem norm_eq_pow (q4 : Fintype.card F%4=1) (z : Ext d) :
    algebraMap F (Ext d) z.norm = z^(Fintype.card F+1) := by
  rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star, ← pow_card_eq_star q4, pow_succ, mul_comm]

private theorem norm_unit_order (q4 : Fintype.card F%4=1) (ω : (Ext d)ˣ)
    (hω : orderOf ω = Nat.card (Ext d)ˣ)
    (u : Fˣ) (hu : (u:F) = (ω : Ext d).norm) : orderOf u = Nat.card Fˣ := by
  have emb := orderOf_injective (algebraMap F (Ext d)).toMonoidHom
    (algebraMap F (Ext d)).injective (u:F)
  change orderOf (algebraMap F (Ext d) (u:F)) = orderOf (u:F) at emb
  have full : orderOf (ω : Ext d) = (Fintype.card F-1)*(Fintype.card F+1) := by
    rw [orderOf_units,hω,unit_card]
  have dv : Fintype.card F+1 ∣ orderOf (ω : Ext d) := by rw [full]; exact dvd_mul_left ..
  rw [← orderOf_units (y:=u), ← emb, hu, norm_eq_pow q4,
    orderOf_pow_of_dvd (by omega : Fintype.card F+1≠0) dv, full,
    Nat.mul_div_cancel _ (by omega : 0<Fintype.card F+1), Nat.card_eq_fintype_card, Fintype.card_units]

/-- A quartic character on the quadratic field restricts to the quadratic character on the base. -/
theorem quartic_base (q4 : Fintype.card F%4=1) (ω : (Ext d)ˣ)
    (hω : orderOf ω = Nat.card (Ext d)ˣ) (τ : MulChar (Ext d) ℂ) (hτ : orderOf τ = 4)
    (s : F) : τ (algebraMap F (Ext d) s) = eta F s := by
  have nz : (ω : Ext d).norm ≠ 0 :=
    fun e ↦ ω.ne_zero (QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp e)
  let b : Fˣ := Units.mk0 (ω : Ext d).norm nz
  have bo : orderOf b = Nat.card Fˣ := norm_unit_order q4 ω hω b rfl
  have bval : τ (algebraMap F (Ext d) (b:F)) = eta F (b:F) := by
    rw [chars_on_generator (char_ne_two q4) b bo]
    change τ (algebraMap F (Ext d) (ω : Ext d).norm) = -1
    have odd : Odd ((Fintype.card F+1)/2) := ⟨Fintype.card F/4, by omega⟩
    rw [norm_eq_pow q4,map_pow,show Fintype.card F+1 = 2*((Fintype.card F+1)/2) by omega,
      pow_mul,quartic_at_generator ω hω τ hτ,odd.neg_one_pow]
  by_cases hs : s = 0
  · subst s; simp [MulChar.map_zero]
  · let u := Units.mk0 s hs
    obtain ⟨n, hn⟩ := mem_powers_iff_mem_zpowers.mpr (generator_zpowers bo u)
    have es : (b:F)^n = s := congrArg Units.val hn
    rw [← es,map_pow,map_pow,map_pow,bval]

/-- The real coordinate of the table's distinguished power of the generator vanishes. -/
theorem phasePoint_re (q4 : Fintype.card F%4=1) (ω : (Ext d)ˣ)
    (hω : orderOf ω = Nat.card (Ext d)ˣ) : (phasePoint ω).re = 0 := by
  let q := Fintype.card F
  let v := (q+1)/2
  have qpos : 1 < q := Fintype.one_lt_card
  have two : 2*v=q+1 := by dsimp [q,v]; omega
  have full : orderOf (ω : Ext d) = (v*(q-1))*2 := by
    rw [orderOf_units,hω,unit_card]
    change (q-1)*(q+1) = (v*(q-1))*2
    rw [← two]; ring
  have vp : 0<v*(q-1) := Nat.mul_pos (by dsimp [v]; omega) (by omega)
  have div : v*(q-1) ∣ orderOf (ω : Ext d) := by rw [full]; exact dvd_mul_right ..
  have op : orderOf ((phasePoint ω)^(q-1)) = 2 := by
    change orderOf (((ω : Ext d)^v)^(q-1)) = 2
    rw [← pow_mul,orderOf_pow_of_dvd vp.ne' div,full,Nat.mul_div_cancel_left _ vp]
  have hc : ringChar (Ext d) ≠ 2 := by rw [← Algebra.ringChar_eq F (Ext d)]; exact char_ne_two q4
  have minus : (phasePoint ω)^(q-1) = -1 :=
    (CharP.orderOf_eq_two_iff (ringChar (Ext d)) hc).mp op
  have flip : star (phasePoint ω) = -(phasePoint ω) := by
    rw [← pow_card_eq_star q4]
    change (phasePoint ω)^q = _
    calc
      _ = (phasePoint ω)^(q-1+1) := congrArg ((phasePoint ω)^·) (by omega)
      _ = _ := by rw [pow_succ,minus,neg_one_mul]
  have re := congrArg QuadraticAlgebra.re flip
  simp only [QuadraticAlgebra.re_star,zero_mul,add_zero,QuadraticAlgebra.re_neg] at re
  have eqn : (2:F)*(phasePoint ω).re=0 := by linear_combination re
  exact (mul_eq_zero.mp eqn).resolve_left (Ring.two_ne_zero (char_ne_two q4))

/-- The trace-zero point has the imaginary coordinate as its nonzero scalar on the root line. -/
theorem phasePoint_eq_offset (q4 : Fintype.card F%4=1) (ω : (Ext d)ˣ)
    (hω : orderOf ω = Nat.card (Ext d)ˣ) :
    (phasePoint ω).im ≠ 0 ∧
      phasePoint ω = algebraMap F (Ext d) (phasePoint ω).im * offset d true := by
  have re := phasePoint_re q4 ω hω
  constructor
  · intro eqn
    exact pow_ne_zero _ ω.ne_zero (QuadraticAlgebra.ext re eqn : phasePoint ω = 0)
  · apply QuadraticAlgebra.ext <;>
      simp [re,offset,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul]

/-- The standard `2√d` and the table's `ω^v` differ by a nonzero base scalar. -/
theorem phasePoint_coordinate (q4 : Fintype.card F%4=1) (ω : (Ext d)ˣ)
    (hω : orderOf ω = Nat.card (Ext d)ˣ) :
    ∃ k : Fˣ, twiceRoot d = algebraMap F (Ext d) (k:F) * phasePoint ω := by
  have re := phasePoint_re q4 ω hω
  have im := (phasePoint_eq_offset q4 ω hω).1
  let k := Units.mk0 (2/(phasePoint ω).im) (div_ne_zero (Ring.two_ne_zero (char_ne_two q4)) im)
  refine ⟨k, ?_⟩
  apply QuadraticAlgebra.ext <;>
    simp [twiceRoot,offset,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,re,k]
  field_simp [im]

/-- The multiplicative generator, quartic character and order-`v` character always exist. -/
theorem exists_parameters (q4 : Fintype.card F%4=1) :
    ∃ (ω : (Ext d)ˣ) (τ ν : MulChar (Ext d) ℂ),
      orderOf ω = Nat.card (Ext d)ˣ ∧ orderOf τ = 4 ∧ orderOf ν = (Fintype.card F+1)/2 := by
  obtain ⟨ω,hω⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic (Ext d)ˣ)
  let e := (MulChar.mulEquiv_units (Ext d) ℂ).some
  have dv : 4 ∣ orderOf ω := by
    rw [hω,unit_card]
    exact dvd_mul_of_dvd_left (show 4 ∣ Fintype.card F-1 from ⟨Fintype.card F/4, by omega⟩) _
  refine ⟨ω,e.symm (ω^(orderOf ω/4)),e.symm (torusGen ω),hω,?_,?_⟩
  · rw [e.symm.orderOf_eq,orderOf_pow_orderOf_div (orderOf_pos ω).ne' dv]
  · rw [e.symm.orderOf_eq,torusGen_order q4 ω hω]

omit [DecidableEq F] [Fact (¬ IsSquare d)] in
/-- The quartic character is trivial throughout the odd norm-one subgroup. -/
theorem quartic_spin (q4 : Fintype.card F%4=1) (ω : (Ext d)ˣ)
    (τ : MulChar (Ext d) ℂ) (hτ : orderOf τ = 4) (i : Fin (orderOf (torusGen ω))) :
    τ (spin (torusGen ω) i) = 1 := by
  have period : τ^(2*(Fintype.card F-1))=1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by rw [hτ]; exact ⟨(Fintype.card F-1)/2, by omega⟩)
  have base : τ (torusGen ω : Ext d) = 1 := by
    change τ ((ω : Ext d)^(2*(Fintype.card F-1)))=1
    rw [map_pow, ← MulChar.pow_apply_coe, period, MulChar.one_apply_coe]
  rw [spin,map_pow,base,one_pow]

/-- Evaluation as a power of the character, including the trivial exponent `j=0`. -/
theorem modeEquiv_pow_apply (q4 : Fintype.card F%4=1) (ω : (Ext d)ˣ)
    (hω : orderOf ω = Nat.card (Ext d)ˣ) (ν : MulChar (Ext d) ℂ)
    (hν : orderOf ν = (Fintype.card F+1)/2) (j : Fin ((Fintype.card F+1)/2))
    (i : Fin (orderOf (torusGen ω))) :
    (ν^j.val) (spin (torusGen ω) i) = modeEquiv q4 ω hω ν hν j i :=
  MulChar.pow_apply_coe ν j.val ((torusGen ω)^i.val)

#print axioms torusGen_order
#print axioms torusGen_norm
#print axioms modeEquiv
#print axioms modeEquiv_pow_apply
#print axioms quartic_square
#print axioms quartic_base
#print axioms quartic_spin
#print axioms indexChar_base
#print axioms indexChar_phase
#print axioms phasePoint_coordinate
#print axioms exists_parameters

end Hadamard.NonsplitTorus.MSXTable
