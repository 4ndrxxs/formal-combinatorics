import Quantum.Hadamard.LinPhoaJacobi
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.NumberTheory.MulChar.Duality

/-! Character-basis determinants of the two identical diagonal core Gram blocks. -/

noncomputable section
open Finset Matrix Hadamard.MSXCore Hadamard.NearBorder
namespace Hadamard.LinPhoa

variable {m : ℕ} [NeZero m] {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- A cyclic group matrix diagonal in the character basis has determinant
equal to the product of its character eigenvalues. -/
theorem det_in_characters (A : Matrix (Fin m) (Fin m) ℂ) (s : AddChar (Fin m) ℂ → ℂ)
    (modes : ∀ θ : AddChar (Fin m) ℂ, A.mulVec (θ : Fin m → ℂ)=s θ • (θ : Fin m → ℂ)) :
    A.det=∏ θ, s θ := by
  classical
  let b := AddChar.complexBasis (Fin m)
  have changeBasis : LinearMap.toMatrix b b A.toLin'=diagonal s := by
    ext θ φ
    rw [LinearMap.toMatrix_apply,Matrix.toLin'_apply,show b φ=(φ : Fin m → ℂ) from
      AddChar.complexBasis_apply _,modes]
    rw [←show b φ=(φ : Fin m → ℂ) from AddChar.complexBasis_apply _,map_smul]
    simp [smul_eq_mul,diagonal_apply]
    split_ifs <;> simp_all
  rw [←LinearMap.det_toLin' A,←LinearMap.det_toMatrix b,changeBasis,Matrix.det_diagonal]

def cyclicSymbol (e : Fin m ≃ SquareIndex F) (θ : AddChar (Fin m) ℂ) : ℂ :=
  ∑ l, θ l*eta F ((e l).val-1)

theorem cyclic_difference (e : Fin m ≃ SquareIndex F)
    (cyc : ∀ k l, (e (k-l)).val=(e k).val/(e l).val) (θ : AddChar (Fin m) ℂ) (k : Fin m) :
    (∑ l, eta F ((e l).val-(e k).val)*θ l)=θ k*cyclicSymbol e θ := by
  have nz : (e k).val≠0 := by intro z; have u := (e k).property; rw [z] at u; norm_num at u
  have term (l : Fin m) : eta F ((e l).val-(e k).val)*θ l =
      θ k*(θ (l-k)*eta F ((e (l-k)).val-1)) := by
    have factor : (e l).val-(e k).val=((e (l-k)).val-1)*(e k).val := by
      rw [cyc]; field_simp
    have unit : eta F (e k).val=1 := by change (quadraticChar F (e k).val:ℂ)=1; rw [(e k).property]; norm_num
    have shift : θ l=θ (l-k)*θ k := by rw [←θ.map_add_eq_mul,sub_add_cancel]
    rw [factor,map_mul,unit,mul_one,shift]; ring
  simp only [term,←mul_sum]
  congr 1
  exact (Equiv.subRight k).sum_comp (fun t ↦ θ t*eta F ((e t).val-1))

/-- The cyclic eigenvalue of one row of an old diagonal Gram block. -/
theorem bulk_cyclic_mode (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (w : F) (hw : quadraticChar F w= -1) (i j c a : Bool) (e : Fin m ≃ SquareIndex F)
    (cyc : ∀ k l, (e (k-l)).val=(e k).val/(e l).val) (θ : AddChar (Fin m) ℂ) (k : Fin m) :
    (∑ l, (gram c (sourcePair w i j e) (bulk a k) (bulk a l):ℂ)*θ l)=
      ((Fintype.card F:ℂ)+1-2*(cosetSign i:ℂ)*cyclicSymbol e θ)*θ k := by
  calc
    _ = ((Fintype.card F:ℂ)+1)*θ k - 2*(cosetSign i:ℂ)*
        (∑ l, eta F ((e l).val-(e k).val)*θ l) := by
      have id : ((Fintype.card F:ℂ)+1)*θ k=
          ∑ l, (if k=l then (Fintype.card F:ℂ)+1 else 0)*θ l := by simp [ite_mul]
      rw [id,mul_sum,←sum_sub_distrib]
      apply sum_congr rfl
      intro l _
      rw [bulk_character_entry hc q4 w hw i j c a e cyc k l]
      ring
    _ = _ := by rw [cyclic_difference e cyc θ k]; ring

/-- The exact determinant of an old diagonal Gram block as a product over all
cyclic characters, with the ordinary finite Fourier normalization. -/
theorem bulk_character_product (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (w : F) (hw : quadraticChar F w= -1) (i j c a : Bool) (e : Fin m ≃ SquareIndex F)
    (cyc : ∀ k l, (e (k-l)).val=(e k).val/(e l).val) :
    (((gram c (sourcePair w i j e)).submatrix (bulk a) (bulk a)).map Complex.ofReal).det=
      ∏ θ : AddChar (Fin m) ℂ, ((Fintype.card F:ℂ)+1-2*(cosetSign i:ℂ)*cyclicSymbol e θ) := by
  apply det_in_characters
  intro θ
  funext k
  exact bulk_cyclic_mode hc q4 w hw i j c a e cyc θ k

/-- Eliminate a constant border without inverting the large core matrix. -/
theorem scalar_border_det {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℝ) (U : Matrix I J ℝ) (V : Matrix J I ℝ) (s t n : ℝ) (hs : s≠0)
    (AU : A*U=s • U) (VU : V*U=t • (1 : Matrix J J ℝ)) :
    (fromBlocks A U V (n • (1 : Matrix J J ℝ))).det=A.det*(n-t/s)^Fintype.card J := by
  let T := fromBlocks (1 : Matrix I I ℝ) ((-s⁻¹) • U) (0 : Matrix J I ℝ) (1 : Matrix J J ℝ)
  have dt : T.det=1 := by simp [T]
  have off : (-s⁻¹*s) • U + U=0 := by rw [neg_mul,inv_mul_cancel₀ hs,neg_one_smul,neg_add_cancel]
  have low : (-s⁻¹*t) • (1 : Matrix J J ℝ)+n • (1 : Matrix J J ℝ)=(n-t/s) • 1 := by
    rw [←add_smul]; congr 1; ring
  have mult : fromBlocks A U V (n • (1 : Matrix J J ℝ))*T =
      fromBlocks A (0 : Matrix I J ℝ) V ((n-t/s) • (1 : Matrix J J ℝ)) := by
    simp only [T,fromBlocks_multiply,Matrix.mul_smul,Matrix.mul_one,Matrix.mul_zero,
      AU,VU,smul_smul,add_zero,off,low]
  have d := congrArg Matrix.det mult
  simpa only [det_mul,dt,mul_one,det_fromBlocks_zero₁₂,det_smul,det_one] using d

private def twoClasses (m : ℕ) : Fin m ⊕ Fin m ≃ Core m where
  toFun | .inl k => (false,k) | .inr k => (true,k)
  invFun | (false,k) => .inl k | (true,k) => .inr k
  left_inv x := by cases x <;> rfl
  right_inv x := by obtain ⟨b,k⟩ := x; cases b <;> rfl

private def duplicate (B : Matrix (Fin m) (Fin m) ℝ) : Matrix (Core m) (Core m) ℝ :=
  fun x y ↦ if x.1=y.1 then B x.2 y.2 else 0

omit [NeZero m] in
private theorem duplicate_det (B : Matrix (Fin m) (Fin m) ℝ) : (duplicate B).det=B.det^2 := by
  let f := twoClasses m
  have re : (duplicate B).submatrix f f=fromBlocks B 0 0 B := by
    ext x y; cases x <;> cases y <;> simp [f,twoClasses,duplicate,fromBlocks,submatrix]
  rw [←det_submatrix_equiv_self f (duplicate B),re,det_fromBlocks_zero₁₂,pow_two]

private def spread (D : Matrix Bool Bool ℝ) : Matrix (Core m) Bool ℝ := fun x b ↦ D x.1 b

omit [NeZero m] in
private theorem duplicate_spread (B : Matrix (Fin m) (Fin m) ℝ) (D : Matrix Bool Bool ℝ)
    (s : ℝ) (row : ∀ k, (∑ l,B k l)=s) :
    duplicate B*spread (m:=m) D=s • spread (m:=m) D := by
  ext ⟨a,k⟩ b
  change (∑ y : Core m, (if a=y.1 then B k y.2 else 0)*D y.1 b)=s*D a b
  rw [Fintype.sum_prod_type,Fintype.sum_bool]
  cases a <;> simp [←sum_mul,row]

omit [NeZero m] in
private theorem spread_square (D : Matrix Bool Bool ℝ) (t : ℝ) (norm : D.transpose*D=t • (1 : Matrix Bool Bool ℝ)) :
    (spread (m:=m) D).transpose*spread (m:=m) D=((m:ℝ)*t) • (1 : Matrix Bool Bool ℝ) := by
  ext b c
  have entry := congrFun (congrFun norm b) c
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul] at entry ⊢
  simp only [Fintype.sum_prod_type, spread, sum_const, card_univ, Fintype.card_fin,nsmul_eq_mul,←mul_sum]
  rw [entry]; ring

private theorem zero_symbol (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (e : Fin m ≃ SquareIndex F) : cyclicSymbol e 0= -1 := by
  have h := (sum_by_coords e (fun x : F ↦ quadraticChar F (x-1))).trans (square_shift_sum hc q4)
  simp only [cyclicSymbol,AddChar.zero_apply,one_mul]
  change (∑ l, (quadraticChar F ((e l).val-1):ℂ))= -1
  exact_mod_cast h

private def mixing (r c : ℝ) : Matrix Bool Bool ℝ := fun a b ↦
  (if a then -r*strip b true else r)+(if a=b then 2*c else 0)

private theorem mixing_square (r c : ℝ) :
    (mixing r c).transpose*mixing r c=((r+2*c)^2+r^2) • (1 : Matrix Bool Bool ℝ) := by
  ext a b
  cases a <;> cases b <;> simp [Matrix.mul_apply,mixing,strip] <;> ring

/-- The full determinant in terms of a single circulant determinant,
including its exact correction from the four constant coordinates. -/
theorem core_det_ratio (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (w : F) (hw : quadraticChar F w= -1) (i j c : Bool) (e : Fin m ≃ SquareIndex F)
    (cyc : ∀ k l, (e (k-l)).val=(e k).val/(e l).val) :
    let f := sourcePair w i j e
    let n : ℝ := Fintype.card F+1
    let s := n+2*(cosetSign i:ℝ)
    let r : ℝ := if i then 0 else -2
    s*|(array c f).det|=
      2*((orientation c*r-m)^2+(m:ℝ)^2)*|((gram c f).submatrix (bulk false) (bulk false)).det| := by
  dsimp only
  let f := sourcePair w i j e
  let G := gram c f
  let B := G.submatrix (bulk false) (bulk false)
  let n : ℝ := Fintype.card F+1
  let s := n+2*(cosetSign i:ℝ)
  let r : ℝ := if i then 0 else -2
  let t := (r+2*orientation c)^2+r^2
  let D := mixing r (orientation c)
  have cardq : Fintype.card F=2*m+1 := by
    have h := Fintype.card_congr e
    rw [Fintype.card_fin,square_index_card w hw] at h
    omega
  have order : n=2*(m:ℝ)+2 := by dsimp [n]; rw [cardq]; push_cast; ring
  have hm : (0:ℝ) < m := by exact_mod_cast (NeZero.pos m)
  have hs : 0<s := by
    cases i <;> norm_num [s,cosetSign,order] <;> first | exact NeZero.pos m | linarith
  have rows (k : Fin m) : (∑ l,B k l)=s := by
    have h := bulk_cyclic_mode hc q4 w hw i j c false e cyc 0 k
    simp only [AddChar.zero_apply,mul_one,zero_symbol hc q4 e,mul_neg_one,sub_neg_eq_add] at h
    change ∑ l, G (bulk false k) (bulk false l)=(Fintype.card F:ℝ)+1+2*(cosetSign i:ℝ)
    exact_mod_cast h
  have shared (a : Bool) (k l : Fin m) : G (bulk a k) (bulk a l)=B k l := by
    apply Complex.ofReal_injective
    exact (bulk_character_entry hc q4 w hw i j c a e cyc k l).trans
      (bulk_character_entry hc q4 w hw i j c false e cyc k l).symm
  have sums := source_pair_sums hc q4 w hw i j e
  have mix (a : Bool) (k : Fin m) (b : Bool) : G (bulk a k) (rim b)=D a b :=
    mixed c f r sums.1 sums.2 a b k
  have diag (a : Bool) : G (rim a) (rim a)=n := by
    have h := rim_norm (core f) strip strip (corner c) strip_sign (corner_sign c) a
    change G (rim a) (rim a)=(Fintype.card (Bool × Fin m):ℝ)+2 at h
    rw [h,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,order]; push_cast; ring
  have form : G=fromBlocks (duplicate B) (spread (m:=m) D) (spread (m:=m) D).transpose
      (n • (1 : Matrix Bool Bool ℝ)) := by
    ext x y
    rcases x with ⟨a,k⟩|a <;> rcases y with ⟨b,l⟩|b
    · change G (bulk a k) (bulk b l)=(if a=b then B k l else 0)
      cases a <;> cases b
      · exact shared false k l
      · exact bulk_cross c f _ _
      · exact (gram_sym c f _ _).trans (bulk_cross c f _ _)
      · exact shared true k l
    · exact mix a k b
    · exact (gram_sym c f _ _).trans (mix b l a)
    · change G (rim a) (rim b)=n*(if a=b then 1 else 0)
      cases a <;> cases b <;> norm_num
      · exact diag false
      · exact rim_cross c f
      · exact (gram_sym c f _ _).trans (rim_cross c f)
      · exact diag true
  have reduction := scalar_border_det (duplicate B) (spread (m:=m) D) (spread (m:=m) D).transpose
    s ((m:ℝ)*t) n hs.ne' (duplicate_spread B D s rows) (spread_square D t (mixing_square r (orientation c)))
  rw [←form,duplicate_det,Fintype.card_bool] at reduction
  have sq : (array c f).det^2=(B.det*(n-m*t/s))^2 := by
    simpa only [G,gram,det_mul,det_transpose,pow_two,mul_mul_mul_comm] using reduction
  have magnitudes := (sq_eq_sq_iff_abs_eq_abs _ _).mp sq
  rw [abs_mul] at magnitudes
  have correction : s*(n-m*t/s)=2*((orientation c*r-m)^2+(m:ℝ)^2) := by
    rw [mul_sub,show s*((m:ℝ)*t/s)=(m:ℝ)*t by field_simp]
    cases i <;> cases c <;> simp [s,t,r,orientation,cosetSign,order] <;> ring
  have ac := congrArg abs correction
  have pos : 0≤2*((orientation c*r-m)^2+(m:ℝ)^2) := by positivity
  rw [abs_mul,abs_of_pos hs,abs_of_nonneg pos] at ac
  change s*|(array c f).det|=2*((orientation c*r-m)^2+(m:ℝ)^2)*|B.det|
  rw [magnitudes,←ac]; ring

/-- Exact character product for the determinant of each of the eight arrays. -/
theorem array_character_product (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (w : F) (hw : quadraticChar F w= -1) (i j c : Bool) (e : Fin m ≃ SquareIndex F)
    (cyc : ∀ k l, (e (k-l)).val=(e k).val/(e l).val) :
    ((|(array c (sourcePair w i j e)).det|:ℝ):ℂ)=
      ((2*((orientation c*(if i then 0 else -2)-(m:ℝ))^2+(m:ℝ)^2):ℝ):ℂ)*
      ∏ θ ∈ (univ : Finset (AddChar (Fin m) ℂ)).erase 0,
        ((Fintype.card F:ℂ)+1-2*(cosetSign i:ℂ)*cyclicSymbol e θ) := by
  classical
  let f := sourcePair w i j e
  let B := (gram c f).submatrix (bulk false) (bulk false)
  let s : ℝ := (Fintype.card F:ℝ)+1+2*(cosetSign i:ℝ)
  let P : ℝ := 2*((orientation c*(if i then 0 else -2)-(m:ℝ))^2+(m:ℝ)^2)
  let g (θ : AddChar (Fin m) ℂ) := (Fintype.card F:ℂ)+1-2*(cosetSign i:ℂ)*cyclicSymbol e θ
  have sqF := Fintype.one_lt_card (α:=F)
  have big : 5≤Fintype.card F := by omega
  have bigR : (5:ℝ)≤Fintype.card F := by exact_mod_cast big
  have hs : 0<s := by cases i <;> dsimp [s,cosetSign] <;> push_cast <;> linarith only [bigR]
  have g0 : g 0=(s:ℂ) := by simp [g,s,zero_symbol hc q4 e]
  have detc : (B.det:ℂ)=∏ θ,g θ :=
    (Complex.ofRealHom.map_det B).trans (bulk_character_product hc q4 w hw i j c false e cyc)
  have split := (mul_prod_erase (s:=univ) g (mem_univ (0 : AddChar (Fin m) ℂ)) : _)
  rw [←split,g0] at detc
  have psd : (gram c f).PosSemidef := by simpa [gram] using posSemidef_self_mul_conjTranspose (array c f)
  have nn : 0≤B.det := (psd.submatrix (bulk false)).det_nonneg
  have main : s*|(array c f).det|=P*|B.det| := core_det_ratio hc q4 w hw i j c e cyc
  rw [abs_of_nonneg nn] at main
  change ((|(array c f).det|:ℝ):ℂ)=(P:ℂ)*(∏ θ ∈ univ.erase 0,g θ)
  apply mul_left_cancel₀ (by exact_mod_cast hs.ne' : (s:ℂ)≠0)
  calc
    _ = (P:ℂ)*(B.det:ℂ) := by exact_mod_cast main
    _ = _ := by rw [detc]; ring

/-- Each character of the enumerated squares extends to the multiplicative
group of the entire field, using a complex-valued character. -/
theorem exists_character_lift (e : Fin m ≃ SquareIndex F)
    (cyc : ∀ k l, (e (k-l)).val=(e k).val/(e l).val) (θ : AddChar (Fin m) ℂ) :
    ∃ ψ : MulChar F ℂ, ∀ k, ψ (e k).val=θ k := by
  classical
  let H := squareUnits F
  let E : Fin m ≃ H := e.trans (squareUnitEquiv (F:=F)).symm
  have times (k l : Fin m) : E (k+l)=E k*E l := by
    apply Subtype.ext; apply Units.ext; exact enum_add e cyc k l
  have base : E 0=1 := by
    have z := times 0 0
    rw [zero_add] at z
    calc
      E 0 = (E 0)⁻¹*(E 0*E 0) := by group
      _ = 1 := by rw [←z,inv_mul_cancel]
  let φ : H →* ℂ :=
    { toFun := fun u ↦ θ (E.symm u)
      map_one' := by rw [←base,E.symm_apply_apply,θ.map_zero_eq_one]
      map_mul' := by
        intro x y
        obtain ⟨a,rfl⟩ := E.surjective x
        obtain ⟨b,rfl⟩ := E.surjective y
        rw [←times,E.symm_apply_apply,E.symm_apply_apply,E.symm_apply_apply,θ.map_add_eq_mul] }
  obtain ⟨Ψ,agree⟩ := MonoidHom.domRestrict_surjective (G:=Fˣ) ℂ H φ.toHomUnits
  refine ⟨MulChar.ofUnitHom Ψ,?_⟩
  intro k
  have h := congrArg (fun v : H →* ℂˣ ↦ ((v (E k)):ℂ)) agree
  change (((Ψ (E k).val):ℂˣ):ℂ)=(φ (E k)) at h
  change MulChar.ofUnitHom Ψ ((E k).val:F)=_
  rw [MulChar.ofUnitHom_coe,h]
  change θ (E.symm (E k))=θ k
  rw [E.symm_apply_apply]

/-- Exact paired-Jacobi product with no absolute value around the complex
product. The choice of an extension of each cyclic character is arbitrary. -/
theorem array_jacobi_product (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (w : F) (hw : quadraticChar F w= -1) (i j c : Bool) (e : Fin m ≃ SquareIndex F)
    (cyc : ∀ k l, (e (k-l)).val=(e k).val/(e l).val)
    (ψ : AddChar (Fin m) ℂ → MulChar F ℂ) (extendsOn : ∀ θ k, ψ θ (e k).val=θ k) :
    ((|(array c (sourcePair w i j e)).det|:ℝ):ℂ)=
      ((2*((orientation c*(if i then 0 else -2)-(m:ℝ))^2+(m:ℝ)^2):ℝ):ℂ)*
      ∏ θ ∈ (univ : Finset (AddChar (Fin m) ℂ)).erase 0,
        ((Fintype.card F:ℂ)+1-(cosetSign i:ℂ)*
          (jacobiSum (ψ θ) (eta F)+jacobiSum (ψ θ*eta F) (eta F))) := by
  rw [array_character_product hc q4 w hw i j c e cyc]
  congr 1
  apply prod_congr rfl
  intro θ _
  have eq : cyclicSymbol e θ=squareFourier (ψ θ) := by
    rw [←fourier_by_enumeration (ψ θ) e]
    simp only [cyclicSymbol,extendsOn]
  rw [eq,←square_fourier_jacobi q4 (ψ θ)]; ring

/-- The complete formula with the lifts constructed rather than supplied. -/
theorem exists_jacobi_products (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (w : F) (hw : quadraticChar F w= -1) (e : Fin m ≃ SquareIndex F)
    (cyc : ∀ k l, (e (k-l)).val=(e k).val/(e l).val) :
    ∃ ψ : AddChar (Fin m) ℂ → MulChar F ℂ, (∀ θ k, ψ θ (e k).val=θ k) ∧
      ∀ i j c : Bool, ((|(array c (sourcePair w i j e)).det|:ℝ):ℂ)=
        ((2*((orientation c*(if i then 0 else -2)-(m:ℝ))^2+(m:ℝ)^2):ℝ):ℂ)*
        ∏ θ ∈ (univ : Finset (AddChar (Fin m) ℂ)).erase 0,
          ((Fintype.card F:ℂ)+1-(cosetSign i:ℂ)*
            (jacobiSum (ψ θ) (eta F)+jacobiSum (ψ θ*eta F) (eta F))) := by
  choose ψ ok using exists_character_lift e cyc
  exact ⟨ψ,ok,fun i j c ↦ array_jacobi_product hc q4 w hw i j c e cyc ψ ok⟩

#print axioms exists_character_lift
#print axioms array_jacobi_product
#print axioms exists_jacobi_products
#print axioms array_character_product
#print axioms core_det_ratio
#print axioms scalar_border_det
#print axioms det_in_characters
#print axioms cyclic_difference
#print axioms bulk_character_product

end Hadamard.LinPhoa
