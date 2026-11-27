module
public import Quantum.RealHypercubeBases

/-! Maximal real quantum Latin hypercubes of every order at least four,
with no restriction on the number of axes. -/
@[expose] public section
noncomputable section
namespace RealHypercubes

open Complex Finset MaximalHypercubes
open scoped ComplexConjugate BigOperators

abbrev RSpace (q : ℕ) := EuclideanSpace ℝ (Fin q)

def lift {q : ℕ} (v : RSpace q) : Space q :=
  WithLp.toLp 2 (fun k => (v k : ℂ))

theorem inner_lift {q : ℕ} (u v : RSpace q) :
    inner ℂ (lift u) (lift v) = (inner ℝ u v : ℂ) := by
  rw [PiLp.inner_apply,PiLp.inner_apply]
  change (∑ k, (v k : ℂ)*conj (u k : ℂ)) = ((∑ k,v k*u k : ℝ):ℂ)
  simp

/-- The Gram matrix is real on the quaternionic form. Coordinates in one fixed
orthonormal basis of that form therefore lie in real Euclidean space. -/
theorem maximal_real_hypercubes (q d : ℕ) (hq : 4 ≤ q) :
    ∃ (v : (Fin d → Fin q) → EuclideanSpace ℝ (Fin q)) (nz : ∀ a, v a ≠ 0),
      (∀ (k : Fin d) a, ∃ b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)),
        ⇑b = fun x => v (Function.update a k x)) ∧
      (Set.range (fun a => Projectivization.mk ℝ (v a) (nz a))).ncard = q^d := by
  classical
  obtain ⟨r,rfl⟩ : ∃ r, q=r+4 := ⟨q-4,by omega⟩
  obtain ⟨F⟩ := frame_exists r
  obtain ⟨p,hp,hs⟩ := frame_words F d
  have ho : Orthonormal ℂ (fun i => vector (F.basis i)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [vector_gram,F.gram]
    split <;> simp only [inv_mul_cancel₀ (order_ne r),mul_zero]
  let B := OrthonormalBasis.mk ho
    (ho.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)).ge
  have hB : ⇑B = fun i => vector (F.basis i) := OrthonormalBasis.coe_mk _ _
  let w (a : Grid (r+4) d) : RSpace (r+4) :=
    WithLp.toLp 2 (fun i => (B.repr (vector (p a)) i).re)
  have he (a) : lift (w a) = B.repr (vector (p a)) := by
    ext i
    change ((B.repr (vector (p a)) i).re : ℂ) = B.repr (vector (p a)) i
    apply Complex.conj_eq_iff_re.mp
    rw [B.repr_apply_apply,hB,vector_gram]
    simp only [map_mul,map_inv₀,map_natCast,gram_real (F.shape i) (hs a)]
  have hg (a b) : (inner ℝ (w a) (w b) : ℂ) = inner ℂ (vector (p a)) (vector (p b)) := by
    rw [← inner_lift,he,he,B.repr.inner_map_map]
  have hn (a) : w a ≠ 0 := by
    intro hz
    have h:=hg a a
    rw [hz,inner_zero_left,Complex.ofReal_zero,vector_gram,Gram_self (hp.unitary a),
      inv_mul_cancel₀ (order_ne r)] at h
    exact zero_ne_one h
  refine ⟨w,hn,?_,?_⟩
  · intro k a
    have ortho : Orthonormal ℝ (fun x => w (Function.update a k x)) := by
      rw [orthonormal_iff_ite]
      intro x y
      apply Complex.ofReal_injective
      rw [hg,vector_gram,hp.line k _ _ (fun l hl => by simp [Function.update_of_ne hl])]
      simp only [Function.update_self]
      split <;> simp only [inv_mul_cancel₀ (order_ne r),mul_zero,Complex.ofReal_zero,Complex.ofReal_one]
    refine ⟨OrthonormalBasis.mk ortho ?_,OrthonormalBasis.coe_mk _ _⟩
    exact (ortho.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)).ge
  · have inj : Function.Injective (fun a=>Projectivization.mk ℝ (w a) (hn a)) := by
      intro a b hab
      obtain ⟨t,ht⟩ := (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mp hab
      apply separated_rays hp
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
      refine ⟨(t:ℂ),B.repr.injective ?_⟩
      rw [map_smul,← he,← he]
      ext i
      change (t:ℂ)*(w b i:ℂ)=(w a i:ℂ)
      exact_mod_cast congrArg (fun v : RSpace (r+4) => v i) ht
    rw [Set.ncard_range_of_injective inj]
    simp [Grid,Nat.card_eq_fintype_card]

#print axioms maximal_real_hypercubes
end RealHypercubes
