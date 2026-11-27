module
public import Quantum.FractionalLCSOrbit

/-! A ray- and context-transitive arrangement in dimension seven from Brock's BH(7,6). -/
@[expose] public section
noncomputable section
namespace TransitiveLCS.Seven
open QuantumCertificate Finset Complex
open scoped BigOperators ComplexConjugate

abbrev Phase := ZMod 6
abbrev Labels := Fin 6 → Phase
def numerator (a : Phase) : IQ :=
  ![(2,0),(1,1),(-1,1),(-2,0),(-1,-1),(1,-1)] ((ZMod.finEquiv 6).symm a)
def chi (a : Phase) : ℂ := embed 3 (numerator a) / 2

theorem numerator_add : ∀ a b : Phase, times 3 (numerator a) (numerator b) =
    numerator (a+b) + numerator (a+b) := by decide +kernel
theorem numerator_neg : ∀ a : Phase, cstar (numerator a) = numerator (-a) := by decide +kernel
theorem numerator_inj : Function.Injective numerator := by
  change ∀ ⦃a b : Phase⦄, numerator a = numerator b → a=b
  decide +kernel

@[simp] theorem chi_zero : chi 0 = 1 := by
  change embed 3 (2,0) / 2 = 1
  norm_num

theorem chi_add (a b : Phase) : chi (a+b) = chi a * chi b := by
  have h := congrArg (embed 3) (numerator_add a b)
  rw [embed_times,map_add] at h
  unfold chi
  linear_combination -h/4

theorem chi_neg (a : Phase) : chi (-a) = conj (chi a) := by
  unfold chi
  rw [← numerator_neg,embed_cstar,map_div₀,map_ofNat]

theorem chi_unit (a : Phase) : chi a * conj (chi a) = 1 := by
  rw [← chi_neg,← chi_add,add_neg_cancel,chi_zero]

theorem chi_inj : Function.Injective chi := by
  intro a b h
  apply numerator_inj
  apply embed_injective (d:=3) (by decide)
  exact (div_left_inj₀ (show (2:ℂ)≠0 by norm_num)).mp h

def word (t : Labels) : Fin 7 → Phase := Fin.cons 0 t
theorem word_add (a b : Labels) (i : Fin 7) : word (a+b) i = word a i + word b i := by
  refine Fin.cases (by simp [word]) (fun j => ?_) i
  simp [word]

def flat (t : Labels) : Space 7 := vector 3 28 (fun j => numerator (word t j))
def scale : ℂ := (Real.sqrt 28 : ℂ)⁻¹ * 2

theorem scale_nz : scale ≠ 0 := by
  have h : (Real.sqrt 28 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  exact mul_ne_zero (inv_ne_zero h) (by norm_num)

theorem flat_apply (t : Labels) (i : Fin 7) : flat t i = scale * chi (word t i) := by
  change (Real.sqrt 28 : ℂ)⁻¹ * embed 3 (numerator (word t i)) =
    ((Real.sqrt 28 : ℂ)⁻¹ * 2) * (embed 3 (numerator (word t i)) / 2)
  ring

@[simp] theorem flat_zero (t : Labels) : flat t 0 = scale := by simp [flat_apply,word]
theorem flat_nz (t : Labels) : flat t ≠ 0 := by
  intro h
  have hh := congrArg (fun a : Space 7 => a 0) h
  simp [scale_nz] at hh

theorem ray_inj : Function.Injective (fun a => Projectivization.mk ℂ (flat a) (flat_nz a)) := by
  intro a b h
  obtain ⟨s,hs⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  have hi := congrArg (fun f : Space 7 => f 0) hs
  change s * flat b 0 = flat a 0 at hi
  rw [flat_zero,flat_zero] at hi
  have hs1 : s=1 := mul_right_cancel₀ scale_nz (hi.trans (one_mul scale).symm)
  subst s
  rw [one_smul] at hs
  funext i
  apply chi_inj
  have hi := congrArg (fun f : Space 7 => f i.succ) hs.symm
  simpa [flat_apply,word,mul_right_inj' scale_nz] using hi

def diagonal (t : Labels) : Space 7 →ₗ[ℂ] Space 7 where
  toFun v := WithLp.toLp 2 (fun i => chi (word t i)*v i)
  map_add' v w := by
    ext i
    change chi (word t i)*(v i+w i)=chi (word t i)*v i+chi (word t i)*w i
    ring
  map_smul' z v := by
    ext i
    change chi (word t i)*(z*v i)=z*(chi (word t i)*v i)
    ring

theorem diagonal_inner (t : Labels) (v w : Space 7) :
    inner ℂ (diagonal t v) (diagonal t w) = inner ℂ v w := by
  rw [PiLp.inner_apply,PiLp.inner_apply]
  apply sum_congr rfl
  intro i _
  change (chi (word t i)*w i)*conj (chi (word t i)*v i) = w i * conj (v i)
  rw [map_mul,mul_mul_mul_comm,chi_unit,one_mul]

def shift (t : Labels) : Unitary 7 :=
  LinearIsometryEquiv.ofSurjective ((diagonal t).isometryOfInner (diagonal_inner t)) (by
    intro v
    refine ⟨WithLp.toLp 2 (fun i => conj (chi (word t i))*v i),?_⟩
    ext i
    change chi (word t i) * (conj (chi (word t i))*v i) = v i
    rw [← mul_assoc,chi_unit,one_mul])

theorem shift_flat (t a : Labels) : shift t (flat a) = flat (t+a) := by
  ext i
  change chi (word t i) * flat a i = flat (t+a) i
  rw [flat_apply,flat_apply,word_add,chi_add]
  ring

def seed : Fin 7 → Labels := ![
  ![0,0,0,0,0,0], ![1,4,5,3,3,1], ![4,1,3,5,3,1], ![5,3,1,4,1,3],
  ![3,5,4,1,1,3], ![3,3,1,1,4,5], ![1,1,3,3,5,4]]

theorem seed_inj : Function.Injective seed := by
  change ∀ ⦃a b : Fin 7⦄, seed a = seed b → a=b
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem seed_gram : GramTest 3 28 (fun i j => numerator (word (seed i) j)) := by
  decide +kernel

theorem basis_exists : ∃ B : Basis 7, ⇑B = fun i => flat (seed i) :=
  basis_of_test (by decide) _ seed_gram

def orbit : Orbit 7 Labels where
  state := flat
  nz := flat_nz
  projective := ray_inj
  seed := seed
  seed_injective := seed_inj
  basis := Classical.choose basis_exists
  seed_basis := fun i => congrFun (Classical.choose_spec basis_exists) i
  translate := shift
  translate_state := shift_flat

theorem card_labels : Fintype.card Labels = 46656 := by simp [Labels,ZMod.card]

/-- The full stabilizer of an arrangement of actual complex projective rays acts
transitively on the rays and on the specified bases. Its incidence equations have no solution mod 7. -/
theorem transitive_gap :
    ∃ A : Arrangement 7, A.RayAndContextTransitive ∧ ¬ A.Classical := by
  refine ⟨orbit.arrangement,orbit.transitive,orbit.classical_impossible ?_⟩
  rw [card_labels]
  decide +kernel

#print axioms transitive_gap
end TransitiveLCS.Seven

