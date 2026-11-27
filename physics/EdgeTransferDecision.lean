import RationalEdgeWalk
import Quantum.OrbitDecision

/-! Algebraic criterion for symmetry of edge-state transfer in a finite bipartite graph.
In the aperiodic case every candidate time lies in a finite interval calculated from
a source polynomial and a rational target coordinate vector. -/
noncomputable section
namespace BipartiteEdgeWalk.Decision
open RationalOrbit Function Polynomial
variable {E L R : Type*} [Fintype E] [DecidableEq E]
variable [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

def Directed (l : E → L) (r : E → R) (a b : E) := ∃ k, PerfectAt l r a b k

def SymmetricPST (l : E → L) (r : E → R) := ∀ a b, Directed l r a b → Directed l r b a

theorem directed_iff (l : E → L) (r : E → R) (hl : Surjective l) (hr : Surjective r)
    (a b : E) : Directed l r a b ↔ Reaches (step l r) (amplitude a) (amplitude b) :=
  exists_congr (fun k => perfectAt_iff l r hl hr a b k)

private theorem distinct_amplitudes {a b : E} (hne : a≠b) : amplitude a≠amplitude b := by
  intro he
  have := congrFun he a
  simp [amplitude,hne] at this

private theorem amplitude_ne (a : E) : amplitude a≠0 := by
  intro he
  have := congrFun he a
  simp [amplitude] at this

/-- The target is outside a finite column span, or its equality test fails at every
time up to this explicit integer bound. All needed polynomial coefficients are rational. -/
def Excluded (T : Module.End ℚ (E → ℚ)) (v w : E → ℚ) (D : ℤ[X]) :=
  (¬InKrylov T v D.natDegree w) ∨
  ∃ p : ℕ, p.Prime ∧ (p:ℤ)∣D.leadingCoeff ∧
  ∃ A : ℤ, A≠0 ∧ ∃ P : ℤ[X], P.natDegree<D.natDegree ∧
    act T v (P.map castQ)=(A:ℚ) • w ∧
    ∀ k≤ P.natDegree + A.natAbs.factorization p*(D.natDegree-(D.map (red p)).natDegree), (T^k) v≠w

theorem excluded_iff {T : Module.End ℚ (E → ℚ)} {v w : E → ℚ} {D : ℤ[X]}
    (hs : SourceEquation T v D) (dn : D≠0) (vn : v≠0) (nu : ¬IsUnit D.leadingCoeff) :
    Excluded T v w D ↔ ¬Reaches T v w := by
  constructor
  · rintro (out | ⟨p,hp,hd,A,ha,P,_,ht,none⟩) hits
    · exact out (hs.in_krylov_of_reaches dn vn hits)
    · letI : Fact p.Prime := ⟨hp⟩
      obtain ⟨k,hk,eq⟩ := (hs.finite_hits hd ha ht).mp hits
      exact none k hk eq
  · intro no
    by_cases inside : InKrylov T v D.natDegree w
    · obtain ⟨p,hp,hd⟩ := hs.prime_of_nonunit nu
      obtain ⟨A,ha,P,deg,ht⟩ := inside.clear
      exact Or.inr ⟨p,hp,hd,A,ha,P,deg,ht,fun k _ eq => no ⟨k,eq⟩⟩
    · exact Or.inl inside

theorem source_data_exists (l : E → L) (r : E → R) :
    ∃ D : E → ℤ[X], ∀ a, D a≠0 ∧ SourceEquation (step l r) (amplitude a) (D a) := by
  choose D hd using fun a : E => source_equation_exists (step l r) (amplitude a)
  exact ⟨D,hd⟩

/-- In the published two-reflection walk, all ordered transfers are reversible iff
each aperiodic source passes the target exclusion test for every other edge. -/
theorem finite_symmetry_criterion (l : E → L) (r : E → R) (hl : Surjective l) (hr : Surjective r)
    (D : E → ℤ[X]) (valid : ∀ a, D a≠0 ∧ SourceEquation (step l r) (amplitude a) (D a)) :
    SymmetricPST l r ↔ ∀ a b : E, a≠b → ¬IsUnit (D a).leadingCoeff →
      Excluded (step l r) (amplitude a) (amplitude b) (D a) := by
  constructor
  · intro sym a b ne nu
    have h := valid a
    apply (excluded_iff h.2 h.1 (amplitude_ne a) nu).mpr
    intro forward
    have back := (directed_iff l r hl hr b a).mp (sym a b ((directed_iff l r hl hr a b).mpr forward))
    exact nu (h.2.unit_of_periodic ((reverse_iff_periodic (distinct_amplitudes ne) forward).mp back))
  · intro pass a b forward
    by_cases eq : a=b
    · subst b; exact forward
    have fwd := (directed_iff l r hl hr a b).mp forward
    have h := valid a
    by_cases unit : IsUnit (D a).leadingCoeff
    · have per := (h.2.periodic_iff_unit (step_injective l r hl hr) 1 (coordinate_bound l r hl hr a)).mpr unit
      exact (directed_iff l r hl hr b a).mpr ((reverse_iff_periodic (distinct_amplitudes eq) fwd).mpr per)
    · exact ((excluded_iff h.2 h.1 (amplitude_ne a) unit).mp (pass a b eq unit) fwd).elim

/-- For a forward transfer between distinct edges the leading coefficient alone decides
whether reverse transfer occurs, without having to search from the target edge. -/
theorem reverse_iff_unit_leading (l : E → L) (r : E → R) (hl : Surjective l) (hr : Surjective r)
    {a b : E} (ne : a≠b) (forward : Directed l r a b) {D : ℤ[X]}
    (hs : SourceEquation (step l r) (amplitude a) D) :
    Directed l r b a ↔ IsUnit D.leadingCoeff := by
  rw [directed_iff l r hl hr,reverse_iff_periodic (distinct_amplitudes ne) ((directed_iff l r hl hr a b).mp forward)]
  exact hs.periodic_iff_unit (step_injective l r hl hr) 1 (coordinate_bound l r hl hr a)

#print axioms excluded_iff
#print axioms source_data_exists
#print axioms finite_symmetry_criterion
#print axioms reverse_iff_unit_leading
end BipartiteEdgeWalk.Decision
