module
public import Quantum.Exact

/-! A fractional four-by-four Sudoku with orthostochastic local matrices and
no global quantum realization. All two-pair balanced patterns are characterized
by ordinary graph two-colourability. -/
@[expose] public section
noncomputable section
namespace FractionalBinary
open QuantumCertificate Complex Finset
open scoped ComplexConjugate BigOperators

abbrev Site := Fin 4 × Fin 4
abbrev Prob := Site → Fin 4 → ℝ
abbrev ONB := OrthonormalBasis (Fin 4) ℂ (Space 4)

/-- Four rows, four columns, and the four two-by-two blocks in reading order. -/
def line : Fin 12 → Fin 4 → Site :=
  ![![(0,0),(0,1),(0,2),(0,3)],![(1,0),(1,1),(1,2),(1,3)],
    ![(2,0),(2,1),(2,2),(2,3)],![(3,0),(3,1),(3,2),(3,3)],
    ![(0,0),(1,0),(2,0),(3,0)],![(0,1),(1,1),(2,1),(3,1)],
    ![(0,2),(1,2),(2,2),(3,2)],![(0,3),(1,3),(2,3),(3,3)],
    ![(0,0),(0,1),(1,0),(1,1)],![(0,2),(0,3),(1,2),(1,3)],
    ![(2,0),(2,1),(3,0),(3,1)],![(2,2),(2,3),(3,2),(3,3)]]

def Grid (v : Site → Space 4) : Prop :=
  ∀ l, ∃ B : ONB, ⇑B = fun k => v (line l k)

def Realizes (p : Prob) : Prop :=
  ∃ v : Site → Space 4, Grid v ∧ ∀ x a, Complex.normSq (v x a) = p x a

def ArbitraryMeasurement (p : Prob) : Prop :=
  ∃ v : Site → Space 4, ∃ B : ONB, Grid v ∧ ∀ x a, Complex.normSq (B.repr (v x) a) = p x a

theorem any_basis {p : Prob} : ArbitraryMeasurement p ↔ Realizes p := by
  constructor
  · rintro ⟨v,B,h,hp⟩
    refine ⟨fun x => B.repr (v x),?_,hp⟩
    intro l
    obtain ⟨C,hC⟩ := h l
    exact ⟨C.map B.repr,funext fun j => by simp [hC]⟩
  · rintro ⟨v,h,hp⟩
    exact ⟨v,EuclideanSpace.basisFun (Fin 4) ℂ,h,fun x a => by simpa using hp x a⟩

def first : Bool → Fin 4
  | true => 0
  | false => 2
def second : Bool → Fin 4
  | true => 1
  | false => 3
def weight (g : Bool) (a : Fin 4) : ℝ :=
  if a=first g ∨ a=second g then 1/2 else 0
def probabilities (g : Site → Bool) : Prob := fun x => weight (g x)

def Proper (g s : Site → Bool) : Prop :=
  ∀ l i j, i≠j → g (line l i)=g (line l j) → s (line l i)≠s (line l j)

def label (g s : Bool) : Fin 4 := if s then first g else second g
def signs : Fin 4 → Fin 4 → ℤ :=
  ![![1,1,0,0],![1,-1,0,0],![0,0,1,1],![0,0,1,-1]]
def reps (i j : Fin 4) : IQ := (signs i j,0)
def vec (g s : Bool) : Space 4 := vector 1 2 (reps (label g s))

theorem vecGram (g s h t : Bool) :
    inner ℂ (vec g s) (vec h t) = if (g,s)=(h,t) then 1 else 0 := by
  obtain ⟨B,hB⟩ := basis_of_test (by decide : 0<2) (v:=reps)
    (by decide +kernel : GramTest 1 2 reps)
  change inner ℂ (vector 1 2 (reps _)) (vector 1 2 (reps _)) = _
  rw [← congrFun hB (label g s),← congrFun hB (label h t),B.inner_eq_ite]
  cases g <;> cases s <;> cases h <;> cases t <;> norm_num [label,first,second]

theorem vecWeight (g s : Bool) (a : Fin 4) :
    (vec g s a).im=0 ∧ Complex.normSq (vec g s a) = weight g a := by
  have hr : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  cases g <;> cases s <;> fin_cases a <;>
    norm_num [vec,vector,reps,signs,label,first,second,embed,weight,
      Complex.mul_re,Complex.mul_im,Complex.normSq_apply,Complex.inv_re,Complex.inv_im,
      mul_pow,←sq,hr] <;> nlinarith only [hr]

theorem vecBasis (g s : Fin 4 → Bool) (h : ∀ i j, i≠j → g i=g j → s i≠s j) :
    ∃ B : ONB, ⇑B=fun j => vec (g j) (s j) := by
  classical
  have hh : Orthonormal ℂ (fun j => vec (g j) (s j)) := by
    apply orthonormal_iff_ite.mpr
    intro i j
    rw [vecGram]
    by_cases hd : i=j
    · subst j
      simp
    · have hpair : (g i,s i)≠(g j,s j) := by
        intro he
        exact h i j hd (congrArg Prod.fst he) (congrArg Prod.snd he)
      simp [hd,hpair]
  exact ⟨OrthonormalBasis.mk hh (hh.linearIndependent.span_eq_top_of_card_eq_finrank
    (by simp)).ge,OrthonormalBasis.coe_mk _ _⟩

theorem realize_of_proper {g s : Site → Bool} (h : Proper g s) :
    Realizes (probabilities g) :=
  ⟨fun x => vec (g x) (s x),fun l => vecBasis _ _ (h l),fun _ a => (vecWeight _ _ a).2⟩

def half (z : ℂ) : Bool := decide (0<z.re ∨ (z.re=0 ∧ 0<z.im))

theorem half_opposite (z : ℂ) (hz : z≠0) : half z≠half (-z) := by
  by_cases h : z.re=0
  · have him : z.im≠0 := fun e => hz (Complex.ext h e)
    rcases lt_or_gt_of_ne him with hi|hi <;> simp [half,h,hi,le_of_lt hi]
  · rcases lt_or_gt_of_ne h with hi|hi <;> simp [half,h,hi,le_of_lt hi]

theorem two_inner (v w : Space 4) (g : Bool)
    (hv : ∀ a, Complex.normSq (v a)=weight g a) (ho : inner ℂ v w=0) :
    w (first g)*conj (v (first g)) + w (second g)*conj (v (second g))=0 := by
  have hz (a : Fin 4) (ha : a≠first g) (hb : a≠second g) : v a=0 := by
    apply Complex.normSq_eq_zero.mp
    simpa [weight,ha,hb] using hv a
  rw [PiLp.inner_apply,Fin.sum_univ_four] at ho
  change w 0*conj (v 0)+w 1*conj (v 1)+w 2*conj (v 2)+w 3*conj (v 3)=0 at ho
  cases g
  · simpa [first,second,hz 0 (by decide) (by decide),hz 1 (by decide) (by decide)] using ho
  · simpa [first,second,hz 2 (by decide) (by decide),hz 3 (by decide) (by decide)] using ho

theorem phase_opposite (v w : Space 4) (g : Bool)
    (hv : ∀ a, Complex.normSq (v a)=weight g a)
    (hw : ∀ a, Complex.normSq (w a)=weight g a) (ho : inner ℂ v w=0) :
    conj (v (first g))*v (second g) = -(conj (w (first g))*w (second g)) := by
  let a := first g
  let b := second g
  have hx : w a*conj (w a) = (1:ℂ)/2 := by
    rw [Complex.mul_conj,hw]
    simp [weight,a]
  have hy : v b*conj (v b) = (1:ℂ)/2 := by
    rw [Complex.mul_conj,hv]
    simp [weight,b]
  have H := two_inner v w g hv ho
  change w a*conj (v a)+w b*conj (v b)=0 at H
  change conj (v a)*v b= -(conj (w a)*w b)
  linear_combination 2*(conj (w a)*v b)*H - 2*(conj (v a)*v b)*hx - 2*(conj (w a)*w b)*hy

theorem proper_of_realize {g : Site → Bool} (h : Realizes (probabilities g)) :
    ∃ s, Proper g s := by
  obtain ⟨v,hg,hp⟩ := h
  let phase (x : Site) := conj (v x (first (g x))) * v x (second (g x))
  have nz (x : Site) : phase x≠0 := by
    have h1 : Complex.normSq (v x (first (g x)))=1/2 := by simpa [probabilities,weight] using hp x (first (g x))
    have h2 : Complex.normSq (v x (second (g x)))=1/2 := by simpa [probabilities,weight] using hp x (second (g x))
    have ha : v x (first (g x))≠0 := by intro he; simp [he] at h1
    have hb : v x (second (g x))≠0 := by intro he; simp [he] at h2
    exact mul_ne_zero (by simpa using ha) hb
  refine ⟨fun x => half (phase x),?_⟩
  intro l i j hij he
  obtain ⟨B,hB⟩ := hg l
  have ho : inner ℂ (v (line l i)) (v (line l j))=0 := by
    rw [← congrFun hB i,← congrFun hB j,B.inner_eq_ite]
    simp [hij]
  have heq : phase (line l i) = -phase (line l j) := by
    have hq := phase_opposite _ _ (g (line l i)) (hp _) (fun a => by simpa [probabilities,he] using hp (line l j) a) ho
    simpa only [phase,he] using hq
  change half (phase (line l i)) ≠ half (phase (line l j))
  rw [heq]
  exact (half_opposite _ (nz _)).symm

theorem realizable_iff_two_colorable (g : Site → Bool) :
    ArbitraryMeasurement (probabilities g) ↔ ∃ s, Proper g s := by
  rw [any_basis]
  exact ⟨proper_of_realize,fun ⟨_,h⟩ => realize_of_proper h⟩

def pattern (x : Site) : Bool :=
  (![![true,false,true,false],![false,true,false,true],
    ![true,false,false,true],![false,true,true,false]] : Fin 4 → Fin 4 → Bool) x.1 x.2

def LocallyOrthostochastic (p : Prob) : Prop :=
  ∀ l, ∃ B : ONB, ∀ j a, (B j a).im=0 ∧ Complex.normSq (B j a)=p (line l j) a

theorem all_local_orthostochastic : LocallyOrthostochastic (probabilities pattern) := by
  intro l
  have h : ∀ l, ∃ s : Fin 4 → Bool, ∀ i j, i≠j →
      pattern (line l i)=pattern (line l j) → s i≠s j := by decide +kernel
  obtain ⟨s,hs⟩ := h l
  obtain ⟨B,hB⟩ := vecBasis _ _ hs
  refine ⟨B,fun j a => ?_⟩
  rw [congrFun hB j]
  exact vecWeight _ _ _

theorem no_global_measurement : ¬ ArbitraryMeasurement (probabilities pattern) := by
  rw [realizable_iff_two_colorable]
  rintro ⟨s,h⟩
  have a : s (0,0) ≠ s (1,1) := h 8 0 3 (by decide) (by decide)
  have b : s (1,1) ≠ s (3,1) := h 5 1 3 (by decide) (by decide)
  have c : s (3,1) ≠ s (3,2) := h 3 1 2 (by decide) (by decide)
  have d : s (3,2) ≠ s (0,2) := h 6 3 0 (by decide) (by decide)
  have e : s (0,2) ≠ s (0,0) := h 0 2 0 (by decide) (by decide)
  have impossible (a b c d e : Bool) : a≠b → b≠c → c≠d → d≠e → e≠a → False := by
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide +kernel
  exact impossible _ _ _ _ _ a b c d e

#print axioms realizable_iff_two_colorable
#print axioms all_local_orthostochastic
#print axioms no_global_measurement
end FractionalBinary
