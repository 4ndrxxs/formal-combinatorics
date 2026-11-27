module
public import Quantum.FractionalPolygons

/-! A quantitative odd-cycle obstruction for a common measurement basis.
Every site on the cycle carries the same output probabilities, with two
distinguished outcomes of equal mass P. A realization forces
2P ≤ length * (1 - 2P), independently of every other outcome. -/
@[expose] public section
noncomputable section
namespace FractionalOddCycle
open FractionalTorus FractionalPolygons Finset
open scoped BigOperators

private theorem split_sum {S A : Type*} [Fintype S] [DecidableEq S] [AddCommMonoid A]
    (a b : S) (hne : a≠b) (f : S → A) :
    ∑ i, f i=(∑ i ∈ (univ.erase a).erase b, f i)+f b+f a := by
  rw [sum_erase_add _ _ (by simp [Ne.symm hne]),sum_erase_add _ _ (mem_univ _)]

theorem edge_bound {S : Type*} [Fintype S] [DecidableEq S]
    (q : S → ℝ) (hq : ∀ a, 0≤q a) (hs : ∑ a, q a=1)
    (a b : S) (hne : a≠b) {P : ℝ} (hP : 0<P) (ha : q a=P) (hb : q b=P)
    (z w : S → Torus) (orth : ∑ i, (q i:ℂ)*unit (z i-w i)=0) :
    ‖unit (z a-z b)+unit (w a-w b)‖ ≤ (1-2*P)/P := by
  let T := (univ.erase a).erase b
  let v := fun i => (q i:ℂ)*unit (z i-w i)
  have total : (∑ i ∈ T, q i)=1-2*P := by
    have h := split_sum a b hne q
    rw [hs,ha,hb] at h
    dsimp [T]
    linarith
  have normTail : ‖∑ i ∈ T, v i‖ ≤ 1-2*P := calc
    _ ≤ ∑ i ∈ T, ‖v i‖ := norm_sum_le _ _
    _ = ∑ i ∈ T, q i := by
      apply sum_congr rfl
      intro i _
      simp [v,Real.norm_eq_abs,abs_of_nonneg (hq i)]
    _ = _ := total
  have close : (∑ i ∈ T, v i) + v b + v a=0 :=
    (split_sum a b hne v).symm.trans orth
  have phases : unit (z b-w a) * (unit (z a-z b)+unit (w a-w b))=
      unit (z a-w a)+unit (z b-w b) := by
    rw [mul_add,←unit_add,←unit_add]
    congr 2 <;> abel
  have closed : (P:ℂ) * (unit (z b-w a) * (unit (z a-z b)+unit (w a-w b)))=
      -(∑ i ∈ T, v i) := by
    rw [phases,mul_add]
    dsimp [v] at close ⊢
    rw [ha,hb] at close
    linear_combination close
  have bound := congrArg norm closed
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hP,norm_unit,one_mul,norm_neg] at bound
  apply (le_div_iff₀ hP).mpr
  rw [mul_comm, bound]
  exact normTail

theorem alternating_bound (f : ℕ → ℂ) (d : ℝ) (n : ℕ)
    (h : ∀ k<n, ‖f (k+1)+f k‖ ≤ d) :
    ‖f n-(-1:ℂ)^n*f 0‖ ≤ n*d := by
  induction n with
  | zero => simp
  | succ n ih =>
    have first := h n (by omega)
    have previous := ih (fun k hk => h k (by omega))
    calc
      _ = ‖(f (n+1)+f n) - (f n-(-1:ℂ)^n*f 0)‖ := by
        congr 1; rw [pow_succ]; ring
      _ ≤ ‖f (n+1)+f n‖+‖f n-(-1:ℂ)^n*f 0‖ := norm_sub_le _ _
      _ ≤ _ := by push_cast; linarith

theorem odd_bound (f : ℕ → ℂ) (d : ℝ) (n : ℕ) (odd : Odd n)
    (closed : f n=f 0) (unit0 : ‖f 0‖=1) (h : ∀ k<n, ‖f (k+1)+f k‖≤d) :
    2≤n*d := by
  have bound := alternating_bound f d n h
  rw [closed,odd.neg_one_pow,neg_one_mul,sub_neg_eq_add,←two_mul,norm_mul,unit0] at bound
  simpa using bound

open FractionalPolygons.Sudoku QuantumSudoku
theorem measured_cycle {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (p : Site I → Index I → ℝ) (hp : ∀ x a, 0≤p x a) (hs : ∀ x, ∑ a, p x a=1)
    (h : Measured p) (site : ℕ → Site I) (n : ℕ) (odd : Odd n)
    (closed : site n=site 0) (edges : ∀ k<n, Adjacent (site k) (site (k+1)))
    (q : Index I → ℝ) (same : ∀ k≤n, p (site k)=q)
    (a b : Index I) (hne : a≠b) {P : ℝ} (hP : 0<P) (ha : q a=P) (hb : q b=P) :
    2*P≤n*(1-2*P) := by
  obtain ⟨z,hz⟩ := (realizable_iff_phases p L R hp).mp ((measured_iff_vector p hs).mp h)
  let f := fun k => unit (z (site k) a-z (site k) b)
  have eq0 := same 0 (Nat.zero_le _)
  have pos (i) : 0≤q i := by rw [←eq0]; exact hp _ _
  have mass : ∑ i, q i=1 := by rw [←eq0]; exact hs _
  have necessary := odd_bound f ((1-2*P)/P) n odd (by simp [f,closed]) (by simp [f]) (by
    intro k hk
    let edge : Edge I := ⟨(site k,site (k+1)),edges k hk⟩
    have he := hz edge
    have eqk := same k (le_of_lt hk)
    have eqk' := same (k+1) (by omega)
    have hw (i) : weight p L R edge i=q i := by
      change Real.sqrt (p (site k) i)*Real.sqrt (p (site (k+1)) i)=q i
      rw [eqk,eqk',Real.mul_self_sqrt (pos i)]
    simp only [hw] at he
    rw [add_comm]
    exact edge_bound q pos mass a b hne hP ha hb (z (site k)) (z (site (k+1))) he)
  rw [←mul_div_assoc] at necessary
  exact (le_div_iff₀ hP).mp necessary

#print axioms measured_cycle
end FractionalOddCycle
