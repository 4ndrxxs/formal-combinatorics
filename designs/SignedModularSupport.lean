import SignedConcentration

/-! A prime-length word over its prime field with nonzero constant autocorrelation
differs from each constant vector in at least half of its coordinates. -/

namespace Signed39.ModularSupport

open Finset

variable {p : ℕ} [Fact p.Prime]

private def moment (u : ZMod p → ZMod p) (j : ℕ) : ZMod p := ∑ x, x^j*u x
def rcorr (u : ZMod p → ZMod p) (t : ZMod p) : ZMod p := ∑ x, u x*u (x+t)

private theorem translate_moment (u : ZMod p → ZMod p) (c : ZMod p) (n : ℕ) :
    (∑ x, (x+c)^n*u x) = ∑ j ∈ range (n+1),moment u j*c^(n-j)*(n.choose j:ZMod p) := by
  simp_rw [add_pow,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  simp only [moment,sum_mul]
  apply sum_congr rfl
  intros
  ring

private theorem cross_moment (u v : ZMod p → ZMod p) (n : ℕ) :
    (∑ t, t^n*(∑x,u x*v (x+t))) = ∑ j ∈ range (n+1),
      moment v j*moment u (n-j)*(-1:ZMod p)^(n-j)*(n.choose j:ZMod p) := by
  calc
    _ = ∑ t, ∑ x, ((x+t)-x)^n*(u x*v (x+t)) := by simp [mul_sum]
    _ = ∑ x, ∑ y, (y-x)^n*(u x*v y) := by
      rw [sum_comm]; apply sum_congr rfl; intro x _
      exact Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun _ => rfl)
    _ = ∑ x, u x*∑ y, (y+(-x))^n*v y := by
      simp only [mul_sum,sub_eq_add_neg]
      apply sum_congr rfl; intro x _
      apply sum_congr rfl; intros
      ring
    _ = _ := by
      simp_rw [translate_moment,mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      rw [show moment u (n-j)=∑ x, x^(n-j)*u x from rfl,mul_sum,sum_mul,sum_mul]
      apply sum_congr rfl; intro x _
      simp only [← neg_one_mul x,mul_pow]
      ring

private theorem corr_moment (u : ZMod p → ZMod p) (n : ℕ) :
    (∑ t, t^n*rcorr u t) = ∑ j ∈ range (n+1),
      moment u j*moment u (n-j)*(-1:ZMod p)^(n-j)*(n.choose j:ZMod p) := cross_moment u u n

/-- All moments of degree strictly below (p−1)/2 vanish. -/
private theorem vanishing (u : ZMod p → ZMod p) (c : ZMod p) (hc : ∀ t, rcorr u t=c)
    (j : ℕ) (hj : 2*j<p-1) : moment u j=0 := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    have hs := corr_moment u (2*j)
    have pw : ∑ t : ZMod p, t^(2*j)=0 := FiniteField.sum_pow_lt_card_sub_one _ _ (by rwa [ZMod.card])
    simp only [hc,← sum_mul,pw,zero_mul] at hs
    rw [sum_eq_single j] at hs
    · have sub : 2*j-j=j := by omega
      have cp := (Fact.out : p.Prime).coprime_choose_of_lt (by omega : 2*j<p) (by omega : j≤2*j)
      have binom : (((2*j).choose j:ℕ):ZMod p) ≠ 0 :=
        fun e => ((Fact.out : p.Prime).coprime_iff_not_dvd.mp cp) ((ZMod.natCast_eq_zero_iff _ _).mp e)
      have sg : (-1:ZMod p)^j ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
      rw [sub] at hs
      have prod := mul_eq_zero.mp hs.symm
      exact (mul_self_eq_zero.mp ((mul_eq_zero.mp (prod.resolve_right binom)).resolve_right sg))
    · intro b hb hbj
      have bnd := mem_range.mp hb
      by_cases hlt : b<j
      · simp [ih b hlt (by omega)]
      · have b' : 2*j-b < j := by omega
        simp [ih _ b' (by omega)]
    · intro h
      have : j∈range (2*j+1) := mem_range.mpr (by omega)
      contradiction

/-- The first |S| vanishing moments determine all coefficients on S. -/
private theorem sparse_moments (S : Finset (ZMod p)) (u : ZMod p → ZMod p)
    (hs : ∀ x, x∉S → u x=0) (hm : ∀ j, j<S.card → moment u j=0) : ∀ x, u x=0 := by
  classical
  induction S using Finset.induction_on generalizing u with
  | empty => exact fun x => hs x (notMem_empty _)
  | @insert a S ha ih =>
    let w := fun x => (x-a)*u x
    have sw (x : ZMod p) (hx : x∉S) : w x=0 := by
      by_cases h : x=a
      · simp [h,w]
      · simp [w,hs x (by simp [h,hx])]
    have mw (j : ℕ) (hj : j<S.card) : moment w j=0 := by
      have count : (insert a S).card=S.card+1 := card_insert_of_notMem ha
      have eq : moment w j=moment u (j+1)-a*moment u j := by
        simp only [moment,w,mul_sum,← sum_sub_distrib]
        apply sum_congr rfl
        intro x _
        rw [pow_succ]
        ring
      rw [eq,hm _ (by omega),hm _ (by omega),mul_zero,sub_zero]
    have all := ih w sw mw
    have away (x : ZMod p) (hx : x≠a) : u x=0 :=
      (mul_eq_zero.mp (all x)).resolve_left (sub_ne_zero.mpr hx)
    have z := hm 0 (by simp [ha])
    have ua : u a=0 := by
      simp only [moment,pow_zero,one_mul] at z
      rwa [sum_eq_single a (fun x _ hx => away x hx) (by simp)] at z
    intro x
    by_cases h : x=a
    · simpa only [h] using ua
    · exact away x h

theorem moment_zero (u : ZMod p → ZMod p) (c : ZMod p) (hh : ∀ t, rcorr u t=c)
    (j:ℕ) (hj:2*j<p-1) : (∑x:ZMod p,x^j*u x)=0 := vanishing u c hh j hj

theorem cross_constant (u v : ZMod p → ZMod p) (a b : ZMod p)
    (hu : ∀t,rcorr u t=a) (hv : ∀t,rcorr v t=b) (t:ZMod p) :
    (∑x,u x*v (x+t))=∑x,u x*v x := by
  classical
  let h (z:ZMod p) := ∑x,u x*v (x+z)
  let g (z:ZMod p) := h z-h 0
  let S := (univ : Finset (ZMod p)).erase 0
  have count : S.card=p-1 := by simp [S,card_erase_of_mem,ZMod.card]
  have hm (n:ℕ) (hn:n<S.card) : moment g n=0 := by
    rw [count] at hn
    have lower : (∑i:ZMod p,i^n)=0 := FiniteField.sum_pow_lt_card_sub_one _ _ (by rwa [ZMod.card])
    have sumh : (∑i:ZMod p,i^n*h i)=0 := by
      rw [show (∑i:ZMod p,i^n*h i)=_ from cross_moment u v n]
      apply sum_eq_zero; intro j hj
      have jle : j≤n := by have :=mem_range.mp hj; omega
      by_cases lo : 2*j<p-1
      · simp [vanishing v b hv j lo]
      · simp [vanishing u a hu (n-j) (by omega)]
    simp only [moment,g,mul_sub,sum_sub_distrib,←sum_mul,lower,zero_mul,sub_zero,sumh]
  have off (z:ZMod p) (hz:z∉S) : g z=0 := by
    have z0:z=0 := by by_contra n; exact hz (mem_erase.mpr ⟨n,mem_univ _⟩)
    simp [g,z0]
  have eq:=sparse_moments S g off hm t
  simpa only [g,h,add_zero,sub_eq_zero] using eq

theorem support_lower (u : ZMod p → ZMod p) (c : ZMod p) (hc : c≠0) (hh : ∀ t, rcorr u t=c) :
    p ≤ 2*(univ.filter (fun x => u x≠0)).card := by
  classical
  by_contra! few
  let S := univ.filter (fun x => u x≠0)
  have hS : 2*S.card<p := few
  have all := sparse_moments S u (fun x hx => by simpa [S] using hx)
    (fun j hj => vanishing u c hh j (by omega))
  have h := hh 0
  simp [rcorr,all] at h
  exact hc h.symm

#print axioms support_lower

end Signed39.ModularSupport

