import SignedCaseGrid

/-! Efficient divisor enumeration for the endpoint mass equation p c² = s + m λ. -/

namespace Signed39.Contraction

def endpointValue (p s d : ℕ) : ℕ := ((p:ℤ)*(d:ℤ)^2-(s:ℤ)).natAbs

theorem endpoint_divisor {p m s c : ℕ} {l : ℤ} (h : numericalParameter p m s c l)
    (hn : ¬p∣s) {d : ℕ} (choose : d=c ∨ d=m-c) :
    m∣endpointValue p s d ∧ 0<endpointValue p s d := by
  obtain ⟨_,_,_,cm,eq,_,_,_⟩ := h
  have valid : (m:ℤ)∣(p:ℤ)*(d:ℤ)^2-(s:ℤ) := by
    rcases choose with rfl|rfl
    · exact ⟨l,by linear_combination eq⟩
    · rw [Nat.cast_sub cm]
      exact ⟨(p:ℤ)*m-2*p*c+l,by linear_combination eq⟩
  have nonzero : (p:ℤ)*(d:ℤ)^2-(s:ℤ)≠0 := by
    intro z
    have div : (p:ℤ)∣(s:ℤ) := ⟨(d:ℤ)^2,by omega⟩
    exact hn (by exact_mod_cast div)
  exact ⟨by simpa [endpointValue] using Int.natAbs_dvd_natAbs.mpr valid,
    Int.natAbs_pos.mpr nonzero⟩

def oneDivisor (p s d m : ℕ) (keep : List (ℕ × ℤ)) : Option QuotientInput → Prop
  | some q => q.valid (p*m) (p*s)
  | none => ∀ upper : Bool, let c := if upper then m-d else d
      let l := ((p:ℤ)*c^2-(s:ℤ))/(m:ℤ)
      numericalParameter p m s c l → (m,l)∈keep

instance (p s d m : ℕ) (keep : List (ℕ × ℤ)) (w : Option QuotientInput) : Decidable (oneDivisor p s d m keep w) := by
  cases w <;> unfold oneDivisor <;> infer_instance

def divisorGrid (p s B : ℕ) (w : ℕ → Option QuotientInput) (keep : List (ℕ × ℤ)) : Prop :=
  ∀ d : Fin (2*s), let N := endpointValue p s d.val
    N<B^2 ∧ ∀ j : Fin B, 0<j.val → j.val∣N → ∀ other : Bool,
      let m := if other then N/j.val else j.val
      p < m → ¬2∣m → ¬p∣m → oneDivisor p s d.val m keep (w m)

instance (p s B : ℕ) (w : ℕ → Option QuotientInput) (keep : List (ℕ × ℤ)) :
    Decidable (divisorGrid p s B w keep) := by unfold divisorGrid; infer_instance

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] {p : ℕ} [Fact p.Prime]

theorem endpoint_case {m s B : ℕ} {f : G → ℤ} {k l : ℤ} (hf : IsSDS k l f)
    (hg : Fintype.card G=p*m) (hn : k-l=(p:ℤ)*s) (hs : ¬ p∣s) (hm : p < m)
    {w : ℕ → Option QuotientInput} {keep : List (ℕ × ℤ)} (grid : divisorGrid p s B w keep) : (m,l)∈keep := by
  obtain ⟨c,params,hL,_⟩ := bounded_parameters hf hg hn hs hm
  have prime : p.Prime := Fact.out
  have sp : 0<s := Nat.pos_of_ne_zero (fun h => hs (h ▸ dvd_zero _))
  have little := mass_endpoint prime.pos sp params
  obtain ⟨d,mode,eq,near⟩ : ∃ d : Fin (2*s), ∃ mode : Bool,
      (if mode then m-d.val else d.val)=c ∧ (d.val=c ∨ d.val=m-c) := by
    rcases little with h|h
    · exact ⟨⟨c,h⟩,false,rfl,Or.inl rfl⟩
    · exact ⟨⟨m-c,h⟩,true,by have cm := params.2.2.2.1; simp; omega,Or.inr rfl⟩
  let N := endpointValue p s d.val
  obtain ⟨dv,pos⟩ := endpoint_divisor params hs near
  have M : 0 < m := Nat.zero_lt_of_lt hm
  obtain ⟨u,fac⟩ := dv
  change N=m*u at fac
  have ub : 0<u := by by_contra! h; rw [show u=0 by omega,mul_zero] at fac; change 0<N at pos; omega
  have pair : ∃ j : Fin B, 0<j.val ∧ j.val∣N ∧ ∃ other : Bool, (if other then N/j.val else j.val)=m := by
    by_cases h : m<B
    · exact ⟨⟨m,h⟩,M,⟨u,fac⟩,false,rfl⟩
    · have small : u<B := by
        by_contra! hu
        have lim := (grid d).1
        change N<B^2 at lim
        have prod := Nat.mul_le_mul (show B ≤ m by omega) hu
        rw [←fac,←pow_two] at prod
        omega
      exact ⟨⟨u,small⟩,ub,⟨m,by simpa [mul_comm] using fac⟩,true,by simp [fac,ub.ne']⟩
  obtain ⟨j,jpos,jdiv,other,code⟩ := pair
  have atM := (grid d).2 j jpos jdiv other
  change (if other then endpointValue p s d.val/j.val else j.val)=m at code
  simp only [code] at atM
  have core := atM hm params.2.1 params.2.2.1
  cases h : w m with
  | some v =>
      rw [h] at core
      exact False.elim (quotient_certificate_false hf hg (by simpa only [Nat.cast_mul] using hn) core)
  | none =>
      rw [h] at core
      have valid := core mode
      simp only [eq,← hL] at valid
      exact valid params

end Signed39.Contraction
