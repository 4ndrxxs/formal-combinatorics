import SignedMassEndpoint

/-! A bounded numerical grid with optional quotient certificates for whole orders. -/

namespace Signed39.Contraction

structure QuotientInput where
  r : ℕ
  q : ℕ
  e : ℕ
  j : ℕ
  b : ℕ

def QuotientInput.valid (d : QuotientInput) (v n : ℕ) : Prop :=
  quotientCertificate v n d.r d.q d.e d.j d.b
instance quotientInputValidDec (d : QuotientInput) (v n : ℕ) : Decidable (d.valid v n) := by
  unfold QuotientInput.valid; infer_instance

def orderGrid (p s m : ℕ) (keep : List (ℕ × ℤ)) : Option QuotientInput → Prop
  | some d => d.valid (p*m) (p*s)
  | none => ∀ e : Fin (2*s), ∀ high : Bool, let c := if high then m-e.val else e.val
      let l := ((p:ℤ)*c^2-(s:ℤ))/(m:ℤ)
      numericalParameter p m s c l → (m,l)∈keep

instance (p s m : ℕ) (keep : List (ℕ × ℤ)) (w : Option QuotientInput) : Decidable (orderGrid p s m keep w) := by
  cases w <;> unfold orderGrid <;> infer_instance

def caseGrid (p s bound : ℕ) (w : ℕ → Option QuotientInput) (keep : List (ℕ × ℤ)) : Prop :=
  ∀ m : Fin bound, p < m.val → ¬2∣m.val → ¬p∣m.val → orderGrid p s m.val keep (w m.val)

instance (p s B : ℕ) (w : ℕ → Option QuotientInput) (keep : List (ℕ × ℤ)) :
    Decidable (caseGrid p s B w keep) := by
  unfold caseGrid
  infer_instance

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] {p : ℕ} [Fact p.Prime]

theorem bounded_case {m s B : ℕ} {f : G → ℤ} {k l : ℤ} (hf : IsSDS k l f)
    (hg : Fintype.card G=p*m) (hn : k-l=(p:ℤ)*s) (hs : ¬ p∣s) (hm : p < m)
    (size : ∀ t : ℕ, p*t≤(p*s)^2+p*s+1 → t<B)
    {w : ℕ → Option QuotientInput} {keep : List (ℕ × ℤ)} (grid : caseGrid p s B w keep) : (m,l)∈keep := by
  obtain ⟨c,params,hL,hU⟩ := bounded_parameters hf hg hn hs hm
  have prime : p.Prime := Fact.out
  have sp : 0<s := Nat.pos_of_ne_zero (fun h => hs (h ▸ dvd_zero _))
  have little := mass_endpoint prime.pos sp params
  obtain ⟨d,mode,eq⟩ : ∃ d : Fin (2*s), ∃ mode : Bool, (if mode then m-d.val else d.val)=c := by
    rcases little with h|h
    · exact ⟨⟨c,h⟩,false,rfl⟩
    · exact ⟨⟨m-c,h⟩,true,by have cm := params.2.2.2.1; simp; omega⟩
  have atM := grid ⟨m,size m hU⟩ hm params.2.1 params.2.2.1
  change orderGrid p s m keep (w m) at atM
  cases h : w m with
  | some v =>
      rw [h] at atM
      exact False.elim (quotient_certificate_false hf hg (by simpa only [Nat.cast_mul] using hn) atM)
  | none =>
      rw [h] at atM
      have found := atM d mode
      simp only [eq,← hL] at found
      exact found params

end Signed39.Contraction
