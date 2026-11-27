import SignedSmallClassification
import SignedFixedNormExclusions
import SignedPrimeSieve

/-! Exact classification for norm cofactors through eight and further explicit forbidden cofactors. -/

namespace Signed39.Contraction

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] {p : ℕ} [Fact p.Prime]

theorem common_prime_bounds {s : ℕ} {k lam : ℤ} {f : G → ℤ} (hf : IsSDS k lam f)
    (hd : p∣Fintype.card G) (hn : k-lam=(p:ℤ)*s) (hs : ¬p∣s) (hlo : 2 ≤ s) :
    3≤p ∧ p<2*s ∧ ∃ m : ℕ, Fintype.card G=p*m ∧ p < m := by
  have prime : p.Prime := Fact.out
  have hs' : ¬ (p:ℤ)∣(s:ℤ) := by exact_mod_cast hs
  have odd : ¬2∣Fintype.card G := fun he => nonsquare_of_valuation_one prime hs' (hn ▸ even_norm_square hf he)
  have hp : 3≤p := by
    by_contra! h
    have := prime.two_le
    exact odd ((show p=2 by omega) ▸ hd)
  obtain ⟨m,hg⟩ := hd
  have mpos : 0 < m := by
    by_contra! h
    have eq : m=0 := by omega
    simp [eq] at hg
  have hm : 1 < m := by
    by_contra! small
    have m1 : m=1 := by omega
    obtain ⟨c,_,he,_,kb,_⟩ := normalized_parameter hf hg hn
    rw [m1] at he kb
    norm_num at he kb
    have pos := mul_nonneg (Nat.cast_nonneg p : (0:ℤ)≤p) (sq_nonneg (c:ℤ))
    have prod := mul_nonneg (show (0:ℤ)≤(p:ℤ)-2 by omega) (show (0:ℤ)≤(s:ℤ)-2 by omega)
    nlinarith
  have bound := abelian_linear_prime_bound hf hg hm hn hs'
  have le : p<2*s := by exact_mod_cast bound
  exact ⟨hp,le,m,hg,abelian_cofactor_bound hf hg hm hn hs'⟩

/-- The sieve covers 5, 6, 7, 8, 10, 14, 21, 30, 33 and 66. -/
theorem no_sieved_norm_cofactor {s : ℕ} {k lam : ℤ} {f : G → ℤ} (hf : IsSDS k lam f)
    (hd : p∣Fintype.card G) (hn : k-lam=(p:ℤ)*s) (hs : ¬p∣s) (hset : sieveCofactor s) : False := by
  have prime : p.Prime := Fact.out
  have bounds : 2 ≤ s ∧ s≤66 := by unfold sieveCofactor at hset; omega
  obtain ⟨p3,ple,m,hg,hm⟩ := common_prime_bounds hf hd hn hs bounds.1
  have record : sieveLine p s := sieve_valid ⟨p,by omega⟩ ⟨s,by omega⟩ hset prime p3 ple hs
  rcases record with ⟨hp,hs⟩|⟨hp,hs⟩|certificate
  · subst p; subst s
    exact fixed_21_false hf hg hm (by simpa using hn)
  · subst p; subst s
    exact fixed_56_false hf hg hm (by simpa using hn)
  · exact prime_factor_sieve hf hd hn certificate

/-- With 1≤s≤8 and n=ps of p-valuation one, the odd prime Paley parameters are necessary and sufficient. -/
theorem norm_cofactor_through_eight {s : ℕ} {k lam : ℤ} (hd : p∣Fintype.card G)
    (hn : k-lam=(p:ℤ)*s) (hs : ¬p∣s) (lo : 1 ≤ s) (hi : s≤8) :
    (∃ f : G → ℤ, IsSDS k lam f) ↔ s=1 ∧ Fintype.card G=p ∧ k=(p:ℤ)-1 ∧ lam= -1 ∧ p≠2 := by
  constructor
  · rintro ⟨f,hf⟩
    have eq : s=1 := by
      by_contra ne
      by_cases small : s≤4
      · exact no_small_norm_cofactor hf hd hn (by exact_mod_cast hs) (by omega) (by omega)
      · exact no_sieved_norm_cofactor hf hd hn hs (by unfold sieveCofactor; omega)
    exact ⟨eq,prime_norm_parameters hf (by simpa [eq] using hn) hd⟩
  · rintro ⟨_,hG,rfl,rfl,ho⟩
    exact prime_norm_exists G hG ho

#print axioms no_sieved_norm_cofactor
#print axioms norm_cofactor_through_eight

end Signed39.Contraction

