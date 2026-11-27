import Quantum.Hadamard.AsymptoticBuild

/-! Arbitrary seeds, including odd and twice-odd orders. -/

namespace Hadamard.Arithmetic

/-- Two normalized steps of gcd m fill the entire congruence class of the
seed modulo both four and m. -/
theorem shifted_progression {m n₀ u v : ℕ} (hm : 0 < m)
    (c4 : (4 : ℕ).Coprime m) (huv : u.gcd v = m) (hv : 0 < v) :
    ∃ B, ∀ n ≥ B, n ≡ n₀ [MOD 4] → n ≡ n₀ [MOD m] →
      ∃ x y, n=n₀+4*u*x+4*v*y := by
  let s := 4-n₀%4
  have hs : 4 ∣ n₀+s := by dsimp [s]; omega
  obtain ⟨B,hB⟩ := eventually_in_progression hm c4 huv hv hs
  refine ⟨B, ?_⟩
  intro n hn h4 hr
  have h4' : 4 ∣ n+s := by change n%4=n₀%4 at h4; dsimp [s]; omega
  obtain ⟨x,y,xy⟩ := hB (n+s) (by omega) h4' (hr.add_right s)
  exact ⟨x,y,by omega⟩

theorem close_from_seed {m n₀ u v : ℕ} {P : ℕ → Prop} (hm : 0 < m)
    (c4 : (4 : ℕ).Coprime m) (huv : u.gcd v = m) (hv : 0 < v)
    (pos : 0 < n₀) (seed : P n₀)
    (growU : ∀ {n}, 0 < n → P n → n ≡ n₀ [MOD m] → ∀ t, P (n+t*(4*u)))
    (growV : ∀ {n}, 0 < n → P n → n ≡ n₀ [MOD m] → ∀ t, P (n+t*(4*v))) :
    ∃ B, ∀ n ≥ B, n ≡ n₀ [MOD 4] → n ≡ n₀ [MOD m] → P n := by
  obtain ⟨B,hB⟩ := shifted_progression (n₀ := n₀) hm c4 huv hv
  refine ⟨B, ?_⟩
  intro n hn h4 hr
  obtain ⟨x,y,xy⟩ := hB n hn h4 hr
  have du : m ∣ u := huv ▸ Nat.gcd_dvd_left u v
  have dz : 4*u ≡ 0 [MOD m] := Nat.modEq_zero_iff_dvd.mpr (du.trans (dvd_mul_left u 4))
  have hrx : n₀+x*(4*u) ≡ n₀ [MOD m] := by simpa using (dz.mul_left x).add_left n₀
  have px := growU pos seed (Nat.ModEq.refl _) x
  have py := growV (by omega) px hrx y
  rw [xy]
  simpa only [Nat.mul_comm x (4*u), Nat.mul_comm y (4*v)] using py

theorem seed_class_large {m n₀ : ℕ} {P : ℕ → Prop} (hm : m.Prime)
    (hm2 : 2 < m) (C : PrimeOrderConstruction m P) (pos : 0 < n₀) (seed : P n₀) :
    ∃ B, ∀ n ≥ B, n ≡ n₀ [MOD 4] → n ≡ n₀ [MOD m] → P n := by
  have c4 := four_coprime_prime hm hm2
  by_cases hr : n₀%m = 1
  · obtain ⟨q₁,q₂,h₁,h₂,gcd⟩ := square_steps hm hm2
    have rone : n₀ ≡ 1 [MOD m] := by
      simpa [Nat.ModEq, Nat.mod_eq_of_lt (show 1<m by omega)] using hr
    have pos₂ : 0 < squareIncrement q₂ := by
      have H : 1 < (2*(q₂+1))^2 := by have := h₂.prime.two_le; nlinarith
      dsimp [squareIncrement, squareOrder]; omega
    have grow {q n : ℕ} (hq : SquareSeed m q) (hn : 0<n) (pn : P n)
        (res : n ≡ n₀ [MOD m]) (t : ℕ) : P (n+t*(4*squareIncrement q)) := by
      simpa only [Nat.mul_assoc] using C.squareGrow hq hn pn (res.trans rone) (t*4)
    exact close_from_seed hm.pos c4 gcd pos₂ pos seed (grow h₁) (grow h₂)
  · obtain ⟨q,p₁,p₂,hq,q4,qr,h₁,h₂,gcd⟩ := product_steps hm hm2 hr
    have pos₂ : 0 < (p₂*q-1)/4 := by
      have hq2 := hq.two_le
      have pp := h₂.prime.two_le
      have p4 := h₂.modFour
      change p₂%4 = 3%4 at p4
      have hp : 3 ≤ p₂ := by omega
      have h : 6 ≤ p₂*q := by nlinarith
      omega
    have grow {p n : ℕ} (hp : ProductStep m q p) (hn : 0<n) (pn : P n)
        (res : n ≡ n₀ [MOD m]) (t : ℕ) : P (n+t*(4*((p*q-1)/4))) := by
      have h4 : p*q ≡ 1 [MOD 4] := (hp.modFour.mul q4).trans (by decide)
      have po : 1 ≤ p*q := Nat.mul_pos hp.prime.pos hq.pos
      rw [Nat.mul_div_cancel' ((Nat.modEq_iff_dvd' po).mp h4.symm)]
      exact C.productGrow hq q4 hp hn pn (res.trans qr.symm) t
    exact close_from_seed hm.pos c4 gcd pos₂ pos seed (grow h₁) (grow h₂)

/-- For a candidate admissibility predicate, one positive seed in every
admissible pair of classes suffices. No periodicity assumption on admissibility
is necessary. -/
theorem eventual_of_seeds {m : ℕ} {P A : ℕ → Prop} (hm : m.Prime)
    (hm2 : 2 < m) (C : PrimeOrderConstruction m P)
    (seeds : ∀ n, A n → ∃ k > 0, P k ∧ k ≡ n [MOD 4] ∧ k ≡ n [MOD m]) :
    ∃ B, ∀ n ≥ B, A n → P n := by
  classical
  have cls (i : Fin (4*m)) :
      ∃ B, ∀ n ≥ B, n ≡ i.val [MOD 4*m] → A n → P n := by
    by_cases H : ∃ n, n ≡ i.val [MOD 4*m] ∧ A n
    · obtain ⟨j,ji,Aj⟩ := H
      obtain ⟨k,hk,pk,k4,km⟩ := seeds j Aj
      obtain ⟨B,hB⟩ := seed_class_large hm hm2 C hk pk
      refine ⟨B, ?_⟩
      intro n hn ni _
      have h := ni.trans ji.symm
      exact hB n hn ((h.of_dvd (dvd_mul_right 4 m)).trans k4.symm)
        ((h.of_dvd (dvd_mul_left m 4)).trans km.symm)
    · exact ⟨0, fun n _ h a => (H ⟨n,h,a⟩).elim⟩
  choose bound hbound using cls
  refine ⟨Finset.univ.sup bound, ?_⟩
  intro n hn a
  let i : Fin (4*m) := ⟨n%(4*m), Nat.mod_lt _ (by have := hm.pos; positivity)⟩
  exact hbound i n ((Finset.le_sup (Finset.mem_univ i)).trans hn) (Nat.mod_modEq _ _).symm a

end Hadamard.Arithmetic
