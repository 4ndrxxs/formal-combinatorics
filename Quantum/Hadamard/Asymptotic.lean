import Quantum.Hadamard.PaleyCore
import Quantum.Hadamard.Regular
import Quantum.Hadamard.AsymptoticBuild

/-! For every odd prime modulus, all sufficiently large multiples of four
are orders of modular Hadamard matrices. The threshold may depend on the prime. -/
noncomputable section
namespace HadamardMod
open Hadamard.Arithmetic

theorem primeConstruction (m : ℕ) : PrimeOrderConstruction m (AtOrder m) where
  paley := by
    intro q hq h4
    letI : Fact q.Prime := ⟨hq⟩
    exact paley_order m q h4
  productGrow := by
    intro q p n hq h4 step pos hn res t
    letI : Fact q.Prime := ⟨hq⟩
    letI : Fact p.Prime := ⟨step.prime⟩
    have pq : (((p*q:ℕ):ZMod m))=1 := by
      simpa using (ZMod.natCast_eq_natCast_iff _ _ m).mpr step.prodOne
    let D := lexExtension (paleySkew m p step.modFour) (paleySkew m q h4).inner
      (by simpa only [ZMod.card] using pq)
    have rn : (n:ZMod m)=1+(Fintype.card (ZMod q):ZMod m) := by
      simpa [add_comm] using (ZMod.natCast_eq_natCast_iff _ _ m).mpr res
    simpa [Fintype.card_prod,ZMod.card] using D.iterate pos hn rn t
  doublePaley := by
    intro q seed
    letI : Fact q.Prime := ⟨seed.prime⟩
    exact paley_double m q seed.modFour
  squareGrow := by
    intro q n seed pos hn res t
    letI : Fact q.Prime := ⟨seed.prime⟩
    have d : (squareOrder q:ZMod m)=1 := by
      simpa using (ZMod.natCast_eq_natCast_iff _ _ m).mpr seed.orderOne
    have r : (n:ZMod m)=1 := by
      simpa using (ZMod.natCast_eq_natCast_iff _ _ m).mpr res
    apply square_grow (h:=squareOrder q) _ (paley_double m q seed.modFour) d pos hn r
    dsimp [squareOrder]
    omega

theorem all_large_four_mod_prime {p:ℕ} (hp:p.Prime) (odd:2<p) :
    ∃ N : ℕ, ∀ n ≥ N, 4 ∣ n → AtOrder p n :=
  all_large hp odd (primeConstruction p)

theorem all_large_four_integer_gram {p:ℕ} (hp:p.Prime) (odd:2<p) :
    ∃ N : ℕ, ∀ n ≥ N, 4 ∣ n → IntegralSolution p n := by
  obtain ⟨N,hn⟩:=all_large_four_mod_prime hp odd
  exact ⟨N,fun n large four => integer_gram (hn n large four)⟩

#print axioms all_large_four_mod_prime
#print axioms all_large_four_integer_gram
end HadamardMod
