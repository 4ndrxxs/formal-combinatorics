import SignedMassEndpoint

/-! Complete numerical possibilities at norm 9p for the five possible common primes. -/

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def nineList : ℕ → List (ℕ × ℤ)
  | 5 => [(9,-1),(11,1),(19,9),(19,44),(29,4),(29,99),(31,36),(31,41),(33,12),(33,87),(57,3),(57,228),(59,4),(59,229),(71,1),(99,4),(99,409),(171,1),(171,796),(311,1),(311,1476)]
  | 7 => [(9,-1),(19,1),(27,2),(27,9),(27,37),(27,58),(27,114),(29,47),(29,54),(31,18),(31,109),(37,27),(37,118),(81,3),(81,486),(83,2),(83,513),(93,6),(93,531),(103,1),(167,2),(167,1073),(243,1),(243,1618),(279,2),(279,1829),(439,1),(439,2962)]
  | 11 => [(15,6),(19,14),(21,42),(21,75),(25,63),(25,74),(35,1),(35,45),(35,166),(37,50),(37,171),(43,9),(43,350),(45,2),(45,35),(45,266),(49,18),(49,359),(53,10),(53,439),(63,14),(63,509),(129,3),(129,1290),(133,2),(133,1355),(139,5),(139,1358),(147,6),(147,1425),(167,1),(265,2),(265,2763),(387,1),(387,4126),(441,2),(441,4655),(695,1),(695,7470)]
  | 13 => [(17,27),(17,92),(23,68),(23,81),(27,4),(27,17),(27,69),(27,108),(27,212),(29,36),(29,179),(43,1),(51,9),(51,516),(79,4),(79,901),(87,12),(87,909),(153,3),(153,1836),(157,4),(157,1863),(199,1),(261,4),(261,3163),(459,1),(459,5812),(823,1),(823,10492)]
  | 17 => [(19,72),(19,89),(57,24),(57,687),(59,1),(67,9),(67,944),(83,13),(83,1152),(89,19),(89,1192),(103,8),(103,1521),(171,8),(171,2609),(201,3),(201,3216),(263,1),(603,1),(603,10048),(1079,1),(1079,18072)]
  | _ => []

def nineGrid (p B : ℕ) : Prop := ∀ m : Fin B, p < m.val → ¬ 2 ∣ m.val → ¬ p ∣ m.val →
  ∀ d : Fin 18, ∀ upper : Bool, let c := if upper then m.val-d.val else d.val
    let l := ((p:ℤ)*c^2-9)/(m.val:ℤ)
    numericalParameter p m.val 9 c l → (m.val,l) ∈ nineList p

instance (p B : ℕ) : Decidable (nineGrid p B) := by unfold nineGrid; infer_instance

theorem grid_5 : nineGrid 5 415 := by decide +kernel
theorem grid_7 : nineGrid 7 577 := by decide +kernel
theorem grid_11 : nineGrid 11 901 := by decide +kernel
theorem grid_13 : nineGrid 13 1063 := by decide +kernel
theorem grid_17 : nineGrid 17 1387 := by decide +kernel

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] {p : ℕ} [Fact p.Prime]

theorem listed9 {m B : ℕ} {k lam : ℤ} {f : G → ℤ} (hf : IsSDS k lam f) (hg : Fintype.card G=p*m)
    (hm : p < m) (hn : k-lam=(p:ℤ)*(9:ℕ)) (hs : ¬ p ∣ 9)
    (size : ∀ t : ℕ, p*t≤(p*9)^2+p*9+1 → t<B) (grid : nineGrid p B) : (m,lam)∈nineList p := by
  obtain ⟨c,params,hL,hU⟩ := bounded_parameters hf hg hn hs hm
  have below := size m hU
  have csmall : c<18 ∨ m-c<18 := mass_endpoint (Fact.out : p.Prime).pos (by decide) params
  obtain ⟨d,mode,eq⟩ : ∃ d : Fin 18, ∃ mode : Bool, (if mode then m-d.val else d.val)=c := by
    rcases csmall with h|h
    · exact ⟨⟨c,h⟩,false,rfl⟩
    · exact ⟨⟨m-c,h⟩,true,by have cm := params.2.2.2.1; simp; omega⟩
  have gg := grid ⟨m,below⟩ hm params.2.1 params.2.2.1 d mode
  change numericalParameter p m 9 _ _ → (m,_) ∈ nineList p at gg
  simp only [eq] at gg
  norm_num at hL
  rw [← hL] at gg
  exact gg params

end Signed39.Contraction
