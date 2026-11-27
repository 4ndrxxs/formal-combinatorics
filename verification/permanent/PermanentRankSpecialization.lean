import QuinticGramBasics

/-! Rank gain from polynomial columns whose images have second-order zeros. -/
noncomputable section
open Matrix Finset Polynomial
namespace PermanentSpecialization
variable {K E S : Type*} [Field K]

def ev {I J : Type*} (t : K) (A : Matrix I J K[X]) : Matrix I J K := A.map (evalRingHom t)
def constMat {I J : Type*} (A : Matrix I J K) : Matrix I J K[X] := A.map Polynomial.C

@[simp] theorem ev_const {I J : Type*} (t : K) (A : Matrix I J K) : ev t (constMat A)=A := by
  ext i j; simp [ev,constMat]
theorem ev_mul {I J T : Type*} [Fintype J] (t : K) (A : Matrix I J K[X]) (B : Matrix J T K[X]) :
    ev t (A*B)=ev t A*ev t B := Matrix.map_mul
theorem ev_det {I : Type*} [Fintype I] [DecidableEq I] (t : K) (A : Matrix I I K[X]) :
    A.det.eval t=(ev t A).det := (evalRingHom t).map_det A

def joinRows {I J T F : Type*} (A : Matrix I T F) (B : Matrix J T F) : Matrix (I⊕J) T F :=
  Matrix.of (fun i ↦ Sum.elim A B i)
def joinCols {I J T F : Type*} (A : Matrix T I F) (B : Matrix T J F) : Matrix T (I⊕J) F :=
  Matrix.of (fun i ↦ Sum.elim (A i) (B i))

theorem pack {I J T U V F : Type*} [CommRing F] [Fintype T]
    (A : Matrix I T F) (B : Matrix J T F) (C : Matrix T U F) (D : Matrix T V F) :
    joinRows A B*joinCols C D=Matrix.fromBlocks (A*C) (A*D) (B*C) (B*D) := by
  ext i j
  cases i <;> cases j <;> rfl

theorem mul_join {I J T U F : Type*} [CommRing F] [Fintype T]
    (A : Matrix I T F) (C : Matrix T J F) (D : Matrix T U F) :
    A*joinCols C D=joinCols (A*C) (A*D) := by
  ext i j
  cases j <;> rfl

theorem ev_cols {I J T : Type*} (t : K) (A : Matrix T I K[X]) (B : Matrix T J K[X]) :
    ev t (joinCols A B)=joinCols (ev t A) (ev t B) := by
  ext i j
  cases j <;> rfl

theorem compression [Fintype E] [DecidableEq E] (H : Matrix E E K) :
    ∃ A : Matrix (Fin H.rank) E K, ∃ B : Matrix E (Fin H.rank) K, A*H*B=1 := by
  obtain ⟨V,U,e,_,_,red⟩ := Matrix.exists_rank_normal_form H
  let f : Fin H.rank→E := fun j ↦ e.symm (.inl j)
  refine ⟨V.submatrix f id,U.submatrix id f,?_⟩
  change (V*H*U).submatrix f f=1
  rw [red]
  ext i j
  simp [f,Matrix.submatrix,Matrix.fromBlocks]

theorem rank_gain [Fintype E] [DecidableEq E] [Fintype S] [DecidableEq S] [Infinite K]
    (H : Matrix E E K[X]) (L : Matrix S E K) (Y : Matrix E S K[X])
    (g : K[X]) (g0 : g.eval 0≠0)
    (ker : L*ev 0 H=0) (gain : (L*ev 0 Y).det≠0)
    (im : ∀ t : K,t≠0→∃ Z : Matrix E S K,ev t Y=ev t H*Z) :
    ∃ t : K,g.eval t≠0 ∧ (ev 0 H).rank+Fintype.card S≤(ev t H).rank := by
  classical
  obtain ⟨A,B,hAB⟩ := compression (ev 0 H)
  let R := joinRows A L
  let D := constMat R*joinCols (H*constMat B) Y
  have spec (t : K) : ev t D=R*joinCols (ev t H*B) (ev t Y) := by
    simp only [D,ev_mul,ev_cols,ev_const]
  have at0 := spec 0
  change ev 0 D=joinRows A L*joinCols (ev 0 H*B) (ev 0 Y) at at0
  rw [pack,←Matrix.mul_assoc,←Matrix.mul_assoc L,ker,Matrix.zero_mul,hAB] at at0
  have nd0 : D.det.eval 0≠0 := by
    rw [ev_det,at0,Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,one_mul]
    exact gain
  have ng : g≠0 := fun h ↦ g0 (by rw [h,Polynomial.eval_zero])
  have nd : D.det≠0 := fun h ↦ nd0 (by rw [h,Polynomial.eval_zero])
  have nonzero : (Polynomial.X*g)*D.det≠0 := mul_ne_zero (mul_ne_zero X_ne_zero ng) nd
  obtain ⟨t,ht⟩ : ∃ t : K,((Polynomial.X*g)*D.det).eval t≠0 := by
    by_contra! h
    exact nonzero (Polynomial.funext (by simpa using h))
  simp only [Polynomial.eval_mul,Polynomial.eval_X,ne_eq,mul_eq_zero,not_or] at ht
  obtain ⟨⟨tnz,gtnz⟩,dtnz⟩ := ht
  obtain ⟨Z,hZ⟩ := im t tnz
  have hD := spec t
  rw [hZ,←mul_join,←Matrix.mul_assoc] at hD
  have full := Matrix.rank_of_det_ne_zero ((ev_det t D) ▸ dtnz)
  have bound := (Matrix.rank_mul_le_left (R*ev t H) (joinCols B Z)).trans
    (Matrix.rank_mul_le_right R (ev t H))
  rw [←hD,full,Fintype.card_sum,Fintype.card_fin] at bound
  exact ⟨t,gtnz,bound⟩

end PermanentSpecialization
