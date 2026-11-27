module
public import Quantum.SudokuTradeGrid

/-! The two quantum completions differ even as rank-one projections: a specified
cell of the second has two nonzero computational coordinates. -/
@[expose] public section
noncomputable section
namespace SudokuTrade
variable [C : Config] [L : Laws]
include L
open QuantumSudoku QuantumCertificate

def coordinateBoard (r c : Pair) : H I := axis (baseline r c)

private theorem coordinate_basis {f : Pair→Pair} (h : Function.Injective f) :
    BasisLine (fun k => axis (f k)) := by
  apply basis_of_gram
  intro i j
  simp only [axis_inner,h.eq_iff]

theorem coordinate_valid : Valid coordinateBoard := by
  refine ⟨fun r => coordinate_basis (baseline_ordinary.1 r).1,
    fun c => coordinate_basis (baseline_ordinary.2.1 c).1,
    fun x y => coordinate_basis (baseline_ordinary.2.2 x y).1⟩

theorem coordinate_completes : QuantumCompletes puzzle coordinateBoard := by
  refine ⟨coordinate_valid,?_⟩
  intro r c k hp
  obtain rfl := (baseline_completes.2 r c k hp).symm
  exact ⟨1,by simp [coordinateBoard]⟩

theorem value_at_cell (x r : I) (i : Color) :
    quantumBoard (activeCell x r i).1 (activeCell x r i).2=spread (smallVec r i) := by
  change value r (baseline (activeCell x r i).1 (activeCell x r i).2)=_
  rw [baseline_active,value_active]

theorem nonzero_coordinate {r : I} {i j : Color} (h : num (ray r i) j≠(0,0)) :
    quantumBoard (activeCell 0 r i).1 (activeCell 0 r i).2 (activeAxis j)≠0 := by
  rw [value_at_cell,spread_at]
  have nz : embed 1 (num (ray r i) j)≠0 := by
    intro eq
    apply h
    exact embed_injective (by decide : 0<1) (eq.trans (map_zero (embed 1)).symm)
  change (Real.sqrt (16:ℝ):ℂ)⁻¹*embed 1 (num (ray r i) j)≠0
  exact mul_ne_zero (by norm_num) nz

theorem noncoordinate {r : I} {i j l : Color} (hl : j≠l)
    (hj : num (ray r i) j≠(0,0)) (hk : num (ray r i) l≠(0,0)) (k : Pair) (a : ℂ) :
    quantumBoard (activeCell 0 r i).1 (activeCell 0 r i).2≠a • axis k := by
  intro eq
  have zeroAt (t : Color) (ne : activeAxis t≠k) :
      quantumBoard (activeCell 0 r i).1 (activeCell 0 r i).2 (activeAxis t)=0 := by
    rw [eq]
    simp [axis,ne]
  by_cases e : activeAxis j=k
  · exact nonzero_coordinate hk (zeroAt l (fun h => hl (axis_inj (e.trans h.symm))))
  · exact nonzero_coordinate hj (zeroAt j e)

/-- The same symbol occurs at a coordinate anchor and at an explicit noncoordinate cell. -/
theorem inequivalent {r u : I} {i j l : Color} (hl : j≠l)
    (hj : num (ray r i) j≠(0,0)) (hk : num (ray r i) l≠(0,0))
    (pinned : ray u i=refRay i) : ¬Equivalent coordinateBoard quantumBoard := by
  rintro ⟨U,phase⟩
  let anchor := activeCell 0 u i
  let special := activeCell 0 r i
  have same (s : I) : coordinateBoard (activeCell 0 s i).1 (activeCell 0 s i).2=axis (activeAxis i) := by
    change axis (baseline (activeCell 0 s i).1 (activeCell 0 s i).2)=_
    rw [baseline_active]
  have atAnchor : quantumBoard anchor.1 anchor.2=axis (activeAxis i) :=
    (value_at_cell 0 u i).trans (small_reference pinned)
  obtain ⟨a,ha⟩:=phase anchor.1 anchor.2
  obtain ⟨b,hb⟩:=phase special.1 special.2
  change U (coordinateBoard (activeCell 0 u i).1 (activeCell 0 u i).2)=_ at ha
  change U (coordinateBoard (activeCell 0 r i).1 (activeCell 0 r i).2)=_ at hb
  rw [same,atAnchor] at ha
  rw [same] at hb
  have nz : (b:ℂ)≠0 := Circle.coe_ne_zero b
  apply noncoordinate hl hj hk (activeAxis i) ((b:ℂ)⁻¹*(a:ℂ))
  calc
    _ = (b:ℂ)⁻¹ • ((b:ℂ) • quantumBoard special.1 special.2) := by simp [smul_smul,nz,special]
    _ = _ := by rw [←hb,ha,smul_smul]

end SudokuTrade
