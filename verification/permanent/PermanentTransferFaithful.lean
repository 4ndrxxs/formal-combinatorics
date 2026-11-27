import PencilInvisibleDirections
import PermanentCoordinateGradient
import PermanentTransferNilpotent

/-! The internal matrix map is injective along the common endpoint kernel
of a normalized expression for a generic permanent. The gradient witnesses
are available in every order and over every field. -/

noncomputable section
open Matrix Module LinearMap MvPolynomial QuinticPencil
namespace PermanentFive
variable {K I n : Type*} [Field K] [Fintype I] [DecidableEq I] [Fintype n] [DecidableEq n]

def kernelTransfer (b c : n → I × I → K) (D : n → n → I × I → K) :
    (endpoints b c).ker →ₗ[K] Matrix n n K where
  toFun z := transfer D z.val
  map_add' x y := by ext i j; simp [transfer,value,mul_add,Finset.sum_add_distrib]
  map_smul' a x := by ext i j; simp [transfer,value,smul_eq_mul,Finset.mul_sum,mul_left_comm]

theorem kernelTransfer_injective (b c : n → I × I → K) (D : n → n → I × I → K)
    (rep : per K I = regularDet b c D) : Function.Injective (kernelTransfer b c D) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro z hz
  change z = 0
  apply Subtype.ext
  funext u
  obtain ⟨y,grad⟩ := permanent_coordinate_gradient (K:=K) u
  have identity := invisible_direction (per K I) b c D rep z.val z.property hz y
  simpa [grad,mul_ite] using identity

theorem kernelTransfer_finrank (b c : n → I × I → K) (D : n → n → I × I → K)
    (rep : per K I = regularDet b c D) :
    finrank K (kernelTransfer b c D).range = finrank K (endpoints b c).ker :=
  LinearMap.finrank_range_of_inj (kernelTransfer_injective b c D rep)

/-- A five-by-five permanent pencil therefore contains an actual linear
space of nilpotent internal matrices of the stated dimension. -/
theorem nilpotent_matrix_space [CharZero K] (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) :
    ∃ T : Submodule K (Matrix n n K), finrank K T = finrank K (endpoints b c).ker ∧
      ∀ A ∈ T, IsNilpotent A := by
  refine ⟨(kernelTransfer b c D).range,kernelTransfer_finrank b c D rep,?_⟩
  rintro _ ⟨x,rfl⟩
  exact endpoint_transfer_nilpotent b c D rep x.val x.property

#print axioms kernelTransfer_injective
#print axioms kernelTransfer_finrank
#print axioms nilpotent_matrix_space
end PermanentFive
