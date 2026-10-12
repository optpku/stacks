/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.LinearAlgebra.ExteriorPower.Forms
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

@[expose] public section
universe u
namespace CrystallineFormWedge
variable (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]

/-- The degree-zero and degree-one presentation changes are the standard
exterior-power equivalences; higher degrees are unchanged. -/
noncomputable def toExterior (n : ℕ) : exteriorPower.form R M n ≃ₗ[R] ⋀[R]^n M :=
  match n with
  | 0 => (exteriorPower.zeroEquiv R M).symm
  | 1 => (exteriorPower.oneEquiv R M).symm
  | _ + 2 => LinearEquiv.refl _ _

/-- Exterior multiplication on actual homogeneous exterior powers. -/
noncomputable def exteriorMul (a b : ℕ) :
    (⋀[R]^a M) →ₗ[R] (⋀[R]^b M) →ₗ[R] (⋀[R]^(a + b) M) :=
  LinearMap.mk₂ R
    (fun x y ↦ ⟨x.val * y.val, SetLike.mul_mem_graded x.property y.property⟩)
    (by intros; apply Subtype.ext; exact add_mul _ _ _)
    (by intros; apply Subtype.ext; exact smul_mul_assoc _ _ _)
    (by intros; apply Subtype.ext; exact mul_add _ _ _)
    (by intros; apply Subtype.ext; exact mul_smul_comm _ _ _)

/-- Wedge on the ring/module/higher-form presentation, without identifying
PD forms with ordinary Kähler differentials. -/
noncomputable def wedge (a b : ℕ) :
    exteriorPower.form R M a →ₗ[R]
      exteriorPower.form R M b →ₗ[R] exteriorPower.form R M (a + b) :=
  LinearMap.mk₂ R
    (fun x y ↦ (toExterior R M (a + b)).symm
      (exteriorMul R M a b (toExterior R M a x) (toExterior R M b y)))
    (by intros; simp)
    (by intros; simp)
    (by intros; simp)
    (by intros; simp)

end CrystallineFormWedge
