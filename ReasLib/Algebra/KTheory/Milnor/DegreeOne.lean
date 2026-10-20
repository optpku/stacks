/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.KTheory.Milnor.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel

@[expose] public section

noncomputable section

universe u

namespace MilnorK

section

variable (F : Type u) [Field F] [Module ℤᵐᵒᵖ (Additive Fˣ)]
  [IsCentralScalar ℤ (Additive Fˣ)]

/-- The square-zero truncation retains the scalar and degree-one tensor components. -/
private def tensorTruncation :=
  (TensorAlgebra.toTrivSqZeroExt :
    TensorAlgebra ℤ (Additive Fˣ) →ₐ[ℤ] TrivSqZeroExt ℤ (Additive Fˣ)).toRingHom

/-- Square-zero truncation annihilates the two-sided Steinberg ideal. -/
private theorem steinbergIdeal_le_ker_tensorTruncation :
    steinbergIdeal F ≤ TwoSidedIdeal.ker (tensorTruncation F) := by
  apply TwoSidedIdeal.span_le.mpr
  rintro z ⟨x, y, hxy, rfl⟩
  apply (TwoSidedIdeal.mem_ker _).mpr
  simp [tensorTruncation, TensorAlgebra.toTrivSqZeroExt, TensorAlgebra.lift_ι_apply,
    TrivSqZeroExt.inr_mul_inr]

/-- The scalar and degree-one components descend to the Milnor K-ring. -/
private def ringTruncation :=
  (steinbergIdeal F).ringCon.lift (tensorTruncation F)
    (fun _ _ h ↦
      (TwoSidedIdeal.ringCon_le_iff.mp (steinbergIdeal_le_ker_tensorTruncation F)) h)

/-- Projection of the square-zero truncation onto the additive group of units. -/
private def additiveTruncation : Ring F →+ Additive Fˣ :=
  (TrivSqZeroExt.sndHom ℤ (Additive Fˣ)).toAddMonoidHom.comp
    (ringTruncation F).toAddMonoidHom

end

/-- The degree-one component of a Milnor K-class, in the additive group of units. -/
@[no_expose] def degreeOneInverse (F : Type u) [Field F] : Group 1 F →+ Additive Fˣ :=
  (@additiveTruncation F _
      (Module.compHom _ ((RingHom.id ℤ).fromOpposite mul_comm))
      (@IsCentralScalar.mk ℤ (Additive Fˣ) inferInstance
        (Module.compHom (Additive Fˣ) ((RingHom.id ℤ).fromOpposite mul_comm)).toSMul
        (fun _ _ ↦ rfl))).comp (degree 1 F).subtype.toAddMonoidHom

/-- Taking the degree-one component recovers the unit defining a Milnor K-class. -/
theorem degreeOneInverse_degreeOneMap (F : Type u) [Field F] (a : Additive Fˣ) :
    degreeOneInverse F (degreeOneMap F a) = a := sorry

/-- Every degree-one Milnor K-class is represented by its degree-one component. -/
theorem degreeOneMap_degreeOneInverse (F : Type u) [Field F] (a : Group 1 F) :
    degreeOneMap F (degreeOneInverse F a) = a := sorry

end MilnorK
