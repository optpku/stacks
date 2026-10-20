module

public import ReasLib.Algebra.KTheory.Milnor.Basic
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel

@[expose] public section

noncomputable section

universe u

namespace MilnorK

/-- The tensor-algebra augmentation sends every positive-degree generator to zero. -/
private def tensorAugmentation (F : Type u) [Field F] :
    TensorAlgebra ℤ (Additive Fˣ) →+* ℤ :=
  (TensorAlgebra.lift ℤ (0 : Additive Fˣ →ₗ[ℤ] ℤ)).toRingHom

/-- The tensor-algebra augmentation annihilates the Steinberg ideal. -/
private theorem steinbergIdeal_le_ker_tensorAugmentation (F : Type u) [Field F] :
    steinbergIdeal F ≤ TwoSidedIdeal.ker (tensorAugmentation F) := sorry

/-- The augmentation of the Milnor K-ring sends positive-degree generators to zero. -/
@[no_expose] def augmentation (F : Type u) [Field F] : Ring F →+* ℤ :=
  (steinbergIdeal F).ringCon.lift (tensorAugmentation F)
    (fun _ _ h ↦
      (TwoSidedIdeal.ringCon_le_iff.mp (steinbergIdeal_le_ker_tensorAugmentation F)) h)

/-- Restriction of the Milnor K-ring augmentation to degree zero. -/
def degreeZeroInverse (F : Type u) [Field F] : Group 0 F →+ ℤ :=
  (augmentation F).toAddMonoidHom.comp (degree 0 F).subtype.toAddMonoidHom

/-- Augmentation recovers the integer defining a degree-zero Milnor K-class. -/
theorem degreeZeroInverse_degreeZeroMap (F : Type u) [Field F] (n : ℤ) :
    degreeZeroInverse F (degreeZeroMap F n) = n := sorry

/-- Every degree-zero Milnor K-class is the class of its augmentation. -/
theorem degreeZeroMap_degreeZeroInverse (F : Type u) [Field F] (a : Group 0 F) :
    degreeZeroMap F (degreeZeroInverse F a) = a := sorry

/-- The canonical additive identification of the integers with degree-zero Milnor K-theory. -/
def degreeZeroEquiv (F : Type u) [Field F] : ℤ ≃+ Group 0 F where
  toFun := degreeZeroMap F
  invFun := degreeZeroInverse F
  left_inv := degreeZeroInverse_degreeZeroMap F
  right_inv := degreeZeroMap_degreeZeroInverse F
  map_add' := (degreeZeroMap F).map_add

/-- The degree-zero identification sends an integer to its canonical Milnor K-class. -/
theorem degreeZeroEquiv_apply (F : Type u) [Field F] (n : ℤ) :
    degreeZeroEquiv F n = degreeZeroMap F n := rfl

/-- The inverse degree-zero identification is the restriction of augmentation. -/
theorem degreeZeroEquiv_symm_apply (F : Type u) [Field F] (a : Group 0 F) :
    (degreeZeroEquiv F).symm a = degreeZeroInverse F a := rfl

end MilnorK
