module

public import ReasLib.Algebra.Category.CommAlgCat.TopologicallyFiniteType.BaseChange

/-!
# Maps into completed tensor products

The left tensor inclusion induces a ring homomorphism into the completion,
compatible with the scalar maps from the common base ring.
-/

@[expose] public section

open Algebra.TopologicallyFiniteType
open scoped TensorProduct

noncomputable section

universe u

variable {A1 A2 : Type u} [CommRing A1] [CommRing A2] [Algebra A1 A2]

namespace CommAlgCat.TopologicallyFiniteType

/-- The composite `B → B ⊗[A1] A2 → (B ⊗[A1] A2)^∧`. -/
def includeLeftToCompletion (I2 : Ideal A2) (B : Type u)
    [CommRing B] [Algebra A1 B] :
    B →+* completedBaseChange A1 I2 B :=
  (algebraMap (B ⊗[A1] A2) (completedBaseChange A1 I2 B)).comp
    Algebra.TensorProduct.includeLeftRingHom

/-- `includeLeftToCompletion` sends `b` to the class of `b ⊗ₜ 1` in the
completion. -/
theorem includeLeftToCompletion_apply (I2 : Ideal A2) (B : Type u)
    [CommRing B] [Algebra A1 B] (b : B) :
    includeLeftToCompletion I2 B b =
      algebraMap (B ⊗[A1] A2) (completedBaseChange A1 I2 B) (b ⊗ₜ 1) := sorry

/-- The left inclusion commutes with the scalar maps from the common base ring. -/
theorem includeLeftToCompletion_comp (I2 : Ideal A2) (B : Type u)
    [CommRing B] [Algebra A1 B] :
    (includeLeftToCompletion I2 B).comp (algebraMap A1 B) =
      (algebraMap A2 (completedBaseChange A1 I2 B)).comp (algebraMap A1 A2) := by
  exact congrArg (fun f ↦ (algebraMap (B ⊗[A1] A2)
    (completedBaseChange A1 I2 B)).comp f)
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap

end CommAlgCat.TopologicallyFiniteType
