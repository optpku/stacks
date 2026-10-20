module

public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.Comparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening.IdealTensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening.FlatLift
public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening.Strict

/-!
# Obstructions to relatively flat module lifts

The identity infinitesimal obstruction and the canonical ideal tensor comparison
characterize relatively flat lifts along strict morphisms of first-order thickenings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Modules
open AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening
namespace Hom

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
variable (g : T ⟶ U) (F : T.left.Modules)

/-- For a strict morphism of first-order thickenings and a relatively flat module, a
flat lift exists exactly when the canonical ideal tensor comparison is an isomorphism
and the infinitesimal obstruction for the identity comparison vanishes. -/
theorem exists_flatLift_iff [SheafOfModules.IsFlatOver F g.left] (hg : IsStrict g)
    [HasExt.{u} T.left.Modules] :
    Nonempty (FlatLift g F) ↔
      IsIso (sourceIdealTensorMap g F) ∧
        existenceObstruction T.hom F (idealModule T.hom ⊗ F)
          (identityInfinitesimalMap T.hom F) = 0 := sorry

end Hom
end AlgebraicGeometry.RingedSpace.Thickening
