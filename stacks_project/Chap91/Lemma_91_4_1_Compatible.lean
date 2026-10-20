module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Extension.Compatible

/-!
# Compatible maps of mixed-scalar module extensions

This source-facing module preserves the historical import path for the compatible extension API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom
namespace ModuleExtension

#check
  (AlgebraicGeometry.RingedSpace.Hom.ModuleExtension.infinitesimalMap_restrict :
    ∀ {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]
      (E : ModuleExtension i),
      idealModule i ⊗ E.cokernel ⟶ E.kernel)

#check
  (AlgebraicGeometry.RingedSpace.Hom.ModuleExtension.CompatibleMap :
    ∀ {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]
      (E E' : ModuleExtension i)
      (ψ : E.kernel ⟶ E'.kernel) (φ : E.cokernel ⟶ E'.cokernel), Type _)

end ModuleExtension
end AlgebraicGeometry.RingedSpace.Hom
