module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit

/-! # Pullback of the structure module -/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Ordinary pullback of the structure module is the structure module. Both
identifications with the ambient tensor units are explicit. -/
def pullbackStructureSheafIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (pullback g).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  (pullback g).mapIso
      (SheafOfModules.RingedSite.unitIsoTensorUnit
        (J := Opens.grothendieckTopology Y.toTopCat) (𝒪 := Y.𝒪)) ≪≫
    pullbackUnitIso g ≪≫
    (SheafOfModules.RingedSite.unitIsoTensorUnit
      (J := Opens.grothendieckTopology X.toTopCat) (𝒪 := X.𝒪)).symm

/-- The structure-module comparison factors through the canonical monoidal unit
map and the explicit sheafification-unit comparisons. -/
theorem pullbackStructureSheafIso_hom {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (pullbackStructureSheafIso g).hom =
      (pullback g).map
          (SheafOfModules.RingedSite.unitIsoTensorUnit
            (J := Opens.grothendieckTopology Y.toTopCat) (𝒪 := Y.𝒪)).hom ≫
        (pullbackUnitIso g).hom ≫
        (SheafOfModules.RingedSite.unitIsoTensorUnit
          (J := Opens.grothendieckTopology X.toTopCat) (𝒪 := X.𝒪)).inv := rfl

end AlgebraicGeometry.Scheme.Modules
