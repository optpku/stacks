/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening.FlatLift.Obstruction

/-!
# Identification `ℐ = f^* 𝒥` along a strict flat first-order thickening

The shared obstruction module owns the ideal comparison and the relative identity
infinitesimal extension. The checks below retain the source interfaces, including
all three data fields of the extension transported from the identity extension.
-/

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Modules
open AlgebraicGeometry.RingedSpace.Thickening.Hom
open scoped AlgebraicGeometry

universe u

section Comparison

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
variable (g : T ⟶ U) (hg : IsStrict g) [RingedSpace.Hom.IsFlat g.right]
variable (F : T.left.Modules)

#check (AlgebraicGeometry.RingedSpace.Thickening.Hom.isIso_sourceIdealMap hg :
  IsIso (sourceIdealMap g))
#check (sourceIdealIso hg : (g.left^*).obj (idealModule U.hom) ≅ idealModule T.hom)
#check @AlgebraicGeometry.RingedSpace.Thickening.Hom.sourceIdealIso_hom
#check (AlgebraicGeometry.RingedSpace.Thickening.Hom.isIso_sourceIdealTensorMap hg F :
  IsIso (sourceIdealTensorMap g F))
#check (AlgebraicGeometry.RingedSpace.Thickening.Hom.sourceIdealTensorIso hg F :
  (g.left^*).obj (idealModule U.hom) ⊗ F ≅ idealModule T.hom ⊗ F)
#check @AlgebraicGeometry.RingedSpace.Thickening.Hom.sourceIdealTensorIso_hom

#check (relativeIdentityInfinitesimalMap g hg F :
  kernelIdealSheaf T.hom ⊗ (T.hom _*).obj F ⟶
    (T.hom _*).obj ((g.left^*).obj (idealModule U.hom) ⊗ F))
#check @AlgebraicGeometry.RingedSpace.Modules.relativeIdentityInfinitesimalMap_restrict

variable [SheafOfModules.IsFlatOver F g.left] (L : FlatLift g F)

#check (FlatLift.toRelativeInfinitesimalExtension hg L :
  InfinitesimalExtension T.hom F ((g.left^*).obj (idealModule U.hom) ⊗ F)
    (relativeIdentityInfinitesimalMap g hg F))
#check (FlatLift.toRelativeInfinitesimalExtension_module hg L :
  (FlatLift.toRelativeInfinitesimalExtension hg L).module = L.module)
#check (FlatLift.toRelativeInfinitesimalExtension_ι hg L :
  (FlatLift.toRelativeInfinitesimalExtension hg L).ι =
    (T.hom _*).map (FlatLift.sourceIdealTensorIso hg F).hom ≫
      (FlatLift.toInfinitesimalExtension hg L).ι)
#check (FlatLift.toRelativeInfinitesimalExtension_π hg L :
  (FlatLift.toRelativeInfinitesimalExtension hg L).π =
    (FlatLift.toInfinitesimalExtension hg L).π)
#check @AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift.sourceIdealBraid
#check @AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift.sourceIdealBraid_hom
#check @AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift.isIso_sourceIdealMulMap

end Comparison
