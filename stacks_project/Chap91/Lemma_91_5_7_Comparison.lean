/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.Comparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening.IdealTensor

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Modules
open AlgebraicGeometry.RingedSpace.Thickening.Hom
open scoped AlgebraicGeometry

universe u

section Intrinsic

variable {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsFirstOrderThickening i]

#check (AlgebraicGeometry.RingedSpace.Modules.infinitesimalMap_ofRestrict i :
  {F K : X.Modules} → (idealModule i ⊗ F ⟶ K) →
    (kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K))

#check (AlgebraicGeometry.RingedSpace.Modules.infinitesimalMap_ofRestrict_eq i :
  ∀ {F K : X.Modules} (φ : idealModule i ⊗ F ⟶ K),
    infinitesimalMap_ofRestrict i φ =
      (pullbackPushforwardAdjunction i).homEquiv
        (kernelIdealSheaf i ⊗ (i _*).obj F) K
        ((Functor.Monoidal.μIso (pullback i) (kernelIdealSheaf i) ((i _*).obj F)).inv ≫
          tensorHom (𝟙 (idealModule i))
            (asIso ((pullbackPushforwardAdjunction i).counit.app F)).hom ≫ φ))

#check (AlgebraicGeometry.RingedSpace.Modules.infinitesimalMap_restrict_ofRestrict i :
  ∀ {F K : X.Modules} (φ : idealModule i ⊗ F ⟶ K),
    infinitesimalMap_restrict i (infinitesimalMap_ofRestrict i φ) = φ)

#check (AlgebraicGeometry.RingedSpace.Modules.identityInfinitesimalMap i :
  (F : X.Modules) →
    (kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj (idealModule i ⊗ F)))

#check (AlgebraicGeometry.RingedSpace.Modules.identityInfinitesimalMap_restrict i :
  ∀ (F : X.Modules), infinitesimalMap_restrict i (identityInfinitesimalMap i F) =
    𝟙 (idealModule i ⊗ F))

end Intrinsic

section Relative

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]

#check (AlgebraicGeometry.RingedSpace.Thickening.Hom.sourceIdealTensorMap :
  (g : T ⟶ U) → (F : T.left.Modules) →
    ((g.left ^*).obj (idealModule U.hom) ⊗ F ⟶ idealModule T.hom ⊗ F))

#check (AlgebraicGeometry.RingedSpace.Thickening.Hom.sourceIdealTensorMap_eq :
  ∀ (g : T ⟶ U) (F : T.left.Modules),
    sourceIdealTensorMap g F = tensorHom (sourceIdealMap g) (𝟙 F))

end Relative
