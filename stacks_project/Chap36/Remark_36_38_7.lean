/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Pushforward.Derived
import StacksCheckRecall

open CategoryTheory

universe u

/- Remark 36.38.7 (1): a proper morphism of locally Noetherian schemes induces
`f_* : K0' X →+ K0' Y`, defined using its higher direct images. -/
@[stacks 0FDL] #check
  (AlgebraicGeometry.Scheme.K0'.pushforward :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.IsLocallyNoetherian X]
      [AlgebraicGeometry.IsLocallyNoetherian Y] [AlgebraicGeometry.IsProper f],
      AlgebraicGeometry.Scheme.K0' X →+ AlgebraicGeometry.Scheme.K0' Y)

/- Remark 36.38.7 (2): proper pushforward sends the class of a coherent module to
the difference between the even and odd higher-direct-image classes. -/
@[stacks 0FDL] #check
  (AlgebraicGeometry.Scheme.K0'.pushforward_of :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.IsLocallyNoetherian X]
      [AlgebraicGeometry.IsLocallyNoetherian Y] [AlgebraicGeometry.IsProper f]
      (F : (SheafOfModules.isCoherent
        X.toRingedSpace.ringCatSheaf).FullSubcategory),
      AlgebraicGeometry.Scheme.K0'.pushforward f
          (CategoryTheory.ObjectProperty.GrothendieckGroup.of
            (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) F) =
        CategoryTheory.ObjectProperty.GrothendieckGroup.of
            (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf)
            (AlgebraicGeometry.Scheme.K0'.evenHigherDirectImages f F) -
          CategoryTheory.ObjectProperty.GrothendieckGroup.of
            (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf)
            (AlgebraicGeometry.Scheme.K0'.oddHigherDirectImages f F))

/- Remark 36.38.7 (3): on a quasi-compact target, proper pushforward is the
canonical Euler alternating sum of the classes of all higher direct images. -/
@[stacks 0FDL] #check
  (AlgebraicGeometry.Scheme.K0'.pushforward_of_eq_alternatingSum :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.IsLocallyNoetherian X]
      [AlgebraicGeometry.IsLocallyNoetherian Y] [AlgebraicGeometry.IsProper f]
      [CompactSpace Y]
      (F : (SheafOfModules.isCoherent
        X.toRingedSpace.ringCatSheaf).FullSubcategory),
      AlgebraicGeometry.Scheme.K0'.pushforward f
          (CategoryTheory.ObjectProperty.GrothendieckGroup.of
            (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) F) =
        AlgebraicGeometry.Scheme.K0'.fromAbelianK0 Y
          (CategoryTheory.DerivedCategory.Bounded.CohomologyIn.K0.Euler.value
            (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf)
            (AlgebraicGeometry.Scheme.K0'.derivedPushforward f F)))

/- Remark 36.38.7 (4): on a quasi-compact target, the proper-pushforward class
of a coherent module is the Euler class `[Rf_* F]` of its bounded derived pushforward. -/
@[stacks 0FDL] #check
  (AlgebraicGeometry.Scheme.K0'.pushforward_of_eq_derived :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.IsLocallyNoetherian X]
      [AlgebraicGeometry.IsLocallyNoetherian Y] [AlgebraicGeometry.IsProper f]
      [CompactSpace Y]
      (F : (SheafOfModules.isCoherent
        X.toRingedSpace.ringCatSheaf).FullSubcategory),
      AlgebraicGeometry.Scheme.K0'.derivedK0Equiv Y
          (AlgebraicGeometry.Scheme.K0'.pushforward f
            (CategoryTheory.ObjectProperty.GrothendieckGroup.of
              (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) F)) =
        CategoryTheory.TriangulatedK0.of
          (AlgebraicGeometry.Scheme.K0'.derivedPushforward f F))
