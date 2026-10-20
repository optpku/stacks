/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening.FlatLift.Obstruction
import StacksCheckRecall

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Modules
open AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension
open AlgebraicGeometry.RingedSpace.Thickening.Hom
open scoped AlgebraicGeometry

universe u

/- Lemma 91.5.7
For a strict morphism of first-order thickenings and a module flat over the closed base,
a flat lift exists exactly when the canonical ideal tensor comparison is invertible and
the infinitesimal obstruction for the identity comparison vanishes. -/
@[stacks 08LN] #check (AlgebraicGeometry.RingedSpace.Thickening.Hom.exists_flatLift_iff :
  ∀ {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
    (g : T ⟶ U) (F : T.left.Modules) [SheafOfModules.IsFlatOver F g.left]
    (hg : IsStrict g) [HasExt.{u} T.left.Modules],
    Nonempty (FlatLift g F) ↔
      IsIso (sourceIdealTensorMap g F) ∧
        existenceObstruction T.hom F (idealModule T.hom ⊗ F)
          (identityInfinitesimalMap T.hom F) = 0)
