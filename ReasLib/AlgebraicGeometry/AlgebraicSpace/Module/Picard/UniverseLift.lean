/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Picard
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SheafComposition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Sheaf CategoryTheory.Functor
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open CategoryTheory.Abelian

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Invertibility of an `𝒪_Y`-module transports to its universe lift. -/
instance liftModule_isInvertibleObject {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (L : Y.Modules) [isInvertibleObject L] :
    isInvertibleObject (liftModule L) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening

variable {S : Scheme.{u}}

/-- Universe lift of an algebraic-space Picard class to the Picard group of the
lifted commutative structure sheaf. -/
def structurePicardMap (Y : AlgebraicSpace S) :
    Y.PicardGroup →+
      SheafOfModules.RingedSite.PicardGroup (smallEtaleTopology Y)
        (commStructureSheafLift Y) where
  toFun x :=
    MonoidalCategory.PicardGroup.mk (Modules.liftModule (PicardGroup.repr x))
  map_zero' := sorry
  map_add' := sorry

/-- `structurePicardMap Y` is computed by lifting a chosen representative. -/
theorem structurePicardMap_apply (Y : AlgebraicSpace S) (x : Y.PicardGroup) :
    structurePicardMap Y x =
      MonoidalCategory.PicardGroup.mk (Modules.liftModule (PicardGroup.repr x)) :=
  sorry

/-- The underlying inverse function of `structurePicardMap Y`. -/
def structurePicardInverseFunction (Y : AlgebraicSpace S) :
    SheafOfModules.RingedSite.PicardGroup (smallEtaleTopology Y)
      (commStructureSheafLift Y) → Y.PicardGroup :=
  Function.invFun (structurePicardMap Y)

/-- The inverse structure-Picard comparison sends zero to zero. -/
theorem structurePicardInverseFunction_zero (Y : AlgebraicSpace S) :
    structurePicardInverseFunction Y 0 = 0 := sorry

/-- The inverse structure-Picard comparison is additive. -/
theorem structurePicardInverseFunction_add (Y : AlgebraicSpace S)
    (x y : SheafOfModules.RingedSite.PicardGroup (smallEtaleTopology Y)
      (commStructureSheafLift Y)) :
    structurePicardInverseFunction Y (x + y) =
      structurePicardInverseFunction Y x + structurePicardInverseFunction Y y :=
  sorry

/-- The structure-Picard comparison followed by its inverse recovers an ambient
Picard class. -/
theorem structurePicardMap_leftInverse (Y : AlgebraicSpace S)
    (x : Y.PicardGroup) :
    structurePicardInverseFunction Y (structurePicardMap Y x) = x := sorry

/-- The inverse structure-Picard comparison followed by the forward comparison
recovers a lifted Picard class. -/
theorem structurePicardMap_rightInverse (Y : AlgebraicSpace S)
    (x : SheafOfModules.RingedSite.PicardGroup (smallEtaleTopology Y)
      (commStructureSheafLift Y)) :
    structurePicardMap Y (structurePicardInverseFunction Y x) = x := sorry

/-- The canonical additive equivalence between the Picard group of an algebraic
space and the Picard group of its universe-lifted commutative structure sheaf. -/
def structurePicardEquiv (Y : AlgebraicSpace S) :
    ULift.{u + 2, u + 1} Y.PicardGroup ≃+
      SheafOfModules.RingedSite.PicardGroup (smallEtaleTopology Y)
        (commStructureSheafLift Y) where
  toFun x := structurePicardMap Y x.down
  invFun y := ULift.up (structurePicardInverseFunction Y y)
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

end AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening
