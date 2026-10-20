/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.TrivSqZeroExt
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition

/-!
# Square-zero extensions of ringed-space module sheaves

The structure sheaf of a ringed space together with a module sheaf gives the
canonical square-zero extension used for first-order thickenings.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The square-zero extension of the structure sheaf by a module sheaf. -/
noncomputable def squareZeroSheaf {X : RingedSpace.{u}} (M : X.Modules) :
    TopCat.Sheaf CommRingCat.{u} X :=
  SheafOfModules.RingedSite.TrivSqZeroExt.trivSqZeroExt
    (J := Opens.grothendieckTopology X.toPresheafedSpace) X.sheaf M

namespace SquareZeroSheaf

/-- The projection from the square-zero extension to the structure sheaf. -/
noncomputable def fst {X : RingedSpace.{u}} (M : X.Modules) :
    squareZeroSheaf M ⟶ X.sheaf :=
  SheafOfModules.RingedSite.TrivSqZeroExt.fst
    (J := Opens.grothendieckTopology X.toPresheafedSpace) X.sheaf M

/-- The canonical inclusion of the structure sheaf into the square-zero extension. -/
noncomputable def inl {X : RingedSpace.{u}} (M : X.Modules) :
    X.sheaf ⟶ squareZeroSheaf M :=
  SheafOfModules.RingedSite.TrivSqZeroExt.inl
    (J := Opens.grothendieckTopology X.toPresheafedSpace) X.sheaf M

end SquareZeroSheaf

end AlgebraicGeometry.RingedSpace
