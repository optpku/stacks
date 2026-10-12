/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Determinant.Invertible
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Determinant
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Rank.Invertible
import Mathlib.Tactic.CrossRefAttribute

/-!
# Determinant sheaves on locally ringed spaces

Over a locally ringed space, tensor-invertible module sheaves are finite locally free of rank one.
Applying this to the intrinsic determinant gives the rank-one consequence of its invertibility.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.Determinant

variable {X : LocallyRingedSpace.{u}}

/-- On a locally ringed space, an invertible determinant sheaf is finite locally free of rank
one.  In particular, the 0FJN flat finitely presented determinant instance supplies this
hypothesis automatically. -/
@[stacks 0FJN "locally ringed rank-one consequence"]
theorem rankOne
    (F : X.Modules) [isInvertibleObject (RingedSpace.Determinant.sheaf F)] :
    SheafOfModules.IsFiniteLocallyFreeOfRank 1
      (RingedSpace.Determinant.sheaf F) := sorry

end AlgebraicGeometry.LocallyRingedSpace.Determinant
