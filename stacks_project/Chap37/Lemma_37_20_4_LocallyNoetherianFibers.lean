/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyNoetherianFibers

universe u

/- This compatibility module exposes the shared property at its historical import path. -/
#check
  (AlgebraicGeometry.LocallyNoetherianFibers :
    CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
