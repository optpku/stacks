/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Regular.Locality

universe u

/- This compatibility module exposes regular scheme morphisms at its historical import path. -/
#check
  (@AlgebraicGeometry.Regular :
    CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
