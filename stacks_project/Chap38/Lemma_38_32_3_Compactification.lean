/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.Category

universe u

#check (AlgebraicGeometry.Scheme.Compactification.interiorIsomorphisms :
  ∀ (S : AlgebraicGeometry.Scheme.{u}),
    CategoryTheory.MorphismProperty (AlgebraicGeometry.Scheme.Compactification S))
