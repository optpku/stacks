/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.GeometricallyReduced

universe u

open CategoryTheory

#check (AlgebraicGeometry.Scheme.Hom.geometricallyReducedFiberLocus :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}}, (f : X ⟶ Y) → Set Y)
