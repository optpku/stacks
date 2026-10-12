/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening

/-!
# Morphisms of thickenings of ringed spaces

Bundled thickenings of ringed spaces are arrows whose structural morphism is a thickening.
Morphisms of thickenings are commutative squares of ringed spaces.
-/

open CategoryTheory

universe u

#check (AlgebraicGeometry.RingedSpace.Thickening.homMk :
  {T U : AlgebraicGeometry.RingedSpace.Thickening.{u}} →
    (f : T.left ⟶ U.left) → (f' : T.right ⟶ U.right) →
      f ≫ U.hom = T.hom ≫ f' → (T ⟶ U))
