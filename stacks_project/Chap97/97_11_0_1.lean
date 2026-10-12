/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.RestrictScalars.Pair
import StacksCheckRecall

open CategoryTheory

universe u

/- 97.11.0.1: For morphisms `f : X ⟶ Z` and `g : Z ⟶ B` of algebraic spaces
over a scheme `S` and a scheme `T` over `S`, a pair `(a, b)` is a morphism
`a : T ⟶ B` together with a morphism `b : T ×_{a,B} Z ⟶ X` over `Z`, i.e. the
displayed commutative diagram whose lower square is the fibre product
`pullback a g` and whose triangle is `b` over `Z`. -/
@[stacks 05Y9] #check (AlgebraicGeometry.AlgebraicSpace.RestrictScalars.Pair :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Z B : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Z) → (Z ⟶ B) → AlgebraicGeometry.AlgebraicSpace S → Type (u + 1))
