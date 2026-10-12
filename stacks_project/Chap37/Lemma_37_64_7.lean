/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Descent
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 37.64.7: if `X ⟶ Y ⟶ Z` has `X ⟶ Y` flat and surjective and the
diagonal `pullback.diagonal (X ⟶ Z)` is flat, then the diagonal of `Y ⟶ Z` is
flat. -/
@[stacks 094V] #check
  (AlgebraicGeometry.Scheme.Hom.flat_diagonal_of_flat_surjective :
    ∀ {X Y Z : Scheme.{u}} (h : X ⟶ Y) (f : Y ⟶ Z) [Flat h] [Surjective h]
      [Flat (pullback.diagonal (h ≫ f))], Flat (pullback.diagonal f))
