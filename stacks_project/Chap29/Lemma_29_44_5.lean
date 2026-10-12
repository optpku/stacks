/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 29.44.5 (1): A composition of finite morphisms is finite. -/
@[stacks 01WK] #check (@AlgebraicGeometry.IsFinite.instCompScheme :
  ∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    {Z : AlgebraicGeometry.Scheme} (g : Y ⟶ Z)
    [AlgebraicGeometry.IsFinite f] [AlgebraicGeometry.IsFinite g],
    AlgebraicGeometry.IsFinite (f ≫ g))

/- Lemma 29.44.5 (2): A composition of integral morphisms is integral. -/
@[stacks 01WK] #check (@AlgebraicGeometry.IsIntegralHom.instCompScheme :
  ∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.IsIntegralHom f] [AlgebraicGeometry.IsIntegralHom g],
    AlgebraicGeometry.IsIntegralHom (f ≫ g))
