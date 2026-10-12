/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Locally finite type objects under base change

This file records preservation of locally finite type structure morphisms by
the canonical pullback functor between slice categories of schemes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyOfFiniteType

/-- The structure morphism of an object pulled back in a slice is locally of finite type. -/
instance instOverPullbackObj {S S' : Scheme.{u}} (g : S' ⟶ S)
    (X : Over S) [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType ((Over.pullback g).obj X).hom :=
  MorphismProperty.baseChange_obj (P := @LocallyOfFiniteType) g X inferInstance

end AlgebraicGeometry.LocallyOfFiniteType
