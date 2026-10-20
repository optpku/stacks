/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.Diagonal
import StacksCheckRecall

/-!
# Diagonal criterion for unramified morphisms of algebraic spaces

An unramified morphism of algebraic spaces has open relative diagonal, and a
locally of finite type morphism with open relative diagonal is unramified.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.38.9 (1): if `f : X ⟶ Y` is an unramified morphism of algebraic
spaces over a scheme `S`, then the relative diagonal
`pullback.diagonal f : X ⟶ X ×_Y X` is an open immersion. -/
@[stacks 05W1] #check
  (AlgebraicGeometry.AlgebraicSpace.Unramified.isOpenImmersion_diagonal :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Unramified f], IsOpenImmersion (pullback.diagonal f))

/- Lemma 67.38.9 (2): if `f : X ⟶ Y` is a locally of finite type morphism of
algebraic spaces over a scheme `S` and the relative diagonal
`pullback.diagonal f : X ⟶ X ×_Y X` is an open immersion, then `f` is
unramified. -/
@[stacks 05W1] #check
  (AlgebraicGeometry.AlgebraicSpace.Unramified.of_isOpenImmersion_diagonal :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [LocallyOfFiniteType f] [IsOpenImmersion (pullback.diagonal f)],
      Unramified f)

/- A morphism of algebraic spaces is unramified if and only if it is locally of
finite type and its relative diagonal is an open immersion. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Unramified.iff_locallyOfFiniteType_and_isOpenImmersion_diagonal :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      Unramified f ↔
        LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f))

end AlgebraicGeometry.AlgebraicSpace
