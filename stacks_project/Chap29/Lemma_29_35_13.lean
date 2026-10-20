/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Diagonal
import StacksCheckRecall

/-!
# Lemma 29.35.13

The diagonal criterion for unramified and G-unramified morphisms.

@stack 02GE
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

/- Lemma 29.35.13 (1): an unramified morphism has open diagonal. -/
@[stacks 02GE] #check
  (AlgebraicGeometry.isOpenImmersion_diagonal_of_unramified :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Unramified f],
      IsOpenImmersion (pullback.diagonal f))

/- Lemma 29.35.13 (2): a locally finite type morphism with open diagonal is unramified. -/
@[stacks 02GE] #check
  (AlgebraicGeometry.unramified_of_locallyOfFiniteType_of_isOpenImmersion_diagonal :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      [IsOpenImmersion (pullback.diagonal f)], Unramified f)

/- Lemma 29.35.13 (3): a locally finite presentation morphism with open diagonal is
G-unramified. -/
@[stacks 02GE] #check
  (AlgebraicGeometry.gUnramified_of_locallyOfFinitePresentation_of_isOpenImmersion_diagonal :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
      [IsOpenImmersion (pullback.diagonal f)], GUnramified f)

end AlgebraicGeometry
