/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective.Characterization
import StacksCheckRecall

/-!
# Characterizations of universally injective morphisms of algebraic spaces

A morphism of algebraic spaces is universally injective iff it is injective on
field-valued points iff its relative diagonal is surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory.Limits

universe u

/- Lemma 67.19.2: injectivity on field-valued points, universal injectivity, and
surjectivity of the relative diagonal are equivalent. -/
@[stacks 040X] #check
  (AlgebraicGeometry.AlgebraicSpace.UniversallyInjective.tfae :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      List.TFAE [injectiveOnFieldPoints f, UniversallyInjective f,
        Surjective (pullback.diagonal f)])
