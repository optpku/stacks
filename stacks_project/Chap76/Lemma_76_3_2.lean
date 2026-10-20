/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Radicial.UniversallyInjective
import StacksCheckRecall

/-!
# Radicial morphisms of algebraic spaces are universally injective

A radicial morphism of algebraic spaces over a scheme is universally injective:
field-valued points of the target lift in at most one way, so the morphism is
injective on field-valued points and hence universally injective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 76.3.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a radicial morphism of
algebraic spaces over `S`. Then `f` is universally injective. -/
@[stacks 0482]
#check (AlgebraicGeometry.AlgebraicSpace.Radicial.universallyInjective :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [AlgebraicGeometry.AlgebraicSpace.Radicial f] →
      AlgebraicGeometry.AlgebraicSpace.UniversallyInjective f)
