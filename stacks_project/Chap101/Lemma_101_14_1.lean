/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyInjective.Representable
import StacksCheckRecall

/-!
# Representable universally injective morphisms of algebraic stacks

A morphism of algebraic stacks representable by algebraic spaces is universally
injective in the sense of scheme-slice tests of algebraic spaces if and only if
every algebraic-stack base change induces an injective map on underlying point
spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.14.1: Let `f : X ⟶ Y` be a morphism of algebraic stacks which is
representable by algebraic spaces. Then `f` is universally injective as in
Properties of Stacks, Section 100.3 if and only if for every morphism of
algebraic stacks `Z ⟶ Y` the map `|Z ×_Y X| ⟶ |Z|` is injective. -/
@[stacks 0CI1]
#check (AlgebraicGeometry.Groupoids.Hom.has_universallyInjective_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y},
    relativelyRepresentableByAlgebraicSpaces f →
      (AlgebraicGeometry.Groupoids.Hom.has (@AlgebraicSpace.UniversallyInjective S) f ↔
        AlgebraicStack.UniversallyInjective f))
