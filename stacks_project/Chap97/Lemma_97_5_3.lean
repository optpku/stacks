/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreservingOnObjects.FinitePresentation
import StacksCheckRecall

/-!
# Limit preserving on objects versus locally of finite presentation

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is limit preserving on objects if and only if
it is locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

open AlgebraicGeometry.Groupoids.Hom

/- Lemma 97.5.3: Let `p : X ⟶ Y` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. If `p` is representable by algebraic spaces,
then `p` is limit preserving on objects if and only if `p` is locally of finite
presentation in the sense of Algebraic Stacks, Definition 94.10.1. -/
@[stacks 06CX] #check
  (AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects.iff_locallyOfFinitePresentation :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p),
      LimitPreservingOnObjects p ↔ LocallyOfFinitePresentation p)

#check
  (AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects.of_locallyOfFinitePresentation :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      (p : X ⟶ Y) [LocallyOfFinitePresentation p], LimitPreservingOnObjects p)

#check (AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects.iff_has :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p),
    LimitPreservingOnObjects p ↔ has (@AlgebraicSpace.LocallyOfFinitePresentation S) p)

#check
  (AlgebraicGeometry.Groupoids.Hom.LocallyOfFinitePresentation.of_limitPreservingOnObjects :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p)
      [LimitPreservingOnObjects p], LocallyOfFinitePresentation p)
