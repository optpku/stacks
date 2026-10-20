/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Hom.LimitPreserving.FinitePresentation
import StacksCheckRecall

/-!
# Limit-preserving 1-morphisms versus locally of finite presentation

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is limit preserving if and only if it is
limit preserving on objects, if and only if it is locally of finite
presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/- Lemma 102.3.5: Let `p : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. If `p` is representable by algebraic spaces,
then the following are equivalent: `p` is limit preserving, `p` is limit
preserving on objects, and `p` is locally of finite presentation in the sense
of Algebraic Stacks, Definition 94.10.1. -/
@[stacks 0CMV] #check (AlgebraicGeometry.Groupoids.Hom.LimitPreserving.tfae :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (p : X ⟶ Y)
    (hp : relativelyRepresentableByAlgebraicSpaces p),
    List.TFAE [LimitPreserving p, LimitPreservingOnObjects p,
      LocallyOfFinitePresentation p])

/- A 1-morphism of categories fibred in groupoids that is representable by
algebraic spaces is limit preserving if and only if it is limit preserving on
objects. -/
#check (AlgebraicGeometry.Groupoids.Hom.LimitPreserving.iff_limitPreservingOnObjects :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p),
    LimitPreserving p ↔ LimitPreservingOnObjects p)

/- A 1-morphism of categories fibred in groupoids that is representable by
algebraic spaces is limit preserving if and only if it is locally of finite
presentation. -/
#check (AlgebraicGeometry.Groupoids.Hom.LimitPreserving.iff_locallyOfFinitePresentation :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p),
    LimitPreserving p ↔ LocallyOfFinitePresentation p)

/- A 1-morphism of categories fibred in groupoids that is representable by
algebraic spaces and limit preserving on objects is limit preserving. -/
#check (AlgebraicGeometry.Groupoids.Hom.LimitPreserving.of_limitPreservingOnObjects :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p)
    [LimitPreservingOnObjects p], LimitPreserving p)

/- A 1-morphism of categories fibred in groupoids that is locally of finite
presentation is limit preserving. -/
#check (AlgebraicGeometry.Groupoids.Hom.LimitPreserving.of_locallyOfFinitePresentation :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) [LocallyOfFinitePresentation p], LimitPreserving p)

end AlgebraicGeometry.Groupoids.Hom
