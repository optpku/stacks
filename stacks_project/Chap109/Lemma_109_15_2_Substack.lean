/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.LocalCompleteIntersection.IsolatedSingularities
public import stacks_project.Chap108.Lemma_108_4_5_OpenImmersion

/-!
# The object property of lci families of curves with isolated singularities

`𝒞urves^{lci+}` is the full subcategory of families of curves that are local
complete intersections and have isolated singularities. Membership is the
source-facing packaging of a classifying morphism factoring through that open
substack.
-/

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.lciPlus :
  ∀ (S : Scheme.{u}), ObjectProperty (Obj S))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.lciPlus_iff :
  ∀ {S : Scheme.{u}} (P : Obj S),
    lciPlus S P ↔
      AlgebraicSpace.IsLocalCompleteIntersection (hom P) ∧
        IsolatedSingularities (hom P))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsClosedUnderIsomorphisms_lciPlus :
  ∀ (S : Scheme.{u}), (lciPlus S).IsClosedUnderIsomorphisms)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.lciPlus_isLocalCompleteIntersection :
  ∀ {S : Scheme.{u}} {P : Obj S},
    lciPlus S P → AlgebraicSpace.IsLocalCompleteIntersection (hom P))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.lciPlus_isolatedSingularities :
  ∀ {S : Scheme.{u}} {P : Obj S},
    lciPlus S P → IsolatedSingularities (hom P))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsFiberedInGroupoids_lciPlus :
  ∀ (S : Scheme.{u}),
    Functor.IsFibered.InGroupoids ((lciPlus S).ι ⋙ p S))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instOpenImmersion_inclusionOf_lciPlus :
  ∀ (S : Scheme.{u}), CohStack.OpenImmersion (inclusionOf (lciPlus S)))

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
