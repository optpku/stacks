/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Hom.Factorization

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Substack

variable {S : Scheme.{u}}

/-- Locally closed substacks are replete object properties with locally closed inclusion. -/
def LocallyClosed (X : GroupoidsOver S) :=
  {Q : ObjectProperty X.total // IsLocallyClosed X Q}

/-- Closed substacks are replete object properties with closed inclusion. -/
def Closed (X : GroupoidsOver S) :=
  {Q : ObjectProperty X.total // IsClosed X Q}

/-- Open substacks are replete object properties with open inclusion. -/
def Open (X : GroupoidsOver S) :=
  {Q : ObjectProperty X.total // IsOpen X Q}

/-- A morphism factors through an object property when all its image objects satisfy it. -/
def FactorsThrough {X Y : GroupoidsOver S} (f : Y ⟶ X)
    (Q : ObjectProperty X.total) : Prop :=
  ∀ y, Q ((toFunctor f).obj y)

/-- Objectwise membership in a replete full subcategory is equivalent to
bicategorical factorization through its literal inclusion. -/
theorem factorsThrough_iff {X Y : GroupoidsOver S} (f : Y ⟶ X)
    (Q : ObjectProperty X.total)
    (h : Functor.IsFibered.InGroupoids (Q.ι ⋙ X.p))
    (hQ : Q.IsClosedUnderIsomorphisms) :
    FactorsThrough f Q ↔
      Groupoids.Hom.FactorsThrough f (inclusion X Q h) := sorry

end AlgebraicGeometry.AlgebraicStack.Substack
