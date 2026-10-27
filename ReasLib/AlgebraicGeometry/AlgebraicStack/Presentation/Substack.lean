/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Presentation.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.InvariantSubspace

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Presentation

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- Pullback of an object property along the atlas of a presentation. -/
def pullbackSubstack (P : Presentation X) (Q : ObjectProperty X.total) :
    ObjectProperty P.groupoid.U.left.toGroupoids.total :=
  Q.inverseImage (toFunctor P.atlas)

/-- An object belongs to the pulled-back substack exactly when its atlas image
belongs to the original substack. -/
theorem pullbackSubstack_apply (P : Presentation X) (Q : ObjectProperty X.total)
    (y : P.groupoid.U.left.toGroupoids.total) :
    P.pullbackSubstack Q y ↔ Q ((toFunctor P.atlas).obj y) := sorry

/-- Atlas pullback of a locally closed substack is locally closed and invariant
under the presenting groupoid. -/
theorem pullbackLocallyClosed_spec (P : Presentation X) (Q : Substack.LocallyClosed X) :
    Substack.IsLocallyClosed P.groupoid.U.left.toGroupoids (P.pullbackSubstack Q.val) ∧
      P.groupoid.IsInvariantSubstack (P.pullbackSubstack Q.val) := sorry

/-- Atlas pullback of a closed substack is closed and invariant under the
presenting groupoid. -/
theorem pullbackClosed_spec (P : Presentation X) (Q : Substack.Closed X) :
    Substack.IsClosed P.groupoid.U.left.toGroupoids (P.pullbackSubstack Q.val) ∧
      P.groupoid.IsInvariantSubstack (P.pullbackSubstack Q.val) := sorry

/-- Atlas pullback of an open substack is open and invariant under the
presenting groupoid. -/
theorem pullbackOpen_spec (P : Presentation X) (Q : Substack.Open X) :
    Substack.IsOpen P.groupoid.U.left.toGroupoids (P.pullbackSubstack Q.val) ∧
      P.groupoid.IsInvariantSubstack (P.pullbackSubstack Q.val) := sorry

/-- Atlas inverse image sends locally closed substacks to invariant locally
closed subspaces of the object space. -/
def pullbackLocallyClosed (P : Presentation X) (Q : Substack.LocallyClosed X) :
    P.groupoid.InvariantLocallyClosedSubspaces :=
  ⟨P.pullbackSubstack Q.val, P.pullbackLocallyClosed_spec Q⟩

/-- Atlas inverse image sends closed substacks to invariant closed subspaces
of the object space. -/
def pullbackClosed (P : Presentation X) (Q : Substack.Closed X) :
    P.groupoid.InvariantClosedSubspaces :=
  ⟨P.pullbackSubstack Q.val, P.pullbackClosed_spec Q⟩

/-- Atlas inverse image sends open substacks to invariant open subspaces of
the object space. -/
def pullbackOpen (P : Presentation X) (Q : Substack.Open X) :
    P.groupoid.InvariantOpenSubspaces :=
  ⟨P.pullbackSubstack Q.val, P.pullbackOpen_spec Q⟩

/-- Atlas pullback gives a bijection between locally closed substacks and
invariant locally closed subspaces of the presenting object space. -/
theorem pullbackLocallyClosed_bijective (P : Presentation X) :
    Function.Bijective P.pullbackLocallyClosed := sorry

/-- Atlas pullback gives a bijection between closed substacks and invariant
closed subspaces of the presenting object space. -/
theorem pullbackClosed_bijective (P : Presentation X) :
    Function.Bijective P.pullbackClosed := sorry

/-- Atlas pullback gives a bijection between open substacks and invariant
open subspaces of the presenting object space. -/
theorem pullbackOpen_bijective (P : Presentation X) :
    Function.Bijective P.pullbackOpen := sorry

/-- Factorization through a locally closed substack can be checked after
pulling back to the atlas of a presentation. -/
theorem factorsThrough_iff {Y : GroupoidsOver S} [AlgebraicStack Y]
    (P : Presentation X) (Q : Substack.LocallyClosed X) (f : Y ⟶ X) :
    Substack.FactorsThrough f Q.val ↔
      Substack.FactorsThrough (P.objectProjection f) (P.pullbackLocallyClosed Q).val := sorry

/-- Factorization through a closed substack can be checked after pulling back
to the atlas of a presentation. -/
theorem closed_factorsThrough_iff {Y : GroupoidsOver S} [AlgebraicStack Y]
    (P : Presentation X) (Q : Substack.Closed X) (f : Y ⟶ X) :
    Substack.FactorsThrough f Q.val ↔
      Substack.FactorsThrough (P.objectProjection f) (P.pullbackClosed Q).val := sorry

/-- Factorization through an open substack can be checked after pulling back
to the atlas of a presentation. -/
theorem open_factorsThrough_iff {Y : GroupoidsOver S} [AlgebraicStack Y]
    (P : Presentation X) (Q : Substack.Open X) (f : Y ⟶ X) :
    Substack.FactorsThrough f Q.val ↔
      Substack.FactorsThrough (P.objectProjection f) (P.pullbackOpen Q).val := sorry

end AlgebraicGeometry.AlgebraicStack.Presentation
