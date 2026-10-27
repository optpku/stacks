/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace
public import ReasLib.CategoryTheory.Subobject.Invariant

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open FiberedCategoryOver.Groupoids

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- An object property is invariant under a groupoid if its source and target
inverse images coincide. -/
def IsInvariantSubstack (G : GroupoidAlgebraicSpace B)
    (Q : ObjectProperty G.U.left.toGroupoids.total) : Prop :=
  Q.inverseImage (toFunctor (toGroupoids.map G.s.left)) =
    Q.inverseImage (toFunctor (toGroupoids.map G.t.left))

/-- Invariant locally closed subspaces are locally closed object properties
whose source and target inverse images coincide. -/
def InvariantLocallyClosedSubspaces (G : GroupoidAlgebraicSpace B) :=
  {Q : ObjectProperty G.U.left.toGroupoids.total //
    AlgebraicStack.Substack.IsLocallyClosed G.U.left.toGroupoids Q ∧
      IsInvariantSubstack G Q}

/-- Invariant closed subspaces are closed object properties whose source and
target inverse images coincide. -/
def InvariantClosedSubspaces (G : GroupoidAlgebraicSpace B) :=
  {Q : ObjectProperty G.U.left.toGroupoids.total //
    AlgebraicStack.Substack.IsClosed G.U.left.toGroupoids Q ∧ IsInvariantSubstack G Q}

/-- Invariant open subspaces are open object properties whose source and
target inverse images coincide. -/
def InvariantOpenSubspaces (G : GroupoidAlgebraicSpace B) :=
  {Q : ObjectProperty G.U.left.toGroupoids.total //
    AlgebraicStack.Substack.IsOpen G.U.left.toGroupoids Q ∧ IsInvariantSubstack G Q}

/-- Invariant locally closed object properties are exactly the essential images
of locally closed subspaces with pullback-invariant inclusion. -/
theorem invariantLocallyClosedSubspaces_iff (G : GroupoidAlgebraicSpace B)
    (Q : ObjectProperty G.U.left.toGroupoids.total) :
    (AlgebraicStack.Substack.IsLocallyClosed G.U.left.toGroupoids Q ∧
      IsInvariantSubstack G Q) ↔
      ∃ W : LocallyClosedSubspace G.U.left,
        (toFunctor (toGroupoids.map W.ι)).essImage = Q ∧
          Morphism.IsPullbackInvariant G.s.left G.t.left W.ι := sorry

/-- Invariant closed object properties are exactly the essential images of
closed subspaces with pullback-invariant inclusion. -/
theorem invariantClosedSubspaces_iff (G : GroupoidAlgebraicSpace B)
    (Q : ObjectProperty G.U.left.toGroupoids.total) :
    (AlgebraicStack.Substack.IsClosed G.U.left.toGroupoids Q ∧
      IsInvariantSubstack G Q) ↔
      ∃ W : ClosedSubspace G.U.left,
        (toFunctor (toGroupoids.map W.ι)).essImage = Q ∧
          Morphism.IsPullbackInvariant G.s.left G.t.left W.ι := sorry

/-- Invariant open object properties are exactly the essential images of open
subspaces with forward-invariant inclusion. -/
theorem invariantOpenSubspaces_iff (G : GroupoidAlgebraicSpace B)
    (Q : ObjectProperty G.U.left.toGroupoids.total) :
    (AlgebraicStack.Substack.IsOpen G.U.left.toGroupoids Q ∧
      IsInvariantSubstack G Q) ↔
      ∃ W : OpenSubspace G.U.left,
        (toFunctor (toGroupoids.map W.ι)).essImage = Q ∧
          Morphism.IsForwardInvariant G.s.left G.t.left W.ι := sorry

/-- Forget invariance of a locally closed subspace, retaining its object property. -/
def InvariantLocallyClosedSubspaces.toSubstack {G : GroupoidAlgebraicSpace B}
    (Q : InvariantLocallyClosedSubspaces G) :
    AlgebraicStack.Substack.LocallyClosed G.U.left.toGroupoids :=
  ⟨Q.val, Q.property.1⟩

/-- Forget invariance of a closed subspace, retaining its object property. -/
def InvariantClosedSubspaces.toSubstack {G : GroupoidAlgebraicSpace B}
    (Q : InvariantClosedSubspaces G) :
    AlgebraicStack.Substack.Closed G.U.left.toGroupoids :=
  ⟨Q.val, Q.property.1⟩

/-- Forget invariance of an open subspace, retaining its object property. -/
def InvariantOpenSubspaces.toSubstack {G : GroupoidAlgebraicSpace B}
    (Q : InvariantOpenSubspaces G) :
    AlgebraicStack.Substack.Open G.U.left.toGroupoids :=
  ⟨Q.val, Q.property.1⟩

end AlgebraicGeometry.GroupoidAlgebraicSpace
