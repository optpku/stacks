/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.InGroupoids.Pullback
public import ReasLib.CategoryTheory.Fibered.InheritedTopology
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Projection
public import ReasLib.CategoryTheory.Sites.Precoverage.Continuous
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Over.MorphismOfSites
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Over
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inherited topology of a category fibred in groupoids

For a groupoid-fibred projection, the canonical precoverage of the generated inherited topology
and the corresponding slice sites admit stronger comparison results.  Continuity and
cocontinuity of an arbitrary fibred projection are owned by `InheritedTopology.Projection`.

## Main declarations

* `Functor.inheritedTopology.isPrecoverageContinuous` -- the
  precoverage-level continuity datum of the projection.
* `Functor.inheritedTopology.overPost.isDenseSubsite` -- the slice
  equivalence is a dense subsite for the inherited and base slice topologies.

The general direct-image statement is
`Functor.inheritedTopology.coverPreserving`; inverse-image transport is the standard
`Functor.cover_lift` readout from cocontinuity.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

namespace Functor

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]

namespace inheritedTopology

/-- Lemma 8.10.4 (tag 0CN0): for a category fibred in groupoids, its projection preserves
covering families and the pullbacks occurring in them for the inherited and base precoverages.
The pullback-preservation input is the shared `InGroupoids.Pullback.preservesWalkingCospan`
instance. -/
@[stacks 0CN0]
instance isPrecoverageContinuous
    (p : S ⥤ C) (J : GrothendieckTopology C) [Functor.IsFibered.InGroupoids p] :
    Functor.Precoverage.IsContinuous p (p.inheritedTopology J).toPrecoverage J.toPrecoverage := sorry

namespace overPost

/-- The slice functor induced by a groupoid-fibred projection is a morphism of sites from the
inherited slice topology to the ordinary slice topology.  This packages the slice equivalence,
continuity, and representable flatness at the correct site level. -/
@[stacks 0CN0]
instance isMorphismOfSites
    (p : S ⥤ C) (J : GrothendieckTopology C) [Functor.IsFibered.InGroupoids p]
    (x : S) :
    IsMorphismOfSites ((p.inheritedTopology J).over x) (J.over (p.obj x))
      (Over.post (X := x) p) := sorry

/-- The slice equivalence induced by a groupoid-fibred projection detects covering sieves.

Together with `overPost.isEquivalence`, this is the cover-reflection half of the equivalence of
the inherited slice site over `x` with the base slice site over `p.obj x`. -/
@[stacks 0CN0 "slice covering reflection"]
theorem covering_iff
    (p : S ⥤ C) (J : GrothendieckTopology C) [Functor.IsFibered.InGroupoids p]
    (x : S) {y : Over x} (R : Sieve y) :
    R ∈ (p.inheritedTopology J).over x y ↔
      R.functorPushforward (Over.post (X := x) p) ∈
        (J.over (p.obj x)) ((Over.post (X := x) p).obj y) := sorry

/-- Lemma 8.10.4 (tag 0CN0): the slice equivalence induced by a groupoid-fibred projection
exhibits the inherited slice site as a dense subsite of the corresponding base slice site. -/
@[stacks 0CN0]
instance isDenseSubsite
    (p : S ⥤ C) (J : GrothendieckTopology C) [Functor.IsFibered.InGroupoids p]
    (x : S) :
    (Over.post (X := x) p).IsDenseSubsite
      ((p.inheritedTopology J).over x) (J.over (p.obj x)) := sorry

end overPost

end inheritedTopology

end Functor

end CategoryTheory
