/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Topos.Point.FromSite
public import ReasLib.CategoryTheory.Sites.Topos.Point.FromTopos
public import ReasLib.CategoryTheory.Sites.Types.Point

/-!
# Canonical point comparisons

This chapter-facing module is a recall block.  The reusable constructions are
owned by the `ReasLib` leaves imported above; in particular, the source label
`00YA` is attached to `MorphismOfTopoiIn.ToSitePoint.sheafFiberIso`.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory

/- Lemma 7.32.7 (1): a point of a site canonically induces a point of its sheaf topos. -/
@[stacks 00YA "(1)"] #check @GrothendieckTopology.Point.toToposPoint
#check @GrothendieckTopology.Point.toToposPoint_pointInverseImageIso
#check @GrothendieckTopology.Point.toToposPoint_pointPushforwardIso

/- Lemma 7.32.7 (2): evaluating a topos point on sheafified representables defines a site point,
whose sheaf fiber recovers the original inverse-image functor. -/
#check @MorphismOfTopoiIn.sitePointFiber
#check @MorphismOfTopoiIn.toSitePoint
#check @MorphismOfTopoiIn.ToSitePoint.sectionEquiv
#check @MorphismOfTopoiIn.ToSitePoint.typePushforwardIso
@[stacks 00YA "(2)"] #check @MorphismOfTopoiIn.ToSitePoint.sheafFiberIso

/- The strict canonical point of the jointly-surjective site on `Type` and its comparison API. -/
#check @GrothendieckTopology.Point.typesPoint
#check @GrothendieckTopology.Point.TypesPoint.sheafFiberIso
#check @GrothendieckTopology.Point.TypesPoint.skyscraperSheafFunctorIso

end CategoryTheory
