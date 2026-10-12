/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Topos.Point.FiberToTypes

/-!
# Canonical type-site presentation of a point

The powerset site in the textbook proof is a chosen presentation of the
terminal topos.  The formal API uses the canonical site `Type` and its
equivalence `typeEquiv` with the terminal topos instead.  This avoids making
an arbitrary universe-sized presentation part of the public interface.

The reusable construction lives in
`GrothendieckTopology.Point.FiberToTypes`; its source label `04EL` is attached
to `Point.FiberToTypes.typePushforwardIso`.
-/

@[expose] public section

open CategoryTheory

universe w

namespace CategoryTheory

/- Lemma 7.32.8 (1): `typeEquiv` is the canonical `Sh(pt) ≌ Sh(Type)`
presentation used in place of the source's chosen powerset site. -/
@[stacks 04EL "(1)"] #check @typeEquiv
#check @GrothendieckTopology.Point.TypesPoint.sheafFiberIso
#check @GrothendieckTopology.Point.TypesPoint.skyscraperSheafFunctorIso

/- Lemma 7.32.8 (2): the fiber of a site point induces a morphism from the canonical type site.
The continuity bridge is an implementation detail of this construction. -/
#check @GrothendieckTopology.Point.FiberToTypes.coverPreserving
#check @GrothendieckTopology.Point.FiberToTypes.compatiblePreserving
#check @GrothendieckTopology.Point.FiberToTypes.isContinuous
@[stacks 04EL "(2)"] #check @GrothendieckTopology.Point.FiberToTypes.morphism

/- Lemma 7.32.8 (3): composing the canonical type-site presentation with the fiber-induced
morphism recovers `p.toToposPoint`. -/
@[stacks 04EL "(3)"] #check @GrothendieckTopology.Point.FiberToTypes.typePushforwardIso
#check @GrothendieckTopology.Point.FiberToTypes.typeInverseImageIso

end CategoryTheory
