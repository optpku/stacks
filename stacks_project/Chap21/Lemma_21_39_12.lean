/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Point
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/-! Lemma 21.39.12 (08RX), change of structure sheaf.

For a morphism of chaotic ring sheaves, the reusable comparison is owned by
`RingedSite.Hom.DerivedPoint.Chaotic.tensor.lowerShriek_obj_isomorphic`. Its statement retains the
cosimplicial pointlike hypothesis and invertibility of the induced map on the lower shriek of the
unit. The `Chaotic.Comm` namespace supplies the commutative-ring specialization separately.
-/

@[stacks 08RX "change of rings after derived lower shriek"]
#check @RingedSite.Hom.DerivedPoint.Chaotic.tensor.lowerShriek_obj_isomorphic

#check @RingedSite.Hom.DerivedPoint.Chaotic.Comm.lowerShriek_obj_isomorphic
