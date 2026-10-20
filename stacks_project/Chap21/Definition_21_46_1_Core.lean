/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.Recall
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension
import StacksCheckRecall

/-!
# Definition 21.46.1 core

Definition 21.46.1 is recalled directly from
`ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension`.  Its canonical owners
are `RingedSite.Hom.ModuleDerived` for derived objects and `RingedSite.ModuleCat` for module
sheaves.
-/

@[expose] public section

/- Definition 21.46.1 (1), (2), and (4) are supplied by the canonical derived-object and
module-sheaf owners below.  This historical core path remains a tagged recall surface; the
primary source-facing entry is `Definition_21_46_1.lean`. -/
@[stacks 08FZ "(1), derived-object Tor-amplitude"]
#check @RingedSite.Hom.ModuleDerived.HasTorAmplitudeIn

@[stacks 08FZ "(1), lower Tor-amplitude view"]
#check @RingedSite.Hom.ModuleDerived.HasTorAmplitudeGE

@[stacks 08FZ "(2), derived-object finite Tor dimension"]
#check @RingedSite.Hom.ModuleDerived.HasFiniteTorDimension

@[stacks 08FZ "(4), module-sheaf Tor dimension"]
#check @RingedSite.ModuleCat.HasTorDimensionLE
