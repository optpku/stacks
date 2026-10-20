/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Depth.Surjective
public import ReasLib.RingTheory.Depth.Equiv
public import ReasLib.RingTheory.RegularLocalRing.ProjectiveDimension
public import ReasLib.RingTheory.RegularLocalRing.ULift

@[expose] public section

/-!
The source proposition is universe-polymorphic in its canonical ReasLib owner. The former local
`ULift` proof route duplicated dimension, depth, and finite-resolution transport without any
consumer, so this support module now recalls those owners directly.
-/

#check @ringKrullDim_eq_of_ringEquiv
#check @LinearEquiv.moduleDepth_eq
#check @moduleDepth_eq_of_surjective
#check @ULift.instIsRegularLocalRing
#check @IsRegularLocalRing.finiteFreeResolutionLengthLE_of_moduleDepth
