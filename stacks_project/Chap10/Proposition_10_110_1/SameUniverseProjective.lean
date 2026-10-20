/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution.Syzygy.ProjectiveResolution
public import ReasLib.RingTheory.CohenMacaulay.Maximal.RegularLocalRing
public import ReasLib.RingTheory.Depth.CohenMacaulay.Syzygy
public import ReasLib.RingTheory.RegularLocalRing.ProjectiveDimension
import StacksCheckRecall

/-!
# Same-universe projective-dimension bridges

The reusable steps formerly proved in this helper now live in ReasLib.  Proposition 10.110.1
uses the final projective-dimension theorem directly.

@stack 00O7
-/

@[expose] public section

@[stacks 00O7 "maximal Cohen--Macaulay syzygy"]
#check @ChainComplex.Syzygy.maximalCohenMacaulay_of_finiteFree

@[stacks 00O7 "maximal Cohen--Macaulay modules over regular local rings are free"]
#check @Module.MaximalCohenMacaulay.free_of_isRegularLocalRing

@[stacks 00O7 "free-resolution syzygy comparison"]
#check @ChainComplex.IsFreeResolution.syzygyIso

@[stacks 00O7 "canonical projective-dimension bound"]
#check @IsRegularLocalRing.hasProjectiveDimensionLE_of_moduleDepth
