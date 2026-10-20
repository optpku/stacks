/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Truncation.LowerResolution.Injective.Derived
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

/-!
21.24.0.1 recalls the canonical map of an injective lower-truncation resolution.  The reusable
owner is `CochainComplex.LowerTruncation.Resolution`; no Chapter 13 wrapper is needed.
-/

@[stacks 070P] #check @CochainComplex.LowerTruncation.Resolution.intoLimit
#check @CochainComplex.LowerTruncation.Resolution.intoLimit_comp_π
