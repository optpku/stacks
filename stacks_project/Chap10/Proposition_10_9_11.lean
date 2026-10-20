/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Iterated
import StacksCheckRecall

/-!
# Proposition 10.9.11

@stack 02C7

Successive localization is represented by a concrete comparison map.  The equivalence constructor
takes an explicit bijectivity certificate, so its data remains independent of unfinished proofs.
-/

@[expose] public section

@[stacks 02C7 "iterated localization comparison"]
#check @LocalizedModule.iteratedToSup

@[stacks 02C7 "iterated localization equivalence from a certificate"]
#check @LocalizedModule.iteratedToSupEquiv

@[stacks 02C7 "iterated localization comparison on the source"]
#check @LocalizedModule.iteratedToSup_comp

@[stacks 02C7 "iterated localization comparison is bijective"]
#check @LocalizedModule.iteratedToSup_bijective
