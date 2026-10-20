/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.StrictHenselian.EtaleZeroLocus
import StacksCheckRecall

@[expose] public section

/-!
# Etale Points over Strictly Henselian Local Rings

The source-facing coordinate presentation and its ind-etale lifting mechanism
are both recalled from ReasLib.

@stack 04GX
-/

@[stacks 04GX "coordinate zero-locus bijection"]
#check @StrictHenselianLocalRing.bijOn_zeroLocus_of_etale

@[stacks 04GX "ind-etale lifting core"]
#check @RingHom.IndEtale.existsUnique_lift
