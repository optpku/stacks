/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.LocallyFree.Reduced
import StacksCheckRecall

@[expose] public section

/-!
# Finite projective modules

Lemma 10.78.3 is owned by the reduced-ring fiber-rank criterion in
`Module.projective_iff_isLocallyConstant_fiberRank`; its `Module.fiberRank`
notation is the canonical form of the residue-field tensor fiber.

@stack 0FWG
-/

/- Lemma 10.78.3: over a reduced ring, finite projectivity is equivalent to
local constancy of the residue-field fiber rank. -/
@[stacks 0FWG]
#check @Module.projective_iff_isLocallyConstant_fiberRank
