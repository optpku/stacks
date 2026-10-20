/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.StrictlyPerfect.InternalHom
import StacksCheckRecall

@[expose] public section

/- Lemma 21.44.9 (08JH): internal Hom from a strictly perfect complex computes the derived
internal Hom on module sheaves over a ringed site. -/
@[stacks 08JH]
#check @RingedSite.CochainComplex.InternalHom.represents_of_strictlyPerfect

#check @RingedSite.CochainComplex.InternalHom.isKFlat_of_strictlyPerfect
