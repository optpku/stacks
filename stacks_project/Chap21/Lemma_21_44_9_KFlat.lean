/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.StrictlyPerfect.InternalHom
import StacksCheckRecall

@[expose] public section

/- K-flat companion to Lemma 21.44.9: internal Hom into a K-flat complex remains K-flat when
its source is strictly perfect. -/
#check @RingedSite.CochainComplex.InternalHom.isKFlat_of_strictlyPerfect
