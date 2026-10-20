/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat
import StacksCheckRecall

/-!
# Definition 18.31.1

The reusable owner is `RingedSite.Hom.IsFlat`; the commutative-presentation bridge identifies it
with flatness of the inverse-image structure map.
-/

@[expose] public section

/- Definition 18.31.1 (04JB): categorical flatness of a ringed-site morphism. -/
@[stacks 04JB "categorical owner"]
#check @RingedSite.Hom.IsFlat

/- Definition 18.31.1 (04JB): structure-map characterization in a commutative presentation. -/
@[stacks 04JB "structure-map criterion"]
#check @RingedSite.Hom.isFlat_iff_isFlatHom
