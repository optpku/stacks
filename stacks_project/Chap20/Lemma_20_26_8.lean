/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.KFlat.Pullback

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape
open scoped RingedSpace.Hom

/- Lemma 20.26.8 (06YC): for a morphism of ringed spaces, pullback preserves K-flat complexes. -/
@[stacks 06YC "pullback preserves K-flat complexes"]
#check @AlgebraicGeometry.RingedSpace.CochainComplex.IsKFlat.pullback

#check @RingedSite.Hom.modulePullbackComplex.isKFlat_of_hasEnoughPoints

end
