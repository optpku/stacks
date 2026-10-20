/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.InverseImage
import StacksCheckRecall

@[expose] public section

open SheafOfModules.RingedSite

/- Lemma 18.35.3 (08TZ): inverse image preserves the naive cotangent complex on a ringed site. -/
@[stacks 08TZ]
#check @NaiveCotangent.InverseImage.Comparison.map_isIso

#check @NaiveCotangent.InverseImage.source
#check @NaiveCotangent.InverseImage.target
#check @NaiveCotangent.Presentation.InverseImage.comparison
#check @NaiveCotangent.Presentation.InverseImage.adjoint_generator
#check @NaiveCotangent.InverseImage.Conormal.app_toCotangent
#check @NaiveCotangent.InverseImage.Comparison.map
#check @NaiveCotangent.InverseImage.Comparison.map_f_negOne
#check @NaiveCotangent.InverseImage.Comparison.map_f_zero
#check @InverseImage.ringSheafPullbackIso
#check @NaiveCotangent.InverseImage.UnderlyingRing.mapOfIso
#check @NaiveCotangent.InverseImage.UnderlyingRing.mapOfIso_isIso
#check @NaiveCotangent.InverseImage.UnderlyingRing.map
#check @NaiveCotangent.InverseImage.UnderlyingRing.map_isIso
#check @InverseImage.pullbackPreservesZeroMorphisms
