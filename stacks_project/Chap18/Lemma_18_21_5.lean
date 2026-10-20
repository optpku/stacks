/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Sheaf.Relocalization
import StacksCheckRecall

/-!
# Lemma 18.21.5

Compatibility facade identifying relocalization at a morphism of
sheafified representables with pullback between the corresponding slice
topoi.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology

/- Lemma 18.21.5 (04J5): under the representable-localization comparisons,
the inverse-image relocalization map is the canonical pullback map. -/
@[stacks 04J5 "inverse-image comparison"]
#check @RepresentableLocalization.relocalizationInverseImageOverPullback

@[stacks 04J5 "invertibility"]
#check @RepresentableLocalization.relocalizationInverseImageOverPullback_isIso

/- The corresponding structure-object comparison is the same slice
pullback isomorphism specialized to the underlying structure sheaf. -/
#check @RingedSite.Localization.AtSheaf.underlyingStructurePullbackIso
#check @RingedSite.Localization.AtSheaf.representableStructureMap
