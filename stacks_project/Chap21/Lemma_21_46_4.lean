/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension.FlatRepresentative.Pullback
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.46.4

The canonical lower-bounded flat-representative predicate records the support, K-flatness, and
termwise flatness needed both to characterize lower Tor-amplitude and to apply pullback-stability
results without choosing a second representative.
-/

/- Lemma 21.46.4 (0F1M): a derived module sheaf has lower Tor-amplitude at least `a` exactly when
it admits a K-flat, termwise-flat cochain representative supported in degrees `≥ a`. -/
@[stacks 0F1M]
#check @RingedSite.Hom.ModuleDerived.hasTorAmplitudeGE_iff_hasFlatRepresentativeGE

#check @RingedSite.Hom.ModuleDerived.hasFlatRepresentativeGE_iff
#check @RingedSite.Hom.ModuleDerived.HasTorAmplitudeGE.hasFlatRepresentativeGE
#check @RingedSite.Hom.ModuleDerived.HasFlatRepresentativeGE.hasTorAmplitudeGE
#check
  @RingedSite.Hom.ModuleDerived.HasTorAmplitudeGE.exists_pullbackStableFlatRepresentative
#check @RingedSite.Hom.modulePullbackComplex.isKFlat_and_isTermwiseFlat
#check @CategoryTheory.DerivedCategory.flatRepresentativeGE
#check @CategoryTheory.DerivedCategory.HasFlatRepresentativeGE.ofIso

end
