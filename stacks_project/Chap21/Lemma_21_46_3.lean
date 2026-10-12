/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension.FlatRepresentative
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.46.3

The bounded termwise-flat representative criterion is owned by the generic derived-category
predicate and its ringed-site Tor-amplitude bridge.
-/

/- Lemma 21.46.3 (08G1): a derived module sheaf has Tor-amplitude in `[a, b]` exactly when it
admits a termwise-flat cochain representative supported in `[a, b]`. -/
@[stacks 08G1]
#check @RingedSite.Hom.ModuleDerived.hasTorAmplitudeIn_iff_hasFlatRepresentativeIn

#check @RingedSite.Hom.ModuleDerived.hasFlatRepresentativeIn_iff
#check @RingedSite.Hom.ModuleDerived.HasTorAmplitudeIn.hasFlatRepresentativeIn
#check @RingedSite.Hom.ModuleDerived.HasFlatRepresentativeIn.hasTorAmplitudeIn
#check @CategoryTheory.DerivedCategory.flatRepresentativeIn

end
