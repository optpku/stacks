/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Underlying
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.20.3

The cohomology presheaf of a derived module is formed using the total right derived
underlying-presheaf functor.  Its sheafification is the underlying additive sheaf of the
corresponding cohomology module sheaf.
-/

/- Lemma 21.20.3 (0BKV): sheafification of `U ↦ H^q(U, K)` is the underlying additive
sheaf of `𝓗^q(K)`. -/
@[stacks 0BKV]
#check @RingedSite.Hom.ModuleDerived.sheafification_cohomologyPresheaf_isomorphic_underlyingCohomologySheaf

#check @RingedSite.Hom.ModuleDerived.underlyingPresheafDerived
#check @RingedSite.Hom.ModuleDerived.cohomologyPresheaf
#check @RingedSite.Hom.ModuleDerived.cohomologyOverObject
#check @RingedSite.Hom.ModuleDerived.cohomologySheaf
#check @RingedSite.Hom.ModuleDerived.cohomologySheafMap
#check @RingedSite.Hom.ModuleDerived.underlyingCohomologySheaf
