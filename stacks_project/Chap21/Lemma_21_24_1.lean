module

public import ReasLib.Algebra.Homology.CochainComplex.Truncation.LowerResolution.Injective.Derived
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Limit.Truncation
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.24.1

The lower-truncation resolution and its inverse-limit comparison are reusable ReasLib owners; the
chapter entry only recalls their canonical construction and criterion.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite.Hom.ModuleDerived.Limit
open scoped RingedSiteCohomology

#check @CochainComplex.LowerTruncation.Resolution.fromSource
#check @CochainComplex.LowerTruncation.Resolution.intoLimit
#check @CochainComplex.LowerTruncation.Resolution.Comparison.exists_of_comp_π

/- Lemma 21.24.1 (070Q): a stagewise compatible map into the inverse limit of an injective
lower-truncation resolution is a quasi-isomorphism under uniform basiswise negative vanishing. -/
@[stacks 070Q]
#check @Resolution.quasiIso_of_comp_π_uniformNegative

#check @Resolution.quasiIso_intoLimit_of_uniformNegative
