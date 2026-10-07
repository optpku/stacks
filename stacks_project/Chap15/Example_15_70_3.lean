module

public import ReasLib.Algebra.Homology.DerivedCategory.TruncationSplitting.Dedekind
import StacksCheckRecall

@[expose] public section

/-!
# Example 15.70.3: bounded derived objects over a Dedekind domain

The reusable content is owned by the ring-level global-dimension API and the generic
shifted-cohomology splitting API. This source file records the exact Dedekind-domain
specialization without retaining chapter-local quotient or Ext infrastructure.

@stack 0EX0
-/

/- Example 15.70.3, tag `0EX0`: every bounded derived object of modules over a Dedekind domain is
isomorphic to the finite biproduct of its shifted cohomology objects over some interval. -/
@[stacks 0EX0]
#check @DerivedCategory.ShiftedCohomology.Split.ofDedekindDomain

/- The ring-level owner is the canonical uniform projective-dimension bound. -/
#check @IsDedekindDomain.globalDimensionLEOne

/- Its canonical instance consequence removes proof-local injective-dimension instances. -/
#check @instHasInjectiveDimensionLE

/- The source's module statement is exposed in the numerical dimension vocabulary. -/
#check @IsDedekindDomain.injectiveDimension_le_one

/- The Ext view is stated in every degree at least two, not only in degree two. -/
#check @IsDedekindDomain.ext_subsingleton
