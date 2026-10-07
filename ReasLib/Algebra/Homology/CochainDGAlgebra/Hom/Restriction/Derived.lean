module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction.Derived.Adjunction
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction.Derived.Basic

/-!
# Derived Restriction of Scalars

Compatibility import for the canonical localization lift of restriction of scalars and its
extension-restriction adjunction.  Downstream files should import `Derived.Basic` when they only
need the restriction functor and its factorization.
-/

@[expose] public section
