/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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
