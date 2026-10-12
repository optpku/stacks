/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact
public import ReasLib.CategoryTheory.Filtration.Derived.Injective
public import ReasLib.CategoryTheory.Filtration.Derived.BoundedFunctor.RightDerived

/-!
# Short names for finite filtered derived comparisons

The source-faithful owners in `FilteredObject.FiniteDerived.Plus` predate the neutral
`FilteredComplex.RightDerived.Finite` vocabulary and have long namespaces.  This file is an
export-only compatibility layer: it introduces no second construction and preserves every
assumption and comparison theorem of the original owners.
-/

@[expose] public section

namespace CategoryTheory.FilteredComplex.RightDerived.Finite

namespace LeftExact

export CategoryTheory.FilteredObject.FiniteDerived.Plus.LeftExact
  (homotopy homotopy_obj_obj homotopy_map_hom Has hasOfEnoughInjectives functor unit
    isRightDerivedFunctor unit_eq_totalRightDerivedUnit unit_fac unit_fac_app)

end LeftExact

namespace Injective

export CategoryTheory.FilteredObject.FiniteDerived.Plus.FilteredInjective
  (functor localizer IsEquivalence isEquivalence equivalenceOf
    equivalenceOfEnoughInjectives equivalenceOfEnoughInjectives_functor
    equivalenceOfEnoughInjectives_inverse)

namespace RightDerived

export CategoryTheory.FilteredObject.FiniteDerived.Plus.FilteredInjective.RightDerived
  (iso isoOfEnoughInjectives fac fac_assoc fac_app inv_fac inv_fac_assoc inv_fac_app)

namespace isoOfEnoughInjectives

export CategoryTheory.FilteredObject.FiniteDerived.Plus.FilteredInjective.RightDerived.isoOfEnoughInjectives
  (fac fac_assoc fac_app inv_fac inv_fac_assoc inv_fac_app)

end isoOfEnoughInjectives

end RightDerived
end Injective

namespace Graded

export CategoryTheory.FilteredObject.FiniteDerived.Plus.GradedPiece.RightDerived
  (iso canonicalIso fac fac_assoc fac_app inv_fac inv_fac_assoc inv_fac_app)

namespace canonicalIso

export CategoryTheory.FilteredObject.FiniteDerived.Plus.GradedPiece.RightDerived.canonicalIso
  (fac fac_assoc fac_app inv_fac inv_fac_assoc inv_fac_app)

end canonicalIso

end Graded

namespace Forget

export CategoryTheory.FilteredObject.FiniteDerived.Plus.Forget.RightDerived
  (iso canonicalIso fac fac_assoc fac_app inv_fac inv_fac_assoc inv_fac_app)

namespace canonicalIso

export CategoryTheory.FilteredObject.FiniteDerived.Plus.Forget.RightDerived.canonicalIso
  (fac fac_assoc fac_app inv_fac inv_fac_assoc inv_fac_app)

end canonicalIso

end Forget

end CategoryTheory.FilteredComplex.RightDerived.Finite
