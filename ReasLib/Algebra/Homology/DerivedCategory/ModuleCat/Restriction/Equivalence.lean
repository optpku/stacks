/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Equivalence
public import ReasLib.CategoryTheory.Adjunction.RightIso

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat

/-- The derived equivalence induced by restriction of scalars along a ring equivalence. -/
noncomputable def derivedRestrictionEquivalenceOfRingEquiv {R S : Type u}
    [CommRing R] [CommRing S] (e : R ≃+* S) :
    DerivedCategory (ModuleCat S) ≌ DerivedCategory (ModuleCat R) :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).mapDerivedCategory

/-- Derived extension along a ring equivalence agrees with restriction along its inverse. -/
noncomputable def derivedExtensionIsoRestrictionOfRingEquiv {R S : Type u}
    [CommRing R] [CommRing S] (e : R ≃+* S) :
    derivedExtensionOfScalars e.toRingHom ≅ derivedRestrictionOfScalars e.symm :=
  (derivedExtensionRestrictionAdjunction e.toRingHom).leftAdjointUniq
    (derivedRestrictionEquivalenceOfRingEquiv e).symm.toAdjunction

/-- Derived coextension along a ring equivalence agrees with restriction along its inverse. -/
noncomputable def derivedCoextensionIsoRestrictionOfRingEquiv {R S : Type u}
    [CommRing R] [CommRing S] (e : R ≃+* S) :
    derivedCoextensionOfScalars e.toRingHom ≅ derivedRestrictionOfScalars e.symm :=
  (derivedRestrictionCoextensionAdjunction e.toRingHom).rightAdjointUniq
    (derivedRestrictionEquivalenceOfRingEquiv e).toAdjunction

end CategoryTheory.ModuleCat
