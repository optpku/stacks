/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.Functor.Derived.Exact.Cochain

@[expose] public section

/-!
# Derived extension-restriction adjunction for modules

@stack 064M

For an explicit homomorphism of commutative rings, this file packages restriction of scalars on
derived categories and the canonical adjunction with derived extension of scalars.  The
comparison maps are owned at the cochain-complex level, so downstream constructions can use the
adjunction without introducing algebra structures or rebuilding local derived-functor instances.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe u

namespace CategoryTheory.ModuleCat

section

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The cochain-level counit exhibiting derived extension of scalars as a left-derived
functor. -/
@[stacks 064M "cochain counit for derived extension of scalars"]
noncomputable abbrev derivedExtensionComplexCounit (σ : R →+* S) :
    (DerivedCategory.Q : CochainComplex (ModuleCat.{u, u} R) ℤ ⥤
        DerivedCategory (ModuleCat.{u, u} R)) ⋙ derivedExtensionOfScalars σ ⟶
      (ModuleCat.extendScalars.{u, u, u} σ).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex (ModuleCat.{u, u} S) ℤ ⥤
          DerivedCategory (ModuleCat.{u, u} S)) :=
  Functor.LeftDerived.Homotopy.cochainCounit
    (ModuleCat.extendScalars.{u, u, u} σ)

/-- The cochain-level unit exhibiting derived restriction of scalars as a right-derived
functor. -/
@[stacks 0BYX "cochain unit for derived restriction of scalars"]
noncomputable abbrev derivedRestrictionComplexUnit (σ : R →+* S) :
    (ModuleCat.restrictScalars.{u} σ).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex (ModuleCat.{u, u} R) ℤ ⥤
          DerivedCategory (ModuleCat.{u, u} R)) ⟶
      (DerivedCategory.Q : CochainComplex (ModuleCat.{u, u} S) ℤ ⥤
        DerivedCategory (ModuleCat.{u, u} S)) ⋙ derivedRestrictionOfScalars σ :=
  (ModuleCat.restrictScalars.{u} σ).mapDerivedCategoryFactors.inv

/-- Derived extension of scalars, with its canonical cochain comparison, is a left-derived
functor. -/
@[stacks 064M "derived extension of scalars is left-derived"]
instance derivedExtensionOfScalars_isLeftDerived (σ : R →+* S) :
    (derivedExtensionOfScalars σ).IsLeftDerivedFunctor
      (derivedExtensionComplexCounit σ)
      (HomologicalComplex.quasiIso (ModuleCat.{u, u} R) (up ℤ)) := sorry

/-- Derived restriction of scalars, with the canonical exact-functor comparison, is a
right-derived functor. -/
@[stacks 0BYX "derived restriction of scalars is right-derived"]
instance derivedRestrictionOfScalars_isRightDerived (σ : R →+* S) :
    (derivedRestrictionOfScalars σ).IsRightDerivedFunctor
      (derivedRestrictionComplexUnit σ)
      (HomologicalComplex.quasiIso (ModuleCat.{u, u} S) (up ℤ)) := sorry

/-- Derived extension followed by derived restriction retains the left-derived universal
property required to derive the extension-restriction adjunction. -/
@[stacks 064M "derived extension-restriction is left-derived"]
instance derivedExtensionRestriction_isLeftDerived (σ : R →+* S) :
    (derivedExtensionOfScalars σ ⋙ derivedRestrictionOfScalars σ).IsLeftDerivedFunctor
      ((Functor.associator
          (DerivedCategory.Q : CochainComplex (ModuleCat.{u, u} R) ℤ ⥤
            DerivedCategory (ModuleCat.{u, u} R))
          (derivedExtensionOfScalars σ) (derivedRestrictionOfScalars σ)).inv ≫
        Functor.whiskerRight (derivedExtensionComplexCounit σ)
          (derivedRestrictionOfScalars σ))
      (HomologicalComplex.quasiIso (ModuleCat.{u, u} R) (up ℤ)) := sorry

/-- Derived restriction followed by derived extension retains the right-derived universal
property required to derive the extension-restriction adjunction. -/
@[stacks 0BYX "derived restriction-extension is right-derived"]
instance derivedRestrictionExtension_isRightDerived (σ : R →+* S) :
    (derivedRestrictionOfScalars σ ⋙ derivedExtensionOfScalars σ).IsRightDerivedFunctor
      (Functor.whiskerRight
          (derivedRestrictionComplexUnit σ) (derivedExtensionOfScalars σ) ≫
        (Functor.associator
          (DerivedCategory.Q : CochainComplex (ModuleCat.{u, u} S) ℤ ⥤
            DerivedCategory (ModuleCat.{u, u} S))
          (derivedRestrictionOfScalars σ) (derivedExtensionOfScalars σ)).hom)
      (HomologicalComplex.quasiIso (ModuleCat.{u, u} S) (up ℤ)) := sorry

/-- Derived extension of scalars is left adjoint to derived restriction of scalars. -/
@[stacks 0BYX, stacks 0GMT "derived extension-restriction adjunction for modules"]
noncomputable def derivedExtensionRestrictionAdjunction (σ : R →+* S) :
    derivedExtensionOfScalars σ ⊣ derivedRestrictionOfScalars σ :=
  Adjunction.derived
    (Adjunction.mapHomologicalComplexAdjunction
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} σ) (up ℤ))
    (HomologicalComplex.quasiIso (ModuleCat.{u, u} R) (up ℤ))
    (HomologicalComplex.quasiIso (ModuleCat.{u, u} S) (up ℤ))
    (derivedExtensionComplexCounit σ) (derivedRestrictionComplexUnit σ)

/-- The Hom equivalence supplied by the derived extension-restriction adjunction. -/
@[stacks 0BYX, stacks 0GMT "derived extension-restriction Hom equivalence for modules"]
noncomputable def derivedExtensionRestrictionHomEquiv (σ : R →+* S)
    (K : DerivedCategory (ModuleCat.{u, u} R))
    (L : DerivedCategory (ModuleCat.{u, u} S)) :
    ((derivedExtensionOfScalars σ).obj K ⟶ L) ≃
      (K ⟶ (derivedRestrictionOfScalars σ).obj L) :=
  (derivedExtensionRestrictionAdjunction σ).homEquiv K L

end

end CategoryTheory.ModuleCat
