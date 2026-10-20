module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition

@[expose] public section

/-!
# Composition of derived restriction of scalars

The generic exact-functor composition comparison specializes to a canonical direct-to-iterated
restriction isomorphism.  This leaf supplies only the ring-map comparison between restriction
along a composite and the composite restriction functor; localization and exact-functor
composition remain owned by their generic reusable layers.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.DerivedRestriction

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- Derived restriction along a strict composite is canonically isomorphic to iterated derived
restriction. -/
@[stacks 0BYX "composition of derived restriction of scalars"]
noncomputable def compIso (σ : R →+* S) (τ : S →+* T) :
    ModuleCat.derivedRestrictionOfScalars (τ.comp σ) ≅
      ModuleCat.derivedRestrictionOfScalars τ ⋙
        ModuleCat.derivedRestrictionOfScalars σ :=
  Localization.liftNatIso
    (h₂ := ExactFunctor.MapDerivedCategory.compLifting (exact τ) (exact σ))
    (DerivedCategory.Q : CochainComplex (ModuleCat.{u, u} T) ℤ ⥤ _)
    (HomologicalComplex.quasiIso (ModuleCat.{u, u} T) (up ℤ))
    ((ModuleCat.restrictScalars (τ.comp σ)).mapHomologicalComplex (up ℤ) ⋙
      (DerivedCategory.Q : CochainComplex (ModuleCat.{u, u} R) ℤ ⥤ _))
    (((exact τ).comp (exact σ)).obj.mapHomologicalComplex (up ℤ) ⋙
      (DerivedCategory.Q : CochainComplex (ModuleCat.{u, u} R) ℤ ⥤ _))
    (ModuleCat.derivedRestrictionOfScalars (τ.comp σ))
    (ModuleCat.derivedRestrictionOfScalars τ ⋙
      ModuleCat.derivedRestrictionOfScalars σ)
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex
        (ModuleCat.restrictScalarsComp' σ τ (τ.comp σ) rfl) (up ℤ))
      (DerivedCategory.Q : CochainComplex (ModuleCat.{u, u} R) ℤ ⥤ _))

/-- The objectwise direct-to-iterated comparison for derived restriction of scalars. -/
noncomputable abbrev compObjIso (σ : R →+* S) (τ : S →+* T)
    (K : DerivedCategory (ModuleCat.{u, u} T)) :
    (ModuleCat.derivedRestrictionOfScalars (τ.comp σ)).obj K ≅
      (ModuleCat.derivedRestrictionOfScalars σ).obj
        ((ModuleCat.derivedRestrictionOfScalars τ).obj K) :=
  (compIso σ τ).app K

/-- Direct derived restriction along a map identified with a composite is isomorphic to the
corresponding iterated derived restriction. -/
noncomputable def compIsoOfEq
    (σ : R →+* S) (τ : S →+* T) (ρ : R →+* T) (hρ : ρ = τ.comp σ) :
    ModuleCat.derivedRestrictionOfScalars ρ ≅
      ModuleCat.derivedRestrictionOfScalars τ ⋙
        ModuleCat.derivedRestrictionOfScalars σ :=
  eqToIso (congrArg ModuleCat.derivedRestrictionOfScalars hρ) ≪≫ compIso σ τ

/-- The objectwise direct-to-iterated comparison transported along an equality with a strict
composite. -/
noncomputable abbrev compObjIsoOfEq
    (σ : R →+* S) (τ : S →+* T) (ρ : R →+* T) (hρ : ρ = τ.comp σ)
    (K : DerivedCategory (ModuleCat.{u, u} T)) :
    (ModuleCat.derivedRestrictionOfScalars ρ).obj K ≅
      (ModuleCat.derivedRestrictionOfScalars σ).obj
        ((ModuleCat.derivedRestrictionOfScalars τ).obj K) :=
  (compIsoOfEq σ τ ρ hρ).app K

end CategoryTheory.ModuleCat.DerivedRestriction
