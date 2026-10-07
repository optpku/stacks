module

public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import stacks_project.Chap61.Lemma_61_19_8_Comparison
public import stacks_project.Chap61.Lemma_61_27_2_Comparison

/-!
# Restricted derived inverse image on constructible cohomology

Derived inverse image `ε⁻¹` along `etaleToProEt` preserves bounded-below complexes
whose cohomology sheaves are constructible sheaves of `Λ`-modules, and therefore
restricts to a functor between the corresponding full subcategories of
`D⁺(X.Etale, Λ)` and `D⁺(X.ProEt, Λ)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
variable [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (etaleToProEt X).op.HasLeftKanExtension F]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]
variable [PreservesFiniteLimits (etaleToProEtPullback X (ModuleCat.{u + 1} Λ))]
variable [PreservesFiniteColimits (etaleToProEtPullback X (ModuleCat.{u + 1} Λ))]
variable [∀ U : X.Etale,
    HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.ProEt,
    HasWeakSheafify ((ProEt.topology X).over U) (ModuleCat.{u + 1} Λ)]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ Y : Scheme.{u}, HasWeakSheafify (ProEt.topology Y) (ModuleCat.{u + 1} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.ProEt),
    HasWeakSheafify ((ProEt.topology Y).over U) (ModuleCat.{u + 1} Λ)]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} Λ),
    (ProEt.baseChange f).op.HasLeftKanExtension P]

/-- Bounded-below derived objects whose cohomology sheaves are constructible
sheaves of `Λ`-modules are sent by derived `ε⁻¹` into the corresponding
pro-étale class. -/
theorem etaleToProEt_modulePlusPullback_constructibleModule_le :
    DerivedCategory.Plus.cohomologyIn (constructibleEtaleModule X Λ) ≤
      ObjectProperty.inverseImage
        (DerivedCategory.Plus.cohomologyIn (constructibleProEtaleModule X Λ))
        (etaleToProEt_modulePlusPullback X Λ) :=
  sorry

/-- Inverse image `ε⁻¹` along `etaleToProEt`, restricted to `D⁺` objects whose
cohomology sheaves are constructible sheaves of `Λ`-modules. -/
def etaleToProEt_modulePlusPullback_constructibleModule :
    DerivedCategory.Plus.CohomologyIn (constructibleEtaleModule X Λ) ⥤
      DerivedCategory.Plus.CohomologyIn (constructibleProEtaleModule X Λ) :=
  ObjectProperty.FullSubcategory.restrict
    (etaleToProEt_modulePlusPullback X Λ)
    (etaleToProEt_modulePlusPullback_constructibleModule_le X Λ)

end AlgebraicGeometry.Scheme

end

end
