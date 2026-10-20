module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleModuleComparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.ProEtaleComparison
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-!
# Derived comparison of constructible module sheaves

Canonical derived inverse image from the small étale site to the small pro-étale
site restricts to an equivalence on bounded-below complexes with constructible
cohomology sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
variable [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (etaleToProEt X).op.HasLeftKanExtension F]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]
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

/-- Derived inverse image from the small étale site to the small pro-étale site
preserves bounded-below complexes with constructible cohomology sheaves. -/
theorem etaleToProEt_modulePlusPullback_constructibleModule_le :
    DerivedCategory.Plus.cohomologyIn (constructibleEtaleModule X Λ) ≤
      ObjectProperty.inverseImage
        (DerivedCategory.Plus.cohomologyIn (constructibleProEtaleModule X Λ))
        (etaleToProEt_modulePlusPullback X Λ) :=
  sorry

/-- Canonical derived inverse image restricted to bounded-below complexes with
constructible cohomology sheaves of `Λ`-modules. -/
def etaleToProEt_modulePlusPullback_constructibleModule :
    DerivedCategory.Plus.CohomologyIn (constructibleEtaleModule X Λ) ⥤
      DerivedCategory.Plus.CohomologyIn (constructibleProEtaleModule X Λ) :=
  ObjectProperty.FullSubcategory.restrict
    (etaleToProEt_modulePlusPullback X Λ)
    (etaleToProEt_modulePlusPullback_constructibleModule_le X Λ)

/-- The underlying object of restricted derived inverse image is the ambient
derived inverse image of the underlying object. -/
theorem etaleToProEt_modulePlusPullback_constructibleModule_obj
    (K : DerivedCategory.Plus.CohomologyIn (constructibleEtaleModule X Λ)) :
    ((etaleToProEt_modulePlusPullback_constructibleModule X Λ).obj K).obj =
      (etaleToProEt_modulePlusPullback X Λ).obj K.obj :=
  rfl

/-- For a scheme `X` and a Noetherian ring `Λ`, canonical derived inverse image
is an equivalence between the bounded-below derived full subcategories with
constructible cohomology sheaves on the small étale and small pro-étale sites. -/
instance etaleToProEt_modulePlusPullback_constructibleModule_isEquivalence :
    (etaleToProEt_modulePlusPullback_constructibleModule X Λ).IsEquivalence :=
  sorry

end AlgebraicGeometry.Scheme

end

end
