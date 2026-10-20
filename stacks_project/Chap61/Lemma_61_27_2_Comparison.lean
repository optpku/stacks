module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.ProEtaleComparison

/-!
# Restricted inverse image of constructible module sheaves

Inverse image `ε⁻¹` along `etaleToProEt` preserves constructible sheaves of
`Λ`-modules, and therefore restricts to a functor between the corresponding
full subcategories of sheaves on `X.Etale` and `X.ProEt`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.Sheaf

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (Λ : Type w) [Ring Λ] [IsNoetherianRing Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ Y : Scheme.{u}, HasWeakSheafify (ProEt.topology Y) (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.ProEt),
    HasWeakSheafify ((ProEt.topology Y).over U) (ModuleCat.{w} Λ)]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ),
    (ProEt.baseChange f).op.HasLeftKanExtension P]
variable [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ, (etaleToProEt X).op.HasLeftKanExtension F]

#check (AlgebraicGeometry.Scheme.etaleToProEtPullback_constructibleModule X Λ :
  (AlgebraicGeometry.Scheme.constructibleEtaleModule X Λ).FullSubcategory ⥤
    (AlgebraicGeometry.Scheme.constructibleProEtaleModule X Λ).FullSubcategory)

end AlgebraicGeometry.Scheme

