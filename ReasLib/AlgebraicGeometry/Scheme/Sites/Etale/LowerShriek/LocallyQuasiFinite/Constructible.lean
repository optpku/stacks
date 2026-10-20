module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.Module

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
  [Scheme.Hom.FinitePresentation f]
variable (Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ (Z : Scheme.{u}) (V : Z.Etale),
  HasWeakSheafify (Z.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [∀ (Z : Scheme.{u}) (g : Z ⟶ X) (G : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (smallEtalePullback g).op.HasLeftKanExtension G]
variable [∀ (Z : Scheme.{u}) (g : Z ⟶ Y) (G : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (smallEtalePullback g).op.HasLeftKanExtension G]
/-- Compact-support direct image along a locally quasi-finite morphism of finite
presentation sends constructible étale sheaves of modules over a Noetherian ring
to constructible étale sheaves of modules. -/
theorem lowerShriekModule_isConstructibleEtaleModule
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (hF : Sheaf.IsConstructibleEtaleModule
      (fun {Z} g ↦
        ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
          X.smallEtaleTopology Z.smallEtaleTopology).obj)
      (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F) :
    Sheaf.IsConstructibleEtaleModule
      (fun {Z} g ↦
        ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
          Y.smallEtaleTopology Z.smallEtaleTopology).obj)
      (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)
      ((lowerShriekModule f Λ).obj F) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
