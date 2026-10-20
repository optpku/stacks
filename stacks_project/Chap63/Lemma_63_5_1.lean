module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.ProjectionFormula

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
variable (Λ : Type u) [CommRing Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [(X.smallEtaleTopology.W (A := ModuleCat.{u} Λ)).IsMonoidal]
variable [(Y.smallEtaleTopology.W (A := ModuleCat.{u} Λ)).IsMonoidal]

variable [LocallyOfFiniteType f]
variable (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
variable (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))

/- Lemma 63.5.1: Let `f : X ⟶ Y` be a locally quasi-finite morphism of schemes.
Let `Λ` be a ring. Let `F` be a sheaf of `Λ`-modules on `X_étale` and let `G`
be a sheaf of `Λ`-modules on `Y_étale`. There is a canonical isomorphism
`can : f_! F ⊗_Λ G ⟶ f_!(F ⊗_Λ f⁻¹ G)` of sheaves of `Λ`-modules on
`Y_étale`, where `f_!` is `lowerShriekModule`, `⊗_Λ` is the sheaf tensor, and
`f⁻¹` is small-étale `sheafPullback`. Stacks locally quasi-finite is rendered
as `[LocallyQuasiFinite f]` together with `[LocallyOfFiniteType f]`. -/
@[stacks 0GKF] #check (AlgebraicGeometry.Scheme.Etale.lowerShriekProjectionIso f Λ F G :
  (lowerShriekModule f Λ).obj F ⊗ G ≅
    (lowerShriekModule f Λ).obj
      (F ⊗ ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
          Y.smallEtaleTopology X.smallEtaleTopology).obj G))

end
