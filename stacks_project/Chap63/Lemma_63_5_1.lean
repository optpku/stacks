/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap63.Lemma_63_5_1_LowerShriek
public import stacks_project.Chap63.Lemma_63_5_1_Projection

/-!
# Projection formula for compact-support direct image along locally quasi-finite morphisms

Lemma 63.5.1: for a locally quasi-finite morphism `f : X ⟶ Y` of schemes, a
ring `Λ`, an étale sheaf `F` of `Λ`-modules on `X` and an étale sheaf `G` of
`Λ`-modules on `Y`, there is a canonical isomorphism
`can : f_! F ⊗_Λ G ≅ f_!(F ⊗_Λ f⁻¹ G)` of étale sheaves of `Λ`-modules on `Y`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

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
variable [MonoidalCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [MonoidalCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [(presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).Monoidal]
variable [(presheafToSheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)).Monoidal]

/-- Lemma 63.5.1: Let `f : X ⟶ Y` be a locally quasi-finite morphism of schemes.
Let `Λ` be a ring. Let `F` be a sheaf of `Λ`-modules on `X_étale` and let `G`
be a sheaf of `Λ`-modules on `Y_étale`. There is a canonical isomorphism
`can : f_! F ⊗_Λ G ⟶ f_!(F ⊗_Λ f⁻¹ G)` of sheaves of `Λ`-modules on
`Y_étale`, where `f_!` is `lowerShriekModule`, `⊗_Λ` is the sheaf tensor, and
`f⁻¹` is small-étale `sheafPullback`. Stacks locally quasi-finite is rendered
as `[LocallyQuasiFinite f]` together with `[LocallyOfFiniteType f]`. -/
@[stacks 0GKF]
def lowerShriekProjectionIso [LocallyOfFiniteType f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule f Λ).obj F ⊗ G ≅
      (lowerShriekModule f Λ).obj
        (F ⊗ ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
            Y.smallEtaleTopology X.smallEtaleTopology).obj G) :=
  asIso (lowerShriekProjectionHom f Λ F G)

/-- The forward map of the isomorphism of Lemma 63.5.1 is the constructed
comparison `can`. -/
theorem lowerShriekProjectionIso_hom [LocallyOfFiniteType f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekProjectionIso f Λ F G).hom =
      lowerShriekProjectionHom f Λ F G :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
