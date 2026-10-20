module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero.ProperSupport
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe u

/- Lemma 63.3.2: for a separated étale morphism `j : U ⟶ X` and an abelian
sheaf `F` on `U_étale`, the image of the injective comparison `j_! F ⟶ j_* F`
is the subsheaf of sections with support proper over the étale base object. -/
@[stacks 0F4Y] #check
  (AlgebraicGeometry.Scheme.Etale.abelianExtensionByZeroToDirectImage_range_eq :
    ∀ {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] [IsSeparated j]
      [∀ G : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
        (etaleRestriction j).op.HasLeftKanExtension G]
      [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
      (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}),
      Subfunctor.range
        (Functor.whiskerRight
          ((AlgebraicGeometry.Scheme.abelianExtensionByZeroToDirectImage j).app F).hom
          (CategoryTheory.forget AddCommGrpCat)) =
        properSupportSubfunctor j F)

#check
  (AlgebraicGeometry.Scheme.Etale.mem_range_abelianExtensionByZeroToDirectImage_iff :
    ∀ {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] [IsSeparated j]
      [∀ G : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
        (etaleRestriction j).op.HasLeftKanExtension G]
      [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
      (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u})
      (V : X.Etale) (σ : F.obj.obj (op ((smallEtalePullback j).obj V))),
      (∃ τ,
        ((AlgebraicGeometry.Scheme.abelianExtensionByZeroToDirectImage j).app F).hom.app
          (op V) τ = σ) ↔
        HasProperSupport j F V σ)
