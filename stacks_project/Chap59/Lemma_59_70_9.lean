module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero.FinitePushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 59.70.9 -/
@[stacks 0GJ1] #check
  (AlgebraicGeometry.Scheme.abelianExtensionByZero_comp_etaleAbelianPushforward :
    ∀ {U X V Y : Scheme.{u}} (j' : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
      [Etale j] [Etale j']
      [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
        (etaleRestriction j').op.HasLeftKanExtension F]
      [∀ F : V.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
        (etaleRestriction j).op.HasLeftKanExtension F]
      [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
      [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
      [IsFinite f] [IsOpenImmersion j]
      (h_cart : IsPullback j' g f j),
      IsIso (abelianExtensionByZeroFinitePushforwardComparison j' g f j h_cart))

/- Objectwise form of Lemma 59.70.9. -/
#check
  (AlgebraicGeometry.Scheme.abelianExtensionByZero_comp_etaleAbelianPushforward_app :
    ∀ {U X V Y : Scheme.{u}} (j' : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
      [Etale j] [Etale j']
      [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
        (etaleRestriction j').op.HasLeftKanExtension F]
      [∀ F : V.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
        (etaleRestriction j).op.HasLeftKanExtension F]
      [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
      [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
      [IsFinite f] [IsOpenImmersion j]
      (h_cart : IsPullback j' g f j)
      (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}),
      IsIso ((abelianExtensionByZeroFinitePushforwardComparison j' g f j h_cart).app F))

end AlgebraicGeometry.Scheme
