module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme

/- Lemma 59.70.5 (Extension by zero commutes with base change) -/
@[stacks 03S6] #check (AlgebraicGeometry.Scheme.abelianExtensionByZero_baseChange :
    ∀ {X Y V : Scheme.{u}} (f : Y ⟶ X) (j : V ⟶ X) [Etale j]
    [∀ F : (pullback f j).Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (etaleRestriction (pullback.fst f j)).op.HasLeftKanExtension F]
    [∀ F : V.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [Functor.IsRightAdjoint ((smallEtalePullback (pullback.snd f j)).sheafPushforwardContinuous
      AddCommGrpCat.{w} V.smallEtaleTopology (pullback f j).smallEtaleTopology)]
    [Functor.IsRightAdjoint ((smallEtalePullback f).sheafPushforwardContinuous
      AddCommGrpCat.{w} X.smallEtaleTopology Y.smallEtaleTopology)],
    Nonempty (
      (smallEtalePullback (pullback.snd f j)).sheafPullback
          AddCommGrpCat.{w} V.smallEtaleTopology
          (pullback f j).smallEtaleTopology ⋙
        abelianExtensionByZero (pullback.fst f j) ≅
      abelianExtensionByZero j ⋙
        (smallEtalePullback f).sheafPullback AddCommGrpCat.{w}
          X.smallEtaleTopology Y.smallEtaleTopology))

/- The corresponding base-change statement for sheaves of modules. -/
#check (AlgebraicGeometry.Scheme.moduleExtensionByZero_baseChange :
    ∀ {X Y V : Scheme.{u}} {Λ : Type w} [Ring Λ]
    (f : Y ⟶ X) (j : V ⟶ X) [Etale j]
    [∀ F : (pullback f j).Etaleᵒᵖ ⥤ ModuleCat.{w} Λ,
      (etaleRestriction (pullback.fst f j)).op.HasLeftKanExtension F]
    [∀ F : V.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ,
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
    [Functor.IsRightAdjoint ((smallEtalePullback (pullback.snd f j)).sheafPushforwardContinuous
      (ModuleCat.{w} Λ) V.smallEtaleTopology (pullback f j).smallEtaleTopology)]
    [Functor.IsRightAdjoint ((smallEtalePullback f).sheafPushforwardContinuous
      (ModuleCat.{w} Λ) X.smallEtaleTopology Y.smallEtaleTopology)],
    Nonempty (
      (smallEtalePullback (pullback.snd f j)).sheafPullback
          (ModuleCat.{w} Λ) V.smallEtaleTopology
          (pullback f j).smallEtaleTopology ⋙
        moduleExtensionByZero (pullback.fst f j) ≅
      moduleExtensionByZero j ⋙
        (smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
          X.smallEtaleTopology Y.smallEtaleTopology))

end AlgebraicGeometry.Scheme
