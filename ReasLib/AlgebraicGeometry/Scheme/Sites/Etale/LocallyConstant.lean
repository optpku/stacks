/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Basic

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme

/-- Pullback of a locally constant sheaf of types along a morphism of schemes is locally constant. -/
theorem sheafPullback_isLocallyConstant_sets
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (Type v)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type v)]
    [HasWeakSheafify Y.smallEtaleTopology (Type v)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (Type v)]
    [∀ P : Y.Etaleᵒᵖ ⥤ Type v,
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    (G : Sheaf Y.smallEtaleTopology (Type v)) [Sheaf.IsLocallyConstant G] :
    Sheaf.IsLocallyConstant
      ((Functor.sheafPullbackConstruction.sheafPullback
        (Scheme.smallEtalePullback f) (Type v)
        Y.smallEtaleTopology X.smallEtaleTopology).obj G) := sorry

/-- Pullback of a locally constant sheaf of additive commutative groups along a morphism of schemes is locally constant. -/
theorem sheafPullback_isLocallyConstant_addCommGrp
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [∀ U : X.Etale,
      HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{w}]
    [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [∀ U : Y.Etale,
      HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{w}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{w})
    [Sheaf.IsLocallyConstant G] :
    Sheaf.IsLocallyConstant
      ((Functor.sheafPullbackConstruction.sheafPullback
        (Scheme.smallEtalePullback f) AddCommGrpCat.{w}
        Y.smallEtaleTopology X.smallEtaleTopology).obj G) := sorry

/-- Pullback of a locally constant sheaf of modules along a morphism of schemes is locally constant. -/
theorem sheafPullback_isLocallyConstant_module
    {X Y : Scheme.{u}} {Λ : Type w} [Ring Λ] (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
    [∀ U : X.Etale,
      HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
    [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
    [∀ U : Y.Etale,
      HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ,
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ))
    [Sheaf.IsLocallyConstant G] :
    Sheaf.IsLocallyConstant
      ((Functor.sheafPullbackConstruction.sheafPullback
        (Scheme.smallEtalePullback f) (ModuleCat.{w} Λ)
        Y.smallEtaleTopology X.smallEtaleTopology).obj G) := sorry

end AlgebraicGeometry.Scheme
