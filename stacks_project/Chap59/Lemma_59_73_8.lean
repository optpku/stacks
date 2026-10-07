module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.FinitePresentation

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u w

/- Lemma 59.73.8 (1): a constructible set-valued étale sheaf on a quasi-compact
quasi-separated scheme is finitely presentable. -/
@[stacks 09Z4] #check
  (CategoryTheory.Sheaf.isFinitelyPresentable_of_isConstructibleEtaleSet :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (F : Sheaf X.smallEtaleTopology (Type (u + 1))),
      Sheaf.IsConstructibleEtaleSet
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ Sheaf.IsFiniteLocallyConstant G) F →
      IsFinitelyPresentable.{u + 1} F)

/- Lemma 59.73.8 (2): a constructible abelian-group-valued étale sheaf on a
quasi-compact quasi-separated scheme is finitely presentable. -/
@[stacks 09Z4] #check
  (CategoryTheory.Sheaf.isFinitelyPresentable_of_isConstructibleEtaleAddCommGrp :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      Sheaf.IsConstructibleEtaleAddCommGrp
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ Sheaf.IsFiniteLocallyConstantAddCommGrp G) F →
      IsFinitelyPresentable.{u + 1} F)

/- Lemma 59.73.8 (3): a constructible étale sheaf of modules over a Noetherian
ring on a quasi-compact quasi-separated scheme is finitely presentable. -/
@[stacks 09Z4] #check
  (CategoryTheory.Sheaf.isFinitelyPresentable_of_isConstructibleEtaleModule :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
      [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
      [∀ (Y : Scheme.{u}) (U : Y.Etale),
        HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
      [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z) (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
        (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)),
      Sheaf.IsConstructibleEtaleModule
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)) ↦
          Sheaf.IsFiniteTypeLocallyConstantModule G) F →
      IsFinitelyPresentable.{max (u + 1) w} F)
