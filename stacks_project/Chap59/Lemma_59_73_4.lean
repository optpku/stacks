/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u w

namespace CategoryTheory.Sheaf

/- Lemma 59.73.4 (1): finite étale direct image preserves constructibility of sheaves of sets. -/
@[stacks 095H] #check
  (CategoryTheory.Sheaf.isConstructibleEtaleSet_smallEtalePushforward :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
      [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (Type (u + 1))]
      [∀ (Z W : Scheme.{u}) (g : Z ⟶ W) (P : W.Etaleᵒᵖ ⥤ Type (u + 1)),
        (Scheme.smallEtalePullback g).op.HasLeftKanExtension P]
      (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
      (hF : IsConstructibleEtaleSet (X := X)
        (fun {Z} g ↦ (smallEtaleInverseImage g (Type (u + 1))).obj)
        (fun {Z} G ↦ IsFiniteLocallyConstant G) F),
      IsConstructibleEtaleSet (X := Y)
        (fun {Z} g ↦ (smallEtaleInverseImage g (Type (u + 1))).obj)
        (fun {Z} G ↦ IsFiniteLocallyConstant G)
        (((Scheme.smallEtalePullback f).sheafPushforwardContinuous
          (Type (u + 1)) Y.smallEtaleTopology X.smallEtaleTopology).obj F))

/- Lemma 59.73.4 (2): finite étale direct image preserves constructibility of sheaves of abelian
groups. -/
@[stacks 095H] #check
  (CategoryTheory.Sheaf.isConstructibleEtaleAddCommGrp_smallEtalePushforward :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
      [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [∀ (Z W : Scheme.{u}) (g : Z ⟶ W) (P : W.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
        (Scheme.smallEtalePullback g).op.HasLeftKanExtension P]
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (hF : IsConstructibleEtaleAddCommGrp (X := X)
        (fun {Z} g ↦ (smallEtaleInverseImage g AddCommGrpCat.{u + 1}).obj)
        (fun {Z} G ↦ IsFiniteLocallyConstantAddCommGrp G) F),
      IsConstructibleEtaleAddCommGrp (X := Y)
        (fun {Z} g ↦ (smallEtaleInverseImage g AddCommGrpCat.{u + 1}).obj)
        (fun {Z} G ↦ IsFiniteLocallyConstantAddCommGrp G)
        (((Scheme.smallEtalePullback f).sheafPushforwardContinuous
          (AddCommGrpCat.{u + 1}) Y.smallEtaleTopology X.smallEtaleTopology).obj F))

/- Lemma 59.73.4 (3): finite étale direct image preserves constructibility of sheaves of modules
over a Noetherian ring. -/
@[stacks 095H] #check
  (CategoryTheory.Sheaf.isConstructibleEtaleModule_smallEtalePushforward :
    ∀ {X Y : Scheme.{u}} {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
      (f : X ⟶ Y) [IsFinite f] [Etale f]
      [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{w} Λ)]
      [∀ (Z : Scheme.{u}) (U : Z.Etale),
        HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
      [∀ (Z W : Scheme.{u}) (g : Z ⟶ W) (P : W.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
        (Scheme.smallEtalePullback g).op.HasLeftKanExtension P]
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))
      (hF : IsConstructibleEtaleModule (X := X)
        (fun {Z} g ↦ (smallEtaleInverseImage g (ModuleCat.{w} Λ)).obj)
        (fun {Z} G ↦ IsFiniteTypeLocallyConstantModule G) F),
      IsConstructibleEtaleModule (X := Y)
        (fun {Z} g ↦ (smallEtaleInverseImage g (ModuleCat.{w} Λ)).obj)
        (fun {Z} G ↦ IsFiniteTypeLocallyConstantModule G)
        (((Scheme.smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{w} Λ) Y.smallEtaleTopology X.smallEtaleTopology).obj F))

end CategoryTheory.Sheaf
