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

/- Lemma 59.73.9 (1): if `f : X ⟶ Y` is a finite and finitely presented morphism of schemes and
`F` is a constructible sheaf of sets on `Xₑₜ`, then `f_* F` is constructible on `Yₑₜ`, where
`f_*` is `(Scheme.smallEtalePullback f).sheafPushforwardContinuous`. -/
@[stacks 095R] #check
  (CategoryTheory.Sheaf.isConstructibleEtaleSet_smallEtalePushforward_of_finite_fp :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [LocallyOfFinitePresentation f]
      [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (Type (u + 1))]
      [∀ (Z : Scheme.{u}) (U : Z.Etale),
        HasWeakSheafify (Z.smallEtaleTopology.over U) (Type (u + 1))]
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

/- Lemma 59.73.9 (2): if `f : X ⟶ Y` is a finite and finitely presented morphism of schemes and
`F` is a constructible sheaf of abelian groups on `Xₑₜ`, then `f_* F` is constructible on
`Yₑₜ`, where `f_*` is `(Scheme.smallEtalePullback f).sheafPushforwardContinuous`. -/
@[stacks 095R] #check
  (CategoryTheory.Sheaf.isConstructibleEtaleAddCommGrp_smallEtalePushforward_of_finite_fp :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [LocallyOfFinitePresentation f]
      [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [∀ (Z : Scheme.{u}) (U : Z.Etale),
        HasWeakSheafify (Z.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
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
          AddCommGrpCat.{u + 1} Y.smallEtaleTopology X.smallEtaleTopology).obj F))

/- Lemma 59.73.9 (3): if `f : X ⟶ Y` is a finite and finitely presented morphism of schemes,
`Λ` is Noetherian, and `F` is a constructible sheaf of `Λ`-modules on `Xₑₜ`, then `f_* F` is
constructible on `Yₑₜ`, where `f_*` is
`(Scheme.smallEtalePullback f).sheafPushforwardContinuous`. -/
@[stacks 095R] #check
  (CategoryTheory.Sheaf.isConstructibleEtaleModule_smallEtalePushforward_of_finite_fp :
    ∀ {X Y : Scheme.{u}} {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
      (f : X ⟶ Y) [IsFinite f] [LocallyOfFinitePresentation f]
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
