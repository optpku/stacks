/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.BoundedBelow

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived.Composition.BoundedBelow.Square

noncomputable section

universe w u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}
variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]
variable [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

#check (AlgebraicGeometry.Scheme.Hom.etalePullbackExact :
  ∀ {Z Z' : Scheme.{u}} (p : Z' ⟶ Z),
    Sheaf Z.smallEtaleTopology AddCommGrpCat.{u} ⥤ₑ
      Sheaf Z'.smallEtaleTopology AddCommGrpCat.{u})

#check (AlgebraicGeometry.Scheme.Hom.etaleDerivedInverseImage :
  ∀ {Z Z' : Scheme.{u}} (p : Z' ⟶ Z),
    DerivedCategory.Plus (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) ⥤
      DerivedCategory.Plus (Sheaf Z'.smallEtaleTopology AddCommGrpCat.{u}))

#check (AlgebraicGeometry.Scheme.Hom.etaleDerivedPushforward :
  ∀ {A B : Scheme.{u}} (p : A ⟶ B)
    [(abelianPushforwardAlong p).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf A.smallEtaleTopology AddCommGrpCat.{u}))],
    DerivedCategory.Plus (Sheaf A.smallEtaleTopology AddCommGrpCat.{u}) ⥤
      DerivedCategory.Plus (Sheaf B.smallEtaleTopology AddCommGrpCat.{u}))

#check (AlgebraicGeometry.Scheme.Hom.derivedSourceComparison :
  ∀
    (f : X ⟶ Y) {Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [(abelianPushforwardAlong f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact g).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong f ⋙ (etalePullbackExact g).obj).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))],
    Functor.RightDerived.Bounded.functor
        (abelianPushforwardAlong f ⋙ (etalePullbackExact g).obj) ⟶
      etaleDerivedPushforward f ⋙ etaleDerivedInverseImage g)

#check (AlgebraicGeometry.Scheme.Hom.derivedBaseChange :
  ∀
    (f : X ⟶ Y) {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    [(abelianPushforwardAlong f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong f').toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact g).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact g').obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong f ⋙ (etalePullbackExact g).obj).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [((etalePullbackExact g').obj ⋙ abelianPushforwardAlong f').toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    (h_src : IsIso (derivedSourceComparison f g)),
    etaleDerivedPushforward f ⋙ etaleDerivedInverseImage g ⟶
      etaleDerivedInverseImage g' ⋙ etaleDerivedPushforward f')

#check (AlgebraicGeometry.Scheme.Hom.derivedBaseChangeHom :
  ∀
    (f : X ⟶ Y) {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    [(abelianPushforwardAlong f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong f').toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact g).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact g').obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong f ⋙ (etalePullbackExact g).obj).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [((etalePullbackExact g').obj ⋙ abelianPushforwardAlong f').toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    (h_src : IsIso (derivedSourceComparison f g))
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})),
    (etaleDerivedPushforward f ⋙ etaleDerivedInverseImage g).obj E ⟶
      (etaleDerivedInverseImage g' ⋙ etaleDerivedPushforward f').obj E)

#check (AlgebraicGeometry.Scheme.Hom.derivedBaseChange_eq :
  ∀
    (f : X ⟶ Y) {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    [(abelianPushforwardAlong f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong f').toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact g).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact g').obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong f ⋙ (etalePullbackExact g).obj).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [((etalePullbackExact g').obj ⋙ abelianPushforwardAlong f').toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    (h_src : IsIso (derivedSourceComparison f g)),
    derivedBaseChange f g f' g' h_cart h_src =
      Exact.map (underivedBaseChange f g f' g' h_cart) h_src)

#check (AlgebraicGeometry.Scheme.Hom.derivedBaseChangeHom_eq :
  ∀
    (f : X ⟶ Y) {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    [(abelianPushforwardAlong f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong f').toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact g).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact g').obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong f ⋙ (etalePullbackExact g).obj).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [((etalePullbackExact g').obj ⋙ abelianPushforwardAlong f').toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    (h_src : IsIso (derivedSourceComparison f g))
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})),
    derivedBaseChangeHom f g f' g' h_cart h_src E =
      (derivedBaseChange f g f' g' h_cart h_src).app E)

#check (AlgebraicGeometry.Scheme.Hom.derivedBaseChange_isMap :
  ∀
    (f : X ⟶ Y) {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    [(abelianPushforwardAlong f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong f').toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact g).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact g').obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong f ⋙ (etalePullbackExact g).obj).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [((etalePullbackExact g').obj ⋙ abelianPushforwardAlong f').toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    (h_src : IsIso (derivedSourceComparison f g)),
    Exact.IsMap (underivedBaseChange f g f' g' h_cart)
      (derivedBaseChange f g f' g' h_cart h_src))

end AlgebraicGeometry.Scheme.Hom

end

end
