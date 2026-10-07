module

public import stacks_project.Chap59.Lemma_59_91_6_BaseChange
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow.Square.Exact
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Tactic.CrossRefAttribute

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

/-- Exact inverse image of abelian small-étale sheaves along a morphism of schemes. -/
noncomputable abbrev etalePullbackExact {Z Z' : Scheme.{u}} (p : Z' ⟶ Z) :
    Sheaf Z.smallEtaleTopology AddCommGrpCat.{u} ⥤ₑ
      Sheaf Z'.smallEtaleTopology AddCommGrpCat.{u} :=
  ExactFunctor.of (etaleAbelianSheafPullback p)

/-- Derived inverse image `p⁻¹` on `D⁺` of abelian small-étale sheaves. -/
noncomputable abbrev etaleDerivedInverseImage {Z Z' : Scheme.{u}} (p : Z' ⟶ Z) :
    DerivedCategory.Plus (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) ⥤
      DerivedCategory.Plus (Sheaf Z'.smallEtaleTopology AddCommGrpCat.{u}) :=
  ExactFunctor.Derived.Plus.functor (etalePullbackExact p)

/-- Derived pushforward `Rp_*` on `D⁺` of abelian small-étale sheaves. -/
noncomputable abbrev etaleDerivedPushforward {A B : Scheme.{u}} (p : A ⟶ B)
    [(abelianPushforwardAlong p).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf A.smallEtaleTopology AddCommGrpCat.{u}))] :
    DerivedCategory.Plus (Sheaf A.smallEtaleTopology AddCommGrpCat.{u}) ⥤
      DerivedCategory.Plus (Sheaf B.smallEtaleTopology AddCommGrpCat.{u}) :=
  Functor.RightDerived.Bounded.functor (abelianPushforwardAlong p)

/-- Canonical comparison `R(g⁻¹ f_*) ⟶ Rf_* ⋙ g⁻¹` on `D⁺`. -/
noncomputable abbrev derivedSourceComparison
    (f : X ⟶ Y) {Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [(abelianPushforwardAlong f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact g).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong f ⋙ (etalePullbackExact g).obj).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))] :
    Functor.RightDerived.Bounded.functor
        (abelianPushforwardAlong f ⋙ (etalePullbackExact g).obj) ⟶
      etaleDerivedPushforward f ⋙ etaleDerivedInverseImage g :=
  Exact.sourceComparison

/-- Canonical derived base-change transformation `g⁻¹ Rf_* ⟶ Rf'_* (g')⁻¹` on `D⁺`. -/
noncomputable def derivedBaseChange
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
    (h_src : IsIso (derivedSourceComparison f g)) :
    etaleDerivedPushforward f ⋙ etaleDerivedInverseImage g ⟶
      etaleDerivedInverseImage g' ⋙ etaleDerivedPushforward f' :=
  Exact.map (underivedBaseChange f g f' g' h_cart) h_src

/-- Component of derived base change at an object of `D⁺(X_étale)`. -/
noncomputable def derivedBaseChangeHom
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
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    (etaleDerivedPushforward f ⋙ etaleDerivedInverseImage g).obj E ⟶
      (etaleDerivedInverseImage g' ⋙ etaleDerivedPushforward f').obj E :=
  (derivedBaseChange f g f' g' h_cart h_src).app E

/-- `derivedBaseChange` is the exact-horizontal square map of the underived mate. -/
theorem derivedBaseChange_eq
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
    (h_src : IsIso (derivedSourceComparison f g)) :
    derivedBaseChange f g f' g' h_cart h_src =
      Exact.map (underivedBaseChange f g f' g' h_cart) h_src := sorry

/-- `derivedBaseChangeHom` is the component of `derivedBaseChange`. -/
theorem derivedBaseChangeHom_eq
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
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    derivedBaseChangeHom f g f' g' h_cart h_src E =
      (derivedBaseChange f g f' g' h_cart h_src).app E := sorry

/-- The derived base-change transformation satisfies the exact-horizontal square
specification relative to the underived mate. -/
theorem derivedBaseChange_isMap
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
    (h_src : IsIso (derivedSourceComparison f g)) :
    Exact.IsMap (underivedBaseChange f g f' g' h_cart)
      (derivedBaseChange f g f' g' h_cart h_src) := sorry

end AlgebraicGeometry.Scheme.Hom

end

end
