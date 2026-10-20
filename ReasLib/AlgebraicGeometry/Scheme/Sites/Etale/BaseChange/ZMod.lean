/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ZMod
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.Adjunction.Derived
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Pullback of small-étale `ZMod n`-module sheaves along a composite is the composite pullback. -/
noncomputable def zmodSheafPullback_comp {A B C : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (n : ℕ)
    [HasSheafify A.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify B.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify C.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [((smallEtalePullback p).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        A.smallEtaleTopology B.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback q).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        B.smallEtaleTopology C.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (q ≫ p)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        A.smallEtaleTopology C.smallEtaleTopology).IsRightAdjoint] :
    zmodSheafPullback p n ⋙ zmodSheafPullback q n ≅
      zmodSheafPullback (q ≫ p) n :=
  let siteIso :
      smallEtalePullback p ⋙ smallEtalePullback q ≅ smallEtalePullback (q ≫ p) :=
    (MorphismProperty.Over.pullbackComp q p).symm
  Adjunction.leftAdjointCompIso
    (zmodSheafAdjunction p n) (zmodSheafAdjunction q n)
    (zmodSheafAdjunction (q ≫ p) n)
    (Functor.sheafPushforwardContinuousComp' siteIso (ModuleCat.{u} (ZMod n))
      A.smallEtaleTopology B.smallEtaleTopology C.smallEtaleTopology)

/-- Inverse-image identification along equal morphisms, by substitution of the morphism equality. -/
noncomputable def zmodSheafPullback_congr {A B : Scheme.{u}} {p q : A ⟶ B}
    (h : p = q) (n : ℕ)
    [HasSheafify A.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify B.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [((smallEtalePullback p).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback q).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint] :
    zmodSheafPullback p n ≅ zmodSheafPullback q n :=
  eqToIso (congrArg (fun r : A ⟶ B ↦ zmodSheafPullback r n) h)

/-- The left-adjoint square of étale `ZMod n` inverse images of a cartesian square of schemes. -/
noncomputable def zmodSheafPullback_square
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (n : ℕ)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology Y'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback f').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y'.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        X.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (f' ≫ g)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (g' ≫ f)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint] :
    zmodSheafPullback g n ⋙ zmodSheafPullback f' n ≅
      zmodSheafPullback f n ⋙ zmodSheafPullback g' n :=
  zmodSheafPullback_comp g f' n ≪≫
    zmodSheafPullback_congr h_cart.w.symm n ≪≫
    (zmodSheafPullback_comp f g' n).symm

/-- `zmodSheafPullback_square` is the composite of the two path identifications. -/
theorem zmodSheafPullback_square_eq
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (n : ℕ)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology Y'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback f').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y'.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        X.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (f' ≫ g)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (g' ≫ f)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint] :
    zmodSheafPullback_square f g f' g' h_cart n =
      zmodSheafPullback_comp g f' n ≪≫
        zmodSheafPullback_congr h_cart.w.symm n ≪≫
        (zmodSheafPullback_comp f g' n).symm := rfl

/-- Bundled exact-functor form of the inverse-image square of a cartesian scheme square. -/
noncomputable def zmodPullbackExact_square
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (n : ℕ)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology Y'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback f').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y'.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        X.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (f' ≫ g)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (g' ≫ f)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint] :
    (zmodPullbackExact g n).comp (zmodPullbackExact f' n) ≅
      (zmodPullbackExact f n).comp (zmodPullbackExact g' n) :=
  (exactFunctor
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))
      (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))).isoMk
    (zmodSheafPullback_square f g f' g' h_cart n)

/-- Derived inverse-image square `g⁻¹ ⋙ (f')⁻¹ ≅ f⁻¹ ⋙ (g')⁻¹` on `D(-_étale, ZMod n)`. -/
noncomputable def zmodDerivedPullbackSquare
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (n : ℕ)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology Y'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback f').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y'.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        X.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (f' ≫ g)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (g' ≫ f)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint] :
    zmodDerivedInverseImage g n ⋙ zmodDerivedInverseImage f' n ≅
      zmodDerivedInverseImage f n ⋙ zmodDerivedInverseImage g' n :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (zmodPullbackExact g n) (zmodPullbackExact f' n)).symm ≪≫
    ExactFunctor.MapDerivedCategory.mapIso
      (zmodPullbackExact_square f g f' g' h_cart n) ≪≫
    ExactFunctor.MapDerivedCategory.compFunctorIso
      (zmodPullbackExact f n) (zmodPullbackExact g' n)

/-- `zmodDerivedPullbackSquare` is the derived image of the underived inverse-image square. -/
theorem zmodDerivedPullbackSquare_eq
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (n : ℕ)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology Y'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback f').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y'.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        X.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (f' ≫ g)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (g' ≫ f)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint] :
    zmodDerivedPullbackSquare f g f' g' h_cart n =
      (ExactFunctor.MapDerivedCategory.compFunctorIso
          (zmodPullbackExact g n) (zmodPullbackExact f' n)).symm ≪≫
        ExactFunctor.MapDerivedCategory.mapIso
          (zmodPullbackExact_square f g f' g' h_cart n) ≪≫
        ExactFunctor.MapDerivedCategory.compFunctorIso
          (zmodPullbackExact f n) (zmodPullbackExact g' n) := rfl

/-- Derived base-change transformation `g⁻¹ Rf_* ⟶ Rf'_* (g')⁻¹` on `D(-_étale, ZMod n)`. -/
noncomputable def zmodDerivedBaseChange
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (n : ℕ)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [IsGrothendieckAbelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [IsGrothendieckAbelian (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology Y'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback f').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y'.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        X.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (f' ≫ g)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (g' ≫ f)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint] :
    zmodDerivedPushforward f n ⋙ zmodDerivedInverseImage g n ⟶
      zmodDerivedInverseImage g' n ⋙ zmodDerivedPushforward f' n :=
  DerivedBaseChange.map
    (KInjective.adjunction (zmodPullbackExact f n)
      (zmodSheafPushforward f n) (zmodSheafAdjunction f n))
    (KInjective.adjunction (zmodPullbackExact f' n)
      (zmodSheafPushforward f' n) (zmodSheafAdjunction f' n))
    (zmodDerivedPullbackSquare f g f' g' h_cart n)

/-- `zmodDerivedBaseChange` is `DerivedBaseChange.map` of the two K-injective adjunctions. -/
theorem zmodDerivedBaseChange_eq
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (n : ℕ)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [IsGrothendieckAbelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [IsGrothendieckAbelian (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology Y'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback f').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y'.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        X.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (f' ≫ g)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (g' ≫ f)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint] :
    zmodDerivedBaseChange f g f' g' h_cart n =
      DerivedBaseChange.map
        (KInjective.adjunction (zmodPullbackExact f n)
          (zmodSheafPushforward f n) (zmodSheafAdjunction f n))
        (KInjective.adjunction (zmodPullbackExact f' n)
          (zmodSheafPushforward f' n) (zmodSheafAdjunction f' n))
        (zmodDerivedPullbackSquare f g f' g' h_cart n) := rfl

/-- Component `g⁻¹ Rf_* E ⟶ Rf'_* (g')⁻¹ E` of the derived étale `ZMod n` base-change map. -/
noncomputable def zmodDerivedBaseChangeHom
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (n : ℕ)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [IsGrothendieckAbelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [IsGrothendieckAbelian (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology Y'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback f').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y'.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        X.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (f' ≫ g)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (g' ≫ f)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    (zmodDerivedInverseImage g n).obj ((zmodDerivedPushforward f n).obj E) ⟶
      (zmodDerivedPushforward f' n).obj ((zmodDerivedInverseImage g' n).obj E) :=
  (zmodDerivedBaseChange f g f' g' h_cart n).app E

/-- `zmodDerivedBaseChangeHom` is the component of `zmodDerivedBaseChange`. -/
theorem zmodDerivedBaseChangeHom_eq
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (n : ℕ)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [IsGrothendieckAbelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [IsGrothendieckAbelian (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology Y'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback f').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y'.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        X.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (f' ≫ g)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (g' ≫ f)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    zmodDerivedBaseChangeHom f g f' g' h_cart n E =
      (zmodDerivedBaseChange f g f' g' h_cart n).app E := rfl

/-- The named component satisfies the `DerivedBaseChange.IsMapAt` mate equation. -/
theorem zmodDerivedBaseChangeHom_isMapAt
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (n : ℕ)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [IsGrothendieckAbelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [IsGrothendieckAbelian (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology Y'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback f').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y'.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        X.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (f' ≫ g)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (g' ≫ f)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    DerivedBaseChange.IsMapAt
      (KInjective.adjunction (zmodPullbackExact f n)
        (zmodSheafPushforward f n) (zmodSheafAdjunction f n))
      (KInjective.adjunction (zmodPullbackExact f' n)
        (zmodSheafPushforward f' n) (zmodSheafAdjunction f' n))
      (zmodDerivedPullbackSquare f g f' g' h_cart n) E
      (zmodDerivedBaseChangeHom f g f' g' h_cart n E) := by
  exact DerivedBaseChange.map_isMapAt
    (KInjective.adjunction (zmodPullbackExact f n)
      (zmodSheafPushforward f n) (zmodSheafAdjunction f n))
    (KInjective.adjunction (zmodPullbackExact f' n)
      (zmodSheafPushforward f' n) (zmodSheafAdjunction f' n))
    (zmodDerivedPullbackSquare f g f' g' h_cart n) E

/-- For a proper morphism of schemes and a cartesian base change, the canonical base-change
map on unbounded derived categories of small-étale `ZMod n`-module sheaves is an isomorphism
for every nonzero natural modulus `n`. -/
instance zmodDerivedBaseChangeHom_isIso_of_isProper
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (n : ℕ) [NeZero n]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    IsIso (zmodDerivedBaseChangeHom f g f' g' h_cart n E) := sorry

/-- The canonical base-change map for the chosen fibre product of a proper scheme morphism
is an isomorphism on unbounded derived categories of small-étale `ZMod n`-module sheaves
for every nonzero natural modulus `n`. -/
theorem zmodDerivedBaseChangeHom_isIso_of_isProper_pullback
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y)
    [HasPullback g f] (n : ℕ) [NeZero n]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf (pullback g f).smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    IsIso
      (zmodDerivedBaseChangeHom f g (pullback.fst g f) (pullback.snd g f)
        (IsPullback.of_hasPullback g f).flip n E) := by
  exact zmodDerivedBaseChangeHom_isIso_of_isProper f g
    (pullback.fst g f) (pullback.snd g f)
    (IsPullback.of_hasPullback g f).flip n E

end AlgebraicGeometry.Scheme.Etale

end

end
