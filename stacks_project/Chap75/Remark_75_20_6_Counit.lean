/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Adjunction.InternalHom
public import ReasLib.CategoryTheory.Monoidal.Functor.TensorComparison
public import stacks_project.Chap75.Lemma_75_20_4_BaseChange

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.BaseChange.InternalHom.Counit

/-! # Compatibility checks for derived internal Hom and the counit square -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Hom
open CategoryTheory.Limits CategoryTheory.MonoidalClosed
open CategoryTheory.DerivedCategory CategoryTheory.Functor

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

#check (pushforwardDerived.compIso :
  ∀ {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z),
    moduleDerivedPushforward f ⋙ moduleDerivedPushforward g ≅ moduleDerivedPushforward (f ≫ g))

#check (pushforwardDerived.compIso_eq :
  ∀ {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z),
    pushforwardDerived.compIso f g =
      (((Modules.derivedPullbackPushforwardAdjunction g).comp
          (Modules.derivedPullbackPushforwardAdjunction f)).ofNatIsoLeft
            (ModuleDerived.totalPullbackCompIso f g)).rightAdjointUniq
        (Modules.derivedPullbackPushforwardAdjunction (f ≫ g)))

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.Hom.DerivedBaseChange.InternalHom

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
variable (g' : X' ⟶ X) {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
variable [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]

#check (pushforwardIso g' :
  ∀ (sq : CommSq g' f' f g),
    Modules.moduleDerivedPushforward g' ⋙ Modules.moduleDerivedPushforward f ≅
      Modules.moduleDerivedPushforward f' ⋙ Modules.moduleDerivedPushforward g)

#check (pushforwardIso_hom_app g' :
  ∀ (sq : CommSq g' f' f g)
    (K : ModuleDerived X'),
    (pushforwardIso g' sq).hom.app K =
      (Modules.pushforwardDerived.compIso g' f).hom.app K ≫
        eqToHom (congrArg
          (fun h : X' ⟶ Y ↦ (Modules.moduleDerivedPushforward h).obj K) sq.w) ≫
        (Modules.pushforwardDerived.compIso f' g).inv.app K)

#check (globalHomAdjunctionIso g' :
  ∀ (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (T_X : DerivedTensor.Right.Monoidal.Model (C := X.Modules))
    (T_X' : DerivedTensor.Right.Monoidal.Model (C := X'.Modules))
    (M : ModuleDerived X) (L : ModuleDerived X'),
    (Modules.moduleDerivedPushforward f).obj
        ((H_X.ihomOf M).obj ((Modules.moduleDerivedPushforward g').obj L)) ≅
      (Modules.moduleDerivedPushforward g).obj
        ((Modules.moduleDerivedPushforward f').obj
          ((H_X'.ihomOf ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)).obj L)))

#check (globalHomAdjunctionIso_hom g' :
  ∀ (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (T_X : DerivedTensor.Right.Monoidal.Model (C := X.Modules))
    (T_X' : DerivedTensor.Right.Monoidal.Model (C := X'.Modules))
    (M : ModuleDerived X) (L : ModuleDerived X'),
    (globalHomAdjunctionIso g' sq H_X H_X' T_X T_X' M L).hom =
      (Modules.moduleDerivedPushforward f).map
          (ModuleDerived.InternalHom.adjunctionComparisonIso g' H_X H_X' T_X T_X' M L).hom ≫
        (pushforwardIso g' sq).hom.app
          ((H_X'.ihomOf ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)).obj L))

#check (adjunctionCounitMap g' :
  ∀ (f' : X' ⟶ Y')
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (M : ModuleDerived X) (L : ModuleDerived X'),
    (Modules.moduleDerivedPushforward f').obj
        ((H_X'.ihomOf ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)).obj
          ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj
            ((Modules.moduleDerivedPushforward g').obj L))) ⟶
      (Modules.moduleDerivedPushforward f').obj
        ((H_X'.ihomOf ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)).obj L))

#check (adjunctionCounitMap_spec g' :
  ∀ (f' : X' ⟶ Y')
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (M : ModuleDerived X) (L : ModuleDerived X'),
    adjunctionCounitMap g' f' H_X' M L =
      (Modules.moduleDerivedPushforward f').map
        ((H_X'.ihomOf ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)).map
          ((Modules.derivedPullbackPushforwardAdjunction g').counit.app L)))

#check (multiplication g' :
  ∀ (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (T_X : DerivedTensor.Right.Monoidal.Model (C := X.Modules))
    (T_X' : DerivedTensor.Right.Monoidal.Model (C := X'.Modules))
    (M : ModuleDerived X) (L : ModuleDerived X'),
    (source f g).obj
        ((H_X.ihomOf M).obj ((Modules.moduleDerivedPushforward g').obj L)) ⟶
      (Modules.moduleDerivedPushforward f').obj
        ((H_X'.ihomOf ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)).obj L))

#check (multiplication_spec g' :
  ∀ (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (T_X : DerivedTensor.Right.Monoidal.Model (C := X.Modules))
    (T_X' : DerivedTensor.Right.Monoidal.Model (C := X'.Modules))
    (M : ModuleDerived X) (L : ModuleDerived X'),
    multiplication g' sq H_X H_X' T_X T_X' M L =
      (LeftDerived.Homotopy.functor (Modules.pullback g)).map
          (globalHomAdjunctionIso g' sq H_X H_X' T_X T_X' M L).hom ≫
        (Modules.derivedPullbackPushforwardAdjunction g).counit.app _)

end AlgebraicGeometry.AlgebraicSpace.Hom.DerivedBaseChange.InternalHom

namespace AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange.InternalHom

#check (map_counit_commSq :
  ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B)
    {X X' : AlgebraicSpace (Spec A)} (g' : X' ⟶ X)
    (f' : X' ⟶ ofOver (Over.mk (Spec.map φ)))
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec A))))
    [IsQuasiCompact X] [IsQuasiSeparated X]
    [IsQuasiCompact X'] [IsQuasiSeparated X']
    [QuasiCompact f] [QuasiSeparated f]
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]
    (sq : IsPullback g' f' f (Hom.specMap φ))
    (hTor : TorIndependentOver (Over.mk f) (Over.mk (Hom.specMap φ)))
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (T_X : DerivedTensor.Right.Monoidal.Model (C := X.Modules))
    (T_X' : DerivedTensor.Right.Monoidal.Model (C := X'.Modules))
    (M : ModuleDerived X) (L : ModuleDerived X'),
    CommSq
      (Hom.DerivedBaseChange.InternalHom.canonicalMap sq.toCommSq H_X H_X' T_X T_X' M
        ((Modules.moduleDerivedPushforward g').obj L))
      (Hom.DerivedBaseChange.InternalHom.multiplication g' sq.toCommSq H_X H_X' T_X T_X' M L)
      (Hom.DerivedBaseChange.InternalHom.adjunctionCounitMap g' f' H_X' M L)
      (𝟙 _))

end AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange.InternalHom
