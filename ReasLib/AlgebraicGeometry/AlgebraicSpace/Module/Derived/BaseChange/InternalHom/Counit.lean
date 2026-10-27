/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.BaseChange.InternalHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.AffineSpectrum

/-! # Derived internal Hom and the base-change counit square -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Hom
open CategoryTheory.Limits CategoryTheory.MonoidalClosed
open CategoryTheory.DerivedCategory CategoryTheory.Functor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.DerivedBaseChange.InternalHom

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
variable (g' : X' ⟶ X) {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
variable [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]

/-- The canonical identification of the two iterated derived pushforwards associated to a
commutative square of algebraic spaces. -/
noncomputable def pushforwardIso (sq : CommSq g' f' f g) :
    Modules.moduleDerivedPushforward g' ⋙ Modules.moduleDerivedPushforward f ≅
      Modules.moduleDerivedPushforward f' ⋙ Modules.moduleDerivedPushforward g :=
  Modules.pushforwardDerived.compIso g' f ≪≫
    eqToIso (congrArg (fun h : X' ⟶ Y ↦ Modules.moduleDerivedPushforward h) sq.w) ≪≫
    (Modules.pushforwardDerived.compIso f' g).symm

/-- The forward component of `pushforwardIso` is the two composition isomorphisms with the
commutative-square transport between them. -/
theorem pushforwardIso_hom_app (sq : CommSq g' f' f g)
    (K : ModuleDerived X') :
    (pushforwardIso g' sq).hom.app K =
      (Modules.pushforwardDerived.compIso g' f).hom.app K ≫
        eqToHom (congrArg
          (fun h : X' ⟶ Y ↦ (Modules.moduleDerivedPushforward h).obj K) sq.w) ≫
        (Modules.pushforwardDerived.compIso f' g).inv.app K :=
  sorry

/-- The global internal-Hom adjunction isomorphism, transported across the two canonical
derived-pushforward composition isomorphisms of a commutative algebraic-space square. -/
noncomputable def globalHomAdjunctionIso (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (T_X : DerivedTensor.Right.Monoidal.Model (C := X.Modules))
    (T_X' : DerivedTensor.Right.Monoidal.Model (C := X'.Modules))
    (M : ModuleDerived X) (L : ModuleDerived X') :
    (Modules.moduleDerivedPushforward f).obj
        ((H_X.ihomOf M).obj ((Modules.moduleDerivedPushforward g').obj L)) ≅
      (Modules.moduleDerivedPushforward g).obj
        ((Modules.moduleDerivedPushforward f').obj
          ((H_X'.ihomOf ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)).obj L)) :=
  (Modules.moduleDerivedPushforward f).mapIso
      (ModuleDerived.InternalHom.adjunctionComparisonIso g' H_X H_X' T_X T_X' M L) ≪≫
    (pushforwardIso g' sq).app
      ((H_X'.ihomOf ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)).obj L)

/-- The forward map of `globalHomAdjunctionIso` is pushforward of the internal-Hom
comparison followed by the pushforward-composition transport. -/
theorem globalHomAdjunctionIso_hom (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (T_X : DerivedTensor.Right.Monoidal.Model (C := X.Modules))
    (T_X' : DerivedTensor.Right.Monoidal.Model (C := X'.Modules))
    (M : ModuleDerived X) (L : ModuleDerived X') :
    (globalHomAdjunctionIso g' sq H_X H_X' T_X T_X' M L).hom =
      (Modules.moduleDerivedPushforward f).map
          (ModuleDerived.InternalHom.adjunctionComparisonIso g' H_X H_X' T_X T_X' M L).hom ≫
        (pushforwardIso g' sq).hom.app
          ((H_X'.ihomOf ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)).obj L) :=
  sorry

/-- The right edge obtained by applying internal Hom to the counit
`L(g')^* R(g')_* L ⟶ L` and then applying derived pushforward along `f'`. -/
noncomputable def adjunctionCounitMap (f' : X' ⟶ Y')
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (M : ModuleDerived X) (L : ModuleDerived X') :
    (Modules.moduleDerivedPushforward f').obj
        ((H_X'.ihomOf ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)).obj
          ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj
            ((Modules.moduleDerivedPushforward g').obj L))) ⟶
      (Modules.moduleDerivedPushforward f').obj
        ((H_X'.ihomOf ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)).obj L) :=
  (Modules.moduleDerivedPushforward f').map
    ((H_X'.ihomOf ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)).map
      ((Modules.derivedPullbackPushforwardAdjunction g').counit.app L))

/-- The counit edge is derived pushforward of internal Hom applied to the
pullback-pushforward counit. -/
theorem adjunctionCounitMap_spec (f' : X' ⟶ Y')
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (M : ModuleDerived X) (L : ModuleDerived X') :
    adjunctionCounitMap g' f' H_X' M L =
      (Modules.moduleDerivedPushforward f').map
        ((H_X'.ihomOf ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)).map
          ((Modules.derivedPullbackPushforwardAdjunction g').counit.app L)) :=
  sorry

/-- Multiplication on global derived Hom first uses the global internal-Hom adjunction
isomorphism and then applies the counit `L(g)^* R(g)_* K' ⟶ K'`. -/
noncomputable def multiplication (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (T_X : DerivedTensor.Right.Monoidal.Model (C := X.Modules))
    (T_X' : DerivedTensor.Right.Monoidal.Model (C := X'.Modules))
    (M : ModuleDerived X) (L : ModuleDerived X') :
    (source f g).obj
        ((H_X.ihomOf M).obj ((Modules.moduleDerivedPushforward g').obj L)) ⟶
      (Modules.moduleDerivedPushforward f').obj
        ((H_X'.ihomOf ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)).obj L) :=
  (LeftDerived.Homotopy.functor (Modules.pullback g)).map
      (globalHomAdjunctionIso g' sq H_X H_X' T_X T_X' M L).hom ≫
    (Modules.derivedPullbackPushforwardAdjunction g).counit.app _

/-- Multiplication factors through pullback of the global internal-Hom adjunction isomorphism
and ends in the canonical derived pullback-pushforward counit. -/
theorem multiplication_spec (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (T_X : DerivedTensor.Right.Monoidal.Model (C := X.Modules))
    (T_X' : DerivedTensor.Right.Monoidal.Model (C := X'.Modules))
    (M : ModuleDerived X) (L : ModuleDerived X') :
    multiplication g' sq H_X H_X' T_X T_X' M L =
      (LeftDerived.Homotopy.functor (Modules.pullback g)).map
          (globalHomAdjunctionIso g' sq H_X H_X' T_X T_X' M L).hom ≫
        (Modules.derivedPullbackPushforwardAdjunction g).counit.app _ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.DerivedBaseChange.InternalHom

namespace AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange.InternalHom

/-- For an affine Tor-independent cartesian square of qcqs algebraic spaces, the derived
internal-Hom base-change map commutes with multiplication and the morphism induced by the
pullback-pushforward counit. -/
theorem map_counit_commSq {A B : CommRingCat.{u}} (φ : A ⟶ B)
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
    (M : ModuleDerived X) (L : ModuleDerived X') :
    CommSq
      (Hom.DerivedBaseChange.InternalHom.canonicalMap sq.toCommSq H_X H_X' T_X T_X' M
        ((Modules.moduleDerivedPushforward g').obj L))
      (Hom.DerivedBaseChange.InternalHom.multiplication g' sq.toCommSq H_X H_X' T_X T_X' M L)
      (Hom.DerivedBaseChange.InternalHom.adjunctionCounitMap g' f' H_X' M L)
      (𝟙 _) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange.InternalHom
