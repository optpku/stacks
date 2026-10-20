/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Composition
public import stacks_project.Chap84.Lemma_84_7_1_Carrier
public import stacks_project.Chap84.Lemma_84_7_1_Ringed

/-!
# Canonical derived units along `ε_X` and `a_X`

A quasi-coherent module `F` on an algebraic space, after the carrier lift to
`ModuleCat.{u + 1}`, has canonical maps `π_X^* F ⟶ Rε_{X,*}(a_X^* F)` and
`F ⟶ Ra_{X,*}(a_X^* F)` in the unbounded derived category of modules. These
are the degree-zero adjunction units, transported through `modulePullbackCompIso`
and composed with the total right-derived unit of module pushforward.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale
open AlgebraicGeometry.AlgebraicSpace.Fppf
open RingedSite
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AssociatedModule

/-- A module sheaf placed in degree zero in the homotopy category. -/
def degreeZero.{uX, vX, w, z} (X : RingedSite.{uX, vX, w})
    (F : ModuleCat.{z} X) [UnivLE.{max uX vX, z}] :
    ModuleHomotopy.{z} X :=
  (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)

/-- `degreeZero` is the homotopy class of the cochain complex concentrated in
degree 0. -/
theorem degreeZero_eq.{uX, vX, w, z} (X : RingedSite.{uX, vX, w})
    (F : ModuleCat.{z} X) [UnivLE.{max uX vX, z}] :
    degreeZero X F =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F) :=
  sorry

/-- The specified comparison between pushforward and degree-zero inclusion. -/
def pushforwardSingleIso.{uX, vX, uY, vY, w, z}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : RingedSite.Hom X Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    (F : ModuleCat.{z} X) :
    ((modulePushforward.{z} f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        (degreeZero X F) ≅
      degreeZero Y ((modulePushforward.{z} f).obj F) :=
  ((modulePushforward.{z} f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F) ≪≫
    (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
          (modulePushforward.{z} f) (ComplexShape.up ℤ) 0).app F)

/-- A sheaf comparison mapped to degree zero, followed by the total right-derived
unit. -/
def ordinaryToRightDerived.{uX, vX, uY, vY, w, z}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : RingedSite.Hom X Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} f)
      (ModuleQis.{z} X)]
    (F : ModuleCat.{z} X) (G : ModuleCat.{z} Y)
    (h : G ⟶ (modulePushforward.{z} f).obj F) :
    (moduleLocalization.{z} Y).obj (degreeZero Y G) ⟶
      (modulePushforwardDerived.{z} f).obj
        ((moduleLocalization.{z} X).obj (degreeZero X F)) :=
  (moduleLocalization.{z} Y).map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map h)) ≫
    (moduleLocalization.{z} Y).map (pushforwardSingleIso f F).inv ≫
      ((modulePushforwardToDerived.{z} f).totalRightDerivedUnit
        (moduleLocalization.{z} X) (ModuleQis.{z} X)).app (degreeZero X F)

/-- `ordinaryToRightDerived` localizes the degree-zero map and composes with the
total right-derived unit. -/
theorem ordinaryToRightDerived_eq.{uX, vX, uY, vY, w, z}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : RingedSite.Hom X Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} f)
      (ModuleQis.{z} X)]
    (F : ModuleCat.{z} X) (G : ModuleCat.{z} Y)
    (h : G ⟶ (modulePushforward.{z} f).obj F) :
    ordinaryToRightDerived f F G h =
      (moduleLocalization.{z} Y).map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map h)) ≫
        (moduleLocalization.{z} Y).map (pushforwardSingleIso f F).inv ≫
          ((modulePushforwardToDerived.{z} f).totalRightDerivedUnit
            (moduleLocalization.{z} X) (ModuleQis.{z} X)).app
            (degreeZero X F) :=
  sorry

variable {S : Scheme.{u}}

/-- Grothendieck-abelian module sheaves on `((Spaces/X)_fppf, 𝒪)` give the
canonical total right-derived functor of `ε_{X,*}`. -/
instance epsilon_modulePushforwardDerived_hasRightDerived (X : AlgebraicSpace S)
    [IsGrothendieckAbelian (ModuleCat.{u + 1} (overFppfRingedSite X))] :
    Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u + 1} (epsilonRingedHom X))
      (ModuleQis.{u + 1} (overFppfRingedSite X)) :=
  sorry

/-- Grothendieck-abelian module sheaves on `((Spaces/X)_fppf, 𝒪)` give the
canonical total right-derived functor of `a_{X,*}`. -/
instance a_modulePushforwardDerived_hasRightDerived (X : AlgebraicSpace S)
    [IsGrothendieckAbelian (ModuleCat.{u + 1} (overFppfRingedSite X))] :
    Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u + 1} (aRingedHom X))
      (ModuleQis.{u + 1} (overFppfRingedSite X)) :=
  sorry

/-- The underived adjunction unit `π_X^* F ⟶ ε_{X,*}(a_X^* F)`, after the
carrier lift and the identification `a_X^* ≅ ε_X^* ∘ π_X^*`. -/
def epsilonOrdinaryUnit {X : AlgebraicSpace S} (F : X.Modules)
    [(etalePiRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [(epsilonRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [(aRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint] :
    (etalePiRingedHom X).modulePullback.{u + 1}.obj
        (moduleCarrierLift (ringedSite X) F) ⟶
      (epsilonRingedHom X).modulePushforward.{u + 1}.obj
        ((aRingedHom X).modulePullback.{u + 1}.obj
          (moduleCarrierLift (ringedSite X) F)) :=
  (modulePullbackPushforwardAdjunction.{u + 1} (epsilonRingedHom X)).unit.app
      ((etalePiRingedHom X).modulePullback.{u + 1}.obj
        (moduleCarrierLift (ringedSite X) F)) ≫
    (epsilonRingedHom X).modulePushforward.{u + 1}.map
      ((modulePullbackCompIso.{u + 1} (epsilonRingedHom X)
          (etalePiRingedHom X)).inv.app
        (moduleCarrierLift (ringedSite X) F))

/-- `epsilonOrdinaryUnit` is the `ε_X`-unit at `π_X^* F` followed by `ε_{X,*}` of
the inverse composition identification. -/
theorem epsilonOrdinaryUnit_eq {X : AlgebraicSpace S} (F : X.Modules)
    [(etalePiRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [(epsilonRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [(aRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint] :
    epsilonOrdinaryUnit F =
      (modulePullbackPushforwardAdjunction.{u + 1} (epsilonRingedHom X)).unit.app
          ((etalePiRingedHom X).modulePullback.{u + 1}.obj
            (moduleCarrierLift (ringedSite X) F)) ≫
        (epsilonRingedHom X).modulePushforward.{u + 1}.map
          ((modulePullbackCompIso.{u + 1} (epsilonRingedHom X)
              (etalePiRingedHom X)).inv.app
            (moduleCarrierLift (ringedSite X) F)) :=
  sorry

/-- The underived adjunction unit `F ⟶ a_{X,*}(a_X^* F)` after the carrier
lift. -/
def aOrdinaryUnit {X : AlgebraicSpace S} (F : X.Modules)
    [(aRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint] :
    moduleCarrierLift (ringedSite X) F ⟶
      (aRingedHom X).modulePushforward.{u + 1}.obj
        ((aRingedHom X).modulePullback.{u + 1}.obj
          (moduleCarrierLift (ringedSite X) F)) :=
  (modulePullbackPushforwardAdjunction.{u + 1} (aRingedHom X)).unit.app
    (moduleCarrierLift (ringedSite X) F)

/-- `aOrdinaryUnit` is the `a_X`-adjunction unit at the carrier lift of `F`. -/
theorem aOrdinaryUnit_eq {X : AlgebraicSpace S} (F : X.Modules)
    [(aRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint] :
    aOrdinaryUnit F =
      (modulePullbackPushforwardAdjunction.{u + 1} (aRingedHom X)).unit.app
        (moduleCarrierLift (ringedSite X) F) :=
  sorry

/-- The canonical map `π_X^* F ⟶ Rε_{X,*}(a_X^* F)` in the derived category,
after the carrier lift. -/
def piPullbackToEpsilonDerived {X : AlgebraicSpace S} (F : X.Modules)
    [(etalePiRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [(epsilonRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [(aRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u + 1} (epsilonRingedHom X))
      (ModuleQis.{u + 1} (overFppfRingedSite X))] :=
  ordinaryToRightDerived (epsilonRingedHom X)
    ((aRingedHom X).modulePullback.{u + 1}.obj
      (moduleCarrierLift (ringedSite X) F))
    ((etalePiRingedHom X).modulePullback.{u + 1}.obj
      (moduleCarrierLift (ringedSite X) F))
    (epsilonOrdinaryUnit F)

/-- The canonical map `F ⟶ Ra_{X,*}(a_X^* F)` in the derived category, after
the carrier lift. -/
def toADerived {X : AlgebraicSpace S} (F : X.Modules)
    [(aRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u + 1} (aRingedHom X))
      (ModuleQis.{u + 1} (overFppfRingedSite X))] :=
  ordinaryToRightDerived (aRingedHom X)
    ((aRingedHom X).modulePullback.{u + 1}.obj
      (moduleCarrierLift (ringedSite X) F))
    (moduleCarrierLift (ringedSite X) F)
    (aOrdinaryUnit F)

/-- For a quasi-coherent `𝒪_X`-module, `π_X^* F ⟶ Rε_{X,*}(a_X^* F)` is an
isomorphism. -/
theorem piPullbackToEpsilonDerived_isIso {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent]
    [(etalePiRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [(epsilonRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [(aRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u + 1} (epsilonRingedHom X))
      (ModuleQis.{u + 1} (overFppfRingedSite X))] :
    IsIso (piPullbackToEpsilonDerived F) :=
  sorry

/-- For a quasi-coherent `𝒪_X`-module, `F ⟶ Ra_{X,*}(a_X^* F)` is an
isomorphism. -/
theorem toADerived_isIso {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent]
    [(aRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u + 1} (aRingedHom X))
      (ModuleQis.{u + 1} (overFppfRingedSite X))] :
    IsIso (toADerived F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.AssociatedModule

end

end
