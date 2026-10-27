/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Pullback.Universe
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Comparison
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Composition
public import ReasLib.AlgebraicGeometry.RingedSite.Module.UniverseLift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Ringed

/-!
# Derived étale–fppf comparison for modules on algebraic spaces

The canonical comparison maps are the degree-zero adjunction units followed by the
comparison from ordinary direct image to total right-derived direct image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale
open AlgebraicGeometry.AlgebraicSpace.Fppf
open RingedSite RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AssociatedModule

variable {S : Scheme.{u}}

/-- Grothendieck-abelian module sheaves on `((Spaces/X)_fppf, 𝒪)` give the
canonical total right-derived functor of `ε_{X,*}`. -/
instance epsilon_modulePushforwardDerived_hasRightDerived (X : AlgebraicSpace S) :
    Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u + 1} (epsilonRingedHom X))
      (ModuleQis.{u + 1} (overFppfRingedSite X)) :=
  modulePushforwardToDerived.hasRightDerived.{u + 1} (epsilonRingedHom X)

/-- Grothendieck-abelian module sheaves on `((Spaces/X)_fppf, 𝒪)` give the
canonical total right-derived functor of `a_{X,*}`. -/
instance a_modulePushforwardDerived_hasRightDerived (X : AlgebraicSpace S) :
    Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u + 1} (aRingedHom X))
      (ModuleQis.{u + 1} (overFppfRingedSite X)) :=
  modulePushforwardToDerived.hasRightDerived.{u + 1} (aRingedHom X)

/-- The underived adjunction unit `π_X^* F ⟶ ε_{X,*}(a_X^* F)`, after the
carrier lift and the identification `a_X^* ≅ ε_X^* ∘ π_X^*`. -/
def epsilonOrdinaryUnit {X : AlgebraicSpace S} (F : X.Modules) :
    (Etale.Atlas.etalePiRingedHom X).modulePullback.{u + 1}.obj
        (RingedSite.Module.carrierLift (ringedSite X) F) ⟶
      (epsilonRingedHom X).modulePushforward.{u + 1}.obj
        ((aRingedHom X).modulePullback.{u + 1}.obj
          (RingedSite.Module.carrierLift (ringedSite X) F)) :=
  (modulePullbackPushforwardAdjunction.{u + 1} (epsilonRingedHom X)).unit.app
      ((Etale.Atlas.etalePiRingedHom X).modulePullback.{u + 1}.obj
        (RingedSite.Module.carrierLift (ringedSite X) F)) ≫
    (epsilonRingedHom X).modulePushforward.{u + 1}.map
      ((modulePullbackCompIso.{u + 1} (epsilonRingedHom X)
          (Etale.Atlas.etalePiRingedHom X)).inv.app
        (RingedSite.Module.carrierLift (ringedSite X) F))

/-- `epsilonOrdinaryUnit` is the `ε_X`-unit at `π_X^* F` followed by `ε_{X,*}` of
the inverse composition identification. -/
theorem epsilonOrdinaryUnit_eq {X : AlgebraicSpace S} (F : X.Modules) :
    epsilonOrdinaryUnit F =
      (modulePullbackPushforwardAdjunction.{u + 1} (epsilonRingedHom X)).unit.app
          ((Etale.Atlas.etalePiRingedHom X).modulePullback.{u + 1}.obj
            (RingedSite.Module.carrierLift (ringedSite X) F)) ≫
        (epsilonRingedHom X).modulePushforward.{u + 1}.map
          ((modulePullbackCompIso.{u + 1} (epsilonRingedHom X)
              (Etale.Atlas.etalePiRingedHom X)).inv.app
            (RingedSite.Module.carrierLift (ringedSite X) F)) :=
  rfl

/-- The underived adjunction unit `F ⟶ a_{X,*}(a_X^* F)` after the carrier
lift. -/
def aOrdinaryUnit {X : AlgebraicSpace S} (F : X.Modules) :
    RingedSite.Module.carrierLift (ringedSite X) F ⟶
      (aRingedHom X).modulePushforward.{u + 1}.obj
        ((aRingedHom X).modulePullback.{u + 1}.obj
          (RingedSite.Module.carrierLift (ringedSite X) F)) :=
  (modulePullbackPushforwardAdjunction.{u + 1} (aRingedHom X)).unit.app
    (RingedSite.Module.carrierLift (ringedSite X) F)

/-- `aOrdinaryUnit` is the `a_X`-adjunction unit at the carrier lift of `F`. -/
theorem aOrdinaryUnit_eq {X : AlgebraicSpace S} (F : X.Modules) :
    aOrdinaryUnit F =
      (modulePullbackPushforwardAdjunction.{u + 1} (aRingedHom X)).unit.app
        (RingedSite.Module.carrierLift (ringedSite X) F) :=
  rfl

/-- The canonical map `π_X^* F ⟶ Rε_{X,*}(a_X^* F)` in the derived category,
after the carrier lift. -/
def piPullbackToEpsilonDerived {X : AlgebraicSpace S} (F : X.Modules) :=
  ordinaryToRightDerived (epsilonRingedHom X)
    ((aRingedHom X).modulePullback.{u + 1}.obj
      (RingedSite.Module.carrierLift (ringedSite X) F))
    ((Etale.Atlas.etalePiRingedHom X).modulePullback.{u + 1}.obj
      (RingedSite.Module.carrierLift (ringedSite X) F))
    (epsilonOrdinaryUnit F)

/-- The canonical map `F ⟶ Ra_{X,*}(a_X^* F)` in the derived category, after
the carrier lift. -/
def toADerived {X : AlgebraicSpace S} (F : X.Modules) :=
  ordinaryToRightDerived (aRingedHom X)
    ((aRingedHom X).modulePullback.{u + 1}.obj
      (RingedSite.Module.carrierLift (ringedSite X) F))
    (RingedSite.Module.carrierLift (ringedSite X) F)
    (aOrdinaryUnit F)

/-- For a quasi-coherent `𝒪_X`-module, `π_X^* F ⟶ Rε_{X,*}(a_X^* F)` is an
isomorphism. -/
instance piPullbackToEpsilonDerived_isIso {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent] :
    IsIso (piPullbackToEpsilonDerived F) :=
  sorry

/-- For a quasi-coherent `𝒪_X`-module, `F ⟶ Ra_{X,*}(a_X^* F)` is an
isomorphism. -/
instance toADerived_isIso {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent] :
    IsIso (toADerived F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.AssociatedModule

end

end
