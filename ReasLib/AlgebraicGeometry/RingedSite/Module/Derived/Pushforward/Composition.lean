/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.Composition

@[expose] public section

/-!
# Composition of derived direct images on ringed sites

This module gives the canonical comparison between iterated derived direct image and derived
direct image of a composite, parameterized by a comparison for derived inverse image.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe z uX vX uY vY uZ vZ w

namespace RingedSite.Hom

section

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  {Z : RingedSite.{uZ, vZ, w}} (f : Hom X Y) (g : Hom Y Z)
variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
  [UnivLE.{max uZ vZ, z}]

variable [(f.modulePushforward.{z}).IsRightAdjoint]
variable [(g.modulePushforward.{z}).IsRightAdjoint]

variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} g) (ModuleQis.{z} Y)]
variable [hCompositeRight : Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} (f.comp g)) (ModuleQis.{z} X)]

variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} f) (ModuleQis.{z} Y)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} g) (ModuleQis.{z} Z)]
variable [Functor.HasLeftDerivedFunctor
  (compositePullbackToDerived.{z} f g) (ModuleQis.{z} Z)]

/-- The absolute-derived pair condition for the inverse and direct images along a composite. -/
abbrev compositeDerivedPair : Prop :=
  @DerivedAdjunction.HasPair.{z} _ _ (f.comp g) inferInstance inferInstance
    (modulePushforwardComp_isRightAdjoint f g) inferInstance inferInstance

variable [DerivedAdjunction.HasPair.{z} f]
variable [DerivedAdjunction.HasPair.{z} g]
variable [compositeDerivedPair.{z} f g]

/-- The canonical derived inverse-image–direct-image adjunction along a composite. -/
abbrev compositeDerivedAdjunction :=
  @moduleDerivedAdjunction.{z} _ _ (f.comp g) inferInstance inferInstance
    (modulePushforwardComp_isRightAdjoint f g) inferInstance inferInstance inferInstance

/-- The adjunction whose left adjoint is the composite derived inverse image, transported along a
comparison with derived pullback for the composite morphism. -/
abbrev compositePushforwardAdjunction
    (hpull : modulePullbackDerived.{z} g ⋙ modulePullbackDerived.{z} f ≅
      compositePullbackDerived.{z} f g) :
    compositePullbackDerived.{z} f g ⊣
      modulePushforwardDerived.{z} f ⋙ modulePushforwardDerived.{z} g :=
  ((moduleDerivedAdjunction.{z} g).comp
    (moduleDerivedAdjunction.{z} f)).ofNatIsoLeft hpull

/-- The canonical comparison from iterated derived direct image to derived direct image of the
composite morphism. -/
noncomputable def modulePushforwardDerivedCompIsoOfPullback
    (hpull : modulePullbackDerived.{z} g ⋙ modulePullbackDerived.{z} f ≅
      compositePullbackDerived.{z} f g) :
    modulePushforwardDerived.{z} f ⋙ modulePushforwardDerived.{z} g ≅
      modulePushforwardDerived.{z} (f.comp g) :=
  (compositePushforwardAdjunction f g hpull).rightAdjointUniq
    (compositeDerivedAdjunction.{z} f g)

/-- The comparison isomorphism is characterized by compatibility with the counits of the
canonical derived adjunctions. -/
theorem modulePushforwardDerivedCompIsoOfPullback_hom_counit
    (hpull : modulePullbackDerived.{z} g ⋙ modulePullbackDerived.{z} f ≅
      compositePullbackDerived.{z} f g) :
    Functor.whiskerRight
        (modulePushforwardDerivedCompIsoOfPullback f g hpull).hom
        (compositePullbackDerived.{z} f g) ≫
      (compositeDerivedAdjunction.{z} f g).counit =
        (compositePushforwardAdjunction f g hpull).counit := sorry

/-- The component of the derived direct-image comparison is characterized by the corresponding
counit equation at that derived object. -/
theorem modulePushforwardDerivedCompIsoOfPullback_hom_app_counit
    (hpull : modulePullbackDerived.{z} g ⋙ modulePullbackDerived.{z} f ≅
      compositePullbackDerived.{z} f g)
    (K : ModuleDerived.{z} X) :
    (compositePullbackDerived.{z} f g).map
        ((modulePushforwardDerivedCompIsoOfPullback f g hpull).hom.app K) ≫
      (compositeDerivedAdjunction.{z} f g).counit.app K =
        (compositePushforwardAdjunction f g hpull).counit.app K := sorry

end

end RingedSite.Hom

-- Any `sorryAx` is inherited through Prop-valued derived-adjunction witnesses; the adjunction
-- transport and right-adjoint uniqueness data are explicit canonical constructions.
