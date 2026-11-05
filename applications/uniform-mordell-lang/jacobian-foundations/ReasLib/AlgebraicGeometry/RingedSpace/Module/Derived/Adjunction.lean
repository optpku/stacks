module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom

/-!
# Derived pullback-pushforward adjunctions on ringed spaces

This module specializes the general ringed-site derived adjunction to the ringed sites of open
subsets of ringed spaces.
-/

open AlgebraicGeometry
open ComplexShape
open CategoryTheory
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y : RingedSpace.{u}}
variable (f : X ⟶ Y)
variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [CategoryWithHomology (RingedSpace.Modules Y)]
variable [(pushforward f).Additive]
variable [(pullback f).Additive]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
/-- The two absolute-derived conditions for module pullback and pushforward on a ringed
space, with the canonical existence of total right-derived pushforward supplied. -/
abbrev DerivedAdjunction.HasPair : Prop :=
  @RingedSite.Hom.DerivedAdjunction.HasPair _ _ (opensRingedSiteHom f)
    _ _ _ (opensRingedSiteHom.DerivedPushforward.hasDerived f) _

variable [DerivedAdjunction.HasPair f]

/-- The canonical derived adjunction `L(f)^* ⊣ R(f)_*` on module sheaves over a ringed space. -/
noncomputable abbrev modulePullbackDerivedPushforwardAdjunction :
    L(f)^* ⊣ R(f)_* :=
  @RingedSite.Hom.moduleDerivedAdjunction _ _ (opensRingedSiteHom f)
    _ _ _ (opensRingedSiteHom.DerivedPushforward.hasDerived f) _ inferInstance

/-- The derived pullback `L(f)^*` is left adjoint to the derived pushforward `R(f)_*`. -/
@[stacks 079W]
theorem modulePullbackDerivedPushforward_isAdjoint :
    Functor.IsLeftAdjoint (L(f)^*) ∧ Functor.IsRightAdjoint (R(f)_*) := sorry

/-- Derived pullback along a morphism of ringed spaces is a left adjoint. -/
@[stacks 079W]
instance modulePullbackDerived_isLeftAdjoint :
    (L(f)^*).IsLeftAdjoint := sorry

/-- Derived pushforward along a morphism of ringed spaces is a right adjoint. -/
instance modulePushforwardDerived_isRightAdjoint :
    (R(f)_*).IsRightAdjoint := sorry

end

end AlgebraicGeometry.RingedSpace
