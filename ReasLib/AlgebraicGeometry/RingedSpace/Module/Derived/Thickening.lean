/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Exact

/-!
# Derived pushforward along thickenings of ringed spaces

Pushforward along a thickening is exact. Its localization on derived categories is therefore
canonically isomorphic to total right-derived pushforward, giving explicit shift comparisons.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.ThickeningDerived

variable {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsThickening i]

/-- Module pushforward along a thickening preserves finite limits. -/
theorem pushforward_preservesFiniteLimits : PreservesFiniteLimits (Hom.pushforward i) :=
  (ModulePushforward.ClosedImmersion.exact i
    (IsThickening.isHomeomorph_base i).isClosedEmbedding).1

/-- Module pushforward along a thickening preserves finite colimits. -/
theorem pushforward_preservesFiniteColimits : PreservesFiniteColimits (Hom.pushforward i) :=
  (ModulePushforward.ClosedImmersion.exact i
    (IsThickening.isHomeomorph_base i).isClosedEmbedding).2

/-- The exact functor underlying pushforward along a thickening. -/
noncomputable def exactPushforward : X.Modules ⥤ₑ X'.Modules :=
  ⟨Hom.pushforward i, pushforward_preservesFiniteLimits i,
    pushforward_preservesFiniteColimits i⟩

/-- Exact-derived pushforward along a thickening is canonically isomorphic to total
right-derived pushforward. -/
noncomputable def pushforwardIso :
    @Functor.mapDerivedCategory X.Modules _ _ _ X'.Modules _ _ _
      (Hom.pushforward i) inferInstance (pushforward_preservesFiniteLimits i)
        (pushforward_preservesFiniteColimits i) ≅ R(i)_* :=
  @Functor.RightDerived.Exact.homotopyIso X.Modules _ _ X'.Modules _ _ _ _
    (Hom.pushforward i) inferInstance (pushforward_preservesFiniteLimits i)
      (pushforward_preservesFiniteColimits i)

/-- Total right-derived pushforward along a thickening commutes with every integer shift. -/
def shiftIso (n : ℤ) :
    shiftFunctor (DerivedCategory X.Modules) n ⋙ R(i)_* ≅
      R(i)_* ⋙ shiftFunctor (DerivedCategory X'.Modules) n :=
  Functor.isoWhiskerLeft (shiftFunctor (DerivedCategory X.Modules) n)
      (pushforwardIso i).symm ≪≫
    (@Functor.mapDerivedCategory X.Modules _ _ _ X'.Modules _ _ _
      (Hom.pushforward i) inferInstance (pushforward_preservesFiniteLimits i)
        (pushforward_preservesFiniteColimits i)).commShiftIso n ≪≫
      Functor.isoWhiskerRight (pushforwardIso i)
        (shiftFunctor (DerivedCategory X'.Modules) n)

/-- For a thickening, the canonical comparison from the single complex of a pushforward
module to its total right-derived pushforward is invertible. -/
theorem comparison_isIso (M : X.Modules) :
    IsIso (moduleDerivedPushforward.comparison i ((i _*).obj M) M (𝟙 _)) := sorry

end AlgebraicGeometry.RingedSpace.Hom.ThickeningDerived
