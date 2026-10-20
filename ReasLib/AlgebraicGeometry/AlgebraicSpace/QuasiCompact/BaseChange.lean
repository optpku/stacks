/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact

/-!
# Base change of quasi-compact morphisms of algebraic spaces

Quasi-compact morphisms of algebraic spaces are stable under arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Quasi-compact morphisms of algebraic spaces are stable under arbitrary base change. -/
instance quasiCompact_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@QuasiCompact S : MorphismProperty (AlgebraicSpace S)) := sorry

namespace QuasiCompact

/-- In a pullback square, the base change of a quasi-compact morphism of algebraic
spaces is quasi-compact. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : QuasiCompact g) : QuasiCompact g' := sorry

/-- The base-change projection `pullback.snd f g` of a quasi-compact morphism
`f : X ⟶ Y` is quasi-compact. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : QuasiCompact f) (g : Z ⟶ Y) [HasPullback f g] :
    QuasiCompact (pullback.snd f g) := sorry

end QuasiCompact

/-- The second projection from a pullback of a quasi-compact morphism is quasi-compact. -/
instance quasiCompact_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [QuasiCompact f] [HasPullback f g] :
    QuasiCompact (pullback.snd f g) := sorry

end AlgebraicGeometry.AlgebraicSpace
