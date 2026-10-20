/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeRegularImmersion

/-!
# Relative regular immersions under base change

Arbitrary base change preserves relative `H_1`-regular and quasi-regular immersions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RelativeH1RegularImmersion

/-- An immersion that is relatively `H_1`-regular over a base remains `H_1`-regular after
arbitrary base change. -/
@[stacks 063R, instance]
theorem h1RegularImmersion_pullback_snd
    {X S S' Z : Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}
    [RelativeH1RegularImmersion f i] (g : S' ⟶ S) :
    IsH1RegularImmersion (pullback.snd i (pullback.fst f g)) := sorry

end AlgebraicGeometry.RelativeH1RegularImmersion

namespace AlgebraicGeometry.RelativeQuasiRegularImmersion

/-- An immersion that is relatively quasi-regular over a base remains quasi-regular after
arbitrary base change. -/
@[stacks 063R, instance]
theorem quasiRegularImmersion_pullback_snd
    {X S S' Z : Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}
    [RelativeQuasiRegularImmersion f i] (g : S' ⟶ S) :
    IsQuasiRegularImmersion (pullback.snd i (pullback.fst f g)) := sorry

end AlgebraicGeometry.RelativeQuasiRegularImmersion
