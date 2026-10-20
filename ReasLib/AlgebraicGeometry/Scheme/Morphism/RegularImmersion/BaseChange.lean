/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion

/-!
# Regular immersions under flat base change

Flat base change preserves the standard regularity conditions on immersions of schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X X' Z : Scheme.{u}} (i : Z ⟶ X) (f : X' ⟶ X)

/-- Flat base change of a regular immersion is a regular immersion. -/
@[stacks 067P, instance]
theorem isRegularImmersion_pullback_snd [IsRegularImmersion i] [Flat f] :
    IsRegularImmersion (pullback.snd i f) := sorry

/-- Flat base change of a Koszul-regular immersion is a Koszul-regular immersion. -/
@[stacks 067P, instance]
theorem isKoszulRegularImmersion_pullback_snd [IsKoszulRegularImmersion i] [Flat f] :
    IsKoszulRegularImmersion (pullback.snd i f) := sorry

/-- Flat base change of an `H_1`-regular immersion is an `H_1`-regular immersion. -/
@[stacks 067P, instance]
theorem isH1RegularImmersion_pullback_snd [IsH1RegularImmersion i] [Flat f] :
    IsH1RegularImmersion (pullback.snd i f) := sorry

/-- Flat base change of a quasi-regular immersion is a quasi-regular immersion. -/
@[stacks 067P, instance]
theorem isQuasiRegularImmersion_pullback_snd [IsQuasiRegularImmersion i] [Flat f] :
    IsQuasiRegularImmersion (pullback.snd i f) := sorry

end AlgebraicGeometry
