/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion

/-!
# Regularizing a Koszul-regular closed immersion

A Koszul-regular closed immersion becomes a regular immersion after a smooth surjective base
change.
-/

@[expose] public section

open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.IsKoszulRegularClosedImmersion

/-- A Koszul-regular closed immersion becomes regular after pullback along some smooth surjective
morphism. -/
theorem exists_smooth_surjective_regularImmersion_pullback
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsKoszulRegularClosedImmersion i] :
    ∃ (X' : Scheme.{u}) (f : X' ⟶ X),
      Surjective f ∧ Smooth f ∧ IsRegularImmersion (pullback.snd i f) := sorry

end AlgebraicGeometry.IsKoszulRegularClosedImmersion
