/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal

/-!
# Base change for conormal sheaves

This file records the epimorphism property of the canonical conormal comparison for cartesian
squares of scheme immersions, together with its isomorphism property under flat base change.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Conormal

variable {Z X Z' X' : Scheme.{u}}
variable {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}

/-- For a pullback square of scheme immersions, the canonical conormal comparison is an
epimorphism. -/
theorem map_epi_of_isPullback [IsImmersion i] [IsImmersion i']
    (sq : IsPullback f i i' g) : Epi (map sq.toCommSq) := sorry

/-- For a pullback square of schemes along a flat ambient morphism, the canonical conormal
comparison is an isomorphism. -/
theorem map_isIso_of_isPullback_of_flat [Flat g] (sq : IsPullback f i i' g) :
    IsIso (map sq.toCommSq) := sorry

/-- For a pullback square whose lower horizontal morphism is formally unramified and whose
ambient morphism is flat, the canonical conormal comparison is an isomorphism. -/
theorem map_isIso_of_isPullback_of_flat_of_formallyUnramified [FormallyUnramified i']
    [Flat g] (sq : IsPullback f i i' g) : IsIso (map sq.toCommSq) :=
  map_isIso_of_isPullback_of_flat sq

end AlgebraicGeometry.Scheme.Hom.Conormal
