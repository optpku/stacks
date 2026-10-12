/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsImmersion

/-- A scheme morphism is an immersion if its restriction over a suitable target-open
neighborhood of every source point is an immersion. -/
theorem of_forall_source_exists_morphismRestrict
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : ∀ y : Y, ∃ U : X.Opens, f y ∈ U ∧ IsImmersion (f ∣_ U)) :
    IsImmersion f := sorry

end AlgebraicGeometry.IsImmersion
