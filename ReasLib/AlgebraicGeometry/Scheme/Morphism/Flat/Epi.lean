/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Flat

/-- A surjective flat morphism of schemes is an epimorphism. -/
theorem epi_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] : Epi f := sorry

end AlgebraicGeometry.Flat
