/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_4_1_Points

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.10.9: if `f : X ⟶ Y` is a monomorphism of algebraic spaces over a scheme `S`,
then the induced map of points `|X| ⟶ |Y|` is injective. -/
@[stacks 06RV]
theorem Points.map_injective_of_mono {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Mono f] : Function.Injective (Points.map f) := sorry

end AlgebraicGeometry.AlgebraicSpace
