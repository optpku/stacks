/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Definition_100_8_1_Mono
public import stacks_project.Chap100.Definition_100_9_1_Immersion

/-!
# Immersions of algebraic stacks are monomorphisms

An immersion of algebraic stacks is a monomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace Immersion

/-- Lemma 100.9.5: an immersion of algebraic stacks is a monomorphism. -/
@[stacks 0504]
instance mono {S : Scheme.{u}} {X Y : GroupoidsOver S} {f : X ⟶ Y}
    [Immersion f] : Mono f := sorry

end Immersion

end AlgebraicGeometry.Groupoids.Hom
