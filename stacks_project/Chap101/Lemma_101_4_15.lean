module

public import stacks_project.Chap100.Definition_100_8_1_Mono
public import stacks_project.Chap100.Definition_100_9_1_Immersion
public import stacks_project.Chap101.Definition_101_4_1_Separation

/-!
# Monomorphisms and immersions of algebraic stacks are separated and DM

A monomorphism of algebraic stacks is separated and DM, and the same holds
for immersions of algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Separated

/-- Lemma 101.4.15 (1): A monomorphism of algebraic stacks is separated. -/
@[stacks 06MY]
instance of_mono {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.Mono f] :
    Separated f :=
  sorry

/-- Lemma 101.4.15 (3): An immersion of algebraic stacks is separated. -/
@[stacks 06MY]
instance of_immersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.Immersion f] :
    Separated f :=
  sorry

end Separated

namespace DM

/-- Lemma 101.4.15 (2): A monomorphism of algebraic stacks is DM. -/
@[stacks 06MY]
instance of_mono {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.Mono f] :
    DM f :=
  sorry

/-- Lemma 101.4.15 (4): An immersion of algebraic stacks is DM. -/
@[stacks 06MY]
instance of_immersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.Immersion f] :
    DM f :=
  sorry

end DM

end AlgebraicGeometry.AlgebraicStack
