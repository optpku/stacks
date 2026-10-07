module

public import stacks_project.Chap101.Definition_101_28_1_Gerbe
public import stacks_project.Chap101.Definition_101_15_2_UniversalHomeomorphism

/-!
# Gerbes are universal homeomorphisms

A morphism of algebraic stacks that makes the source a gerbe over the target
is a universal homeomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace UniversalHomeomorphism

/-- Lemma 101.28.13: Let `f : X ⟶ Y` be a morphism of algebraic stacks.
If `X` is a gerbe over `Y`, then `f` is a universal homeomorphism. -/
@[stacks 06R9]
instance of_gerbe {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f] :
    UniversalHomeomorphism f :=
  sorry

end UniversalHomeomorphism

/-- A gerbe morphism of algebraic stacks induces a homeomorphism on underlying
point spaces. -/
theorem pointsIsHomeomorph_of_gerbe {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f] :
    pointsIsHomeomorph f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
