module

public import stacks_project.Chap103.«103_15_1_1_Smooth»
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation
public import stacks_project.Chap106.Definition_106_8_1_FormallySmooth

/-!
# Smooth morphisms of algebraic stacks versus formal smoothness

A morphism of algebraic stacks is smooth if and only if it is locally of finite
presentation and formally smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks is smooth if and only if it is locally of
finite presentation and formally smooth. -/
theorem Smooth.iff_locallyOfFinitePresentation_and_formallySmooth
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    Smooth f ↔ LocallyOfFinitePresentation f ∧ FormallySmooth f :=
  sorry

/-- A smooth morphism of algebraic stacks is formally smooth. -/
instance FormallySmooth.of_smooth {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f] :
    FormallySmooth f :=
  sorry

/-- A locally finitely presented, formally smooth morphism of algebraic stacks is
smooth. -/
instance Smooth.of_locallyOfFinitePresentation_of_formallySmooth
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] [FormallySmooth f] : Smooth f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
