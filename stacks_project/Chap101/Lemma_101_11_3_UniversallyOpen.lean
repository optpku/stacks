module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyOpen
public import stacks_project.Chap101.Lemma_101_27_15_OpenMap

/-!
# Open and universally open morphisms of algebraic stacks

Compatibility checks for the canonical open and universally open morphism
predicates. The historical point-map import preserves the existing exports.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicStack.Open :
  {S : Scheme.{u}} → {X Y : GroupoidsOver S} →
    [AlgebraicStack X] → [AlgebraicStack Y] → (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicStack.UniversallyOpen :
  {S : Scheme.{u}} → {X Y : GroupoidsOver S} →
    [AlgebraicStack X] → [AlgebraicStack Y] → (X ⟶ Y) → Prop)
