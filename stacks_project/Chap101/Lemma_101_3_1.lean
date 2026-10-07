module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap101.Lemma_101_3_2_Isom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 101.3.1

For an algebraic stack `X` and fibre objects `x, y` over a scheme `T`, the
structure morphism `Isom_X(x, y) ⟶ T` is locally of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Isom

/-- Lemma 101.3.1: Let `X` be an algebraic stack. Let `T` be a scheme and let
`x`, `y` be objects of the fibre category of `X` over `T`. Then the morphism
`Isom_X(x, y) ⟶ T` is locally of finite type. -/
@[stacks 04XR, instance]
instance locallyOfFiniteType_isomOverHom {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {T : Over S} (x y : X.p.Fiber T) :
    AlgebraicSpace.LocallyOfFiniteType (isomOverHom x y) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Isom
