module

public import stacks_project.Chap100.Definition_100_11_8_ResidualGerbe
public import stacks_project.Chap100.Example_100_11_9_ResidualGerbe
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap101.Lemma_101_5_1

/-!
# Existence of residual gerbes under quasi-compact inertia

If `X` is an algebraic stack whose inertia morphism `I_X ⟶ X` is
quasi-compact, then a residual gerbe of `X` exists at every point of `|X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.31.1: Let `X` be an algebraic stack such that `I_X ⟶ X` is
quasi-compact. Then the residual gerbe of `X` at `x` exists for every
`x ∈ |X|`. -/
@[stacks 06RD, instance]
instance instHasResidualGerbe_of_quasiCompactInertia {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] (x : Points X) :
    HasResidualGerbe X x :=
  sorry

namespace IsResidualGerbe

/-- If the inertia morphism of an algebraic stack `X` is quasi-compact, then
there is a residual gerbe of `X` at every point `x ∈ |X|`. -/
theorem exists_at_of_quasiCompactInertia {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] (x : Points X) :
    ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (ι : Z ⟶ X),
      IsResidualGerbe ι x :=
  sorry

end IsResidualGerbe

end AlgebraicGeometry.AlgebraicStack
