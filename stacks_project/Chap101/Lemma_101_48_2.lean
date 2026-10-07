module

public import stacks_project.Chap101.Definition_101_8_1_Noetherian
public import stacks_project.Chap101.Definition_101_50_1_Decent

/-!
# Quasi-separated algebraic stacks are decent

A quasi-separated algebraic stack is decent. More generally, quasi-compactness of
the diagonal is enough.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.48.2 (1): A quasi-separated algebraic stack `X` is decent. -/
@[stacks 0GW2]
instance instIsDecent_of_isQuasiSeparated {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsQuasiSeparated X] : IsDecent X :=
  sorry

/-- Lemma 101.48.2 (2): More generally, if `Δ : X ⟶ X × X` is quasi-compact,
then `X` is decent. -/
@[stacks 0GW2]
theorem IsDecent.of_quasiCompact_diagonal {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X]
    (h_quasiCompact :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
        (diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X))) :
    IsDecent X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
