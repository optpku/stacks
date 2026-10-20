module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Integral.QuasiSeparated
import StacksCheckRecall

/-!
# Reduced quasi-separated irreducible algebraic stacks are integral

A reduced quasi-separated algebraic stack with irreducible space of points is
integral. Quasi-compactness of the absolute diagonal is already enough in
place of quasi-separatedness.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.50.3: Let `X` be an algebraic stack which is reduced and
quasi-separated and whose associated topological space `|X|` is irreducible.
Then `X` is integral. -/
@[stacks 0GWD] #check
  (AlgebraicGeometry.AlgebraicStack.instIsIntegral_of_isQuasiSeparated :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
      [AlgebraicStack X] [IsReduced X] [IsQuasiSeparated X] [IsIrreducible X],
      IsIntegral X)

#check (AlgebraicGeometry.AlgebraicStack.instQuasiCompact_forget_of_isQuasiSeparated :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] [IsQuasiSeparated X],
    QuasiCompact (forget.{u + 1, u, u, u + 1} X))

#check (AlgebraicGeometry.AlgebraicStack.IsIntegral.of_quasiCompact_diagonal :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsReduced X] [IsIrreducible X]
    (h_quasiCompact :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
        (diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X))),
    IsIntegral X)

end AlgebraicGeometry.AlgebraicStack
