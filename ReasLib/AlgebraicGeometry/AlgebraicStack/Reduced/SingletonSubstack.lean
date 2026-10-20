module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Monomorphism

/-!
# Locally Noetherian substacks of reduced singleton stacks

A reduced algebraic stack with exactly one point contains a unique replete full
subcategory that is a reduced, locally Noetherian algebraic stack with exactly
one point. Its literal inclusion is a monomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A reduced algebraic stack with exactly one point has a unique replete full
subcategory whose restricted stack is reduced, locally Noetherian, and has
exactly one point. The literal inclusion of this subcategory is a monomorphism. -/
theorem existsUnique_locallyNoetherian_strictlyFull {S : Scheme.{u}}
    (Z : GroupoidsOver S) [AlgebraicStack Z] [IsReduced Z]
    [Nonempty (Points Z)] [Subsingleton (Points Z)] :
    ∃ (P : ObjectProperty Z.total)
      (h_fibered : Functor.IsFibered.InGroupoids (P.ι ⋙ Z.p))
      (h_algebraicStack : AlgebraicStack (Substack.category Z P h_fibered))
      (h_reduced : IsReduced (Substack.category Z P h_fibered))
      (h_locallyNoetherian : IsLocallyNoetherian (Substack.category Z P h_fibered))
      (h_nonempty : Nonempty (Points (Substack.category Z P h_fibered)))
      (h_subsingleton : Subsingleton (Points (Substack.category Z P h_fibered)))
      (h_strictlyFull : P.IsClosedUnderIsomorphisms),
      Groupoids.Hom.Mono (Substack.inclusion Z P h_fibered) ∧
        ∀ (Q : ObjectProperty Z.total)
          (hQ_fibered : Functor.IsFibered.InGroupoids (Q.ι ⋙ Z.p))
          (hQ_algebraicStack : AlgebraicStack (Substack.category Z Q hQ_fibered))
          (hQ_reduced : IsReduced (Substack.category Z Q hQ_fibered))
          (hQ_locallyNoetherian : IsLocallyNoetherian (Substack.category Z Q hQ_fibered))
          (hQ_nonempty : Nonempty (Points (Substack.category Z Q hQ_fibered)))
          (hQ_subsingleton : Subsingleton (Points (Substack.category Z Q hQ_fibered)))
          (hQ_strictlyFull : Q.IsClosedUnderIsomorphisms),
          Q = P :=
  sorry

end AlgebraicGeometry.AlgebraicStack
