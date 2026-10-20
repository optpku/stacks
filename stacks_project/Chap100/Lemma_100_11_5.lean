/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced.SingletonSubstack

/-!
# Unique locally Noetherian strictly full subcategory

A reduced algebraic stack with a singleton space of points has a unique strictly
full subcategory that is reduced, locally Noetherian, and still a singleton on
points. The inclusion of that subcategory is a monomorphism of algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 100.11.5: A reduced singleton algebraic stack has a unique reduced,
locally Noetherian strictly full singleton subcategory, with monomorphic inclusion. -/
@[stacks 06MR] #check (AlgebraicGeometry.AlgebraicStack.existsUnique_locallyNoetherian_strictlyFull :
    ∀ {S : Scheme.{u}}
    (Z : GroupoidsOver S) [AlgebraicStack Z] [IsReduced Z]
    [Nonempty (Points Z)] [Subsingleton (Points Z)],
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
          Q = P)

end AlgebraicGeometry.AlgebraicStack
