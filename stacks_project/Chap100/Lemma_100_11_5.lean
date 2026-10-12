/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap100.Definition_100_8_1_Mono
public import stacks_project.Chap100.Lemma_100_9_10_Substack
public import stacks_project.Chap100.Lemma_100_11_2_Reduced
public import stacks_project.Chap100.Lemma_100_11_3_LocallyNoetherian

/-!
# Unique locally Noetherian strictly full subcategory

A reduced algebraic stack with a singleton space of points has a unique strictly
full subcategory that is reduced, locally Noetherian, and still a singleton on
points. The inclusion of that subcategory is a monomorphism of algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 100.11.5 (1): Let `Z` be an algebraic stack satisfying the equivalent
conditions of Lemma 100.11.2, i.e. `Z` is reduced and `Points Z` is a
singleton. There exists a unique strictly full subcategory of `Z`, as an
`ObjectProperty` of `Z.total`, whose associated algebraic stack
`ofFunctor (P.ι ⋙ Z.p)` satisfies the equivalent conditions of Lemma 100.11.3.
Uniqueness is equality of essential images of `inclusionOf`, not of a bundled
pair `(Z', ι)`. -/
@[stacks 06MR]
theorem existsUnique_locallyNoetherian_strictlyFull {S : Scheme.{u}}
    (Z : GroupoidsOver S) [AlgebraicStack Z] [IsReduced Z]
    [Nonempty (Points Z)] [Subsingleton (Points Z)] :
    ∃ (P : ObjectProperty Z.total)
      (h_fibered : Functor.IsFibered.InGroupoids (P.ι ⋙ Z.p))
      (h_algebraicStack : AlgebraicStack (ofFunctor (P.ι ⋙ Z.p)))
      (h_reduced : IsReduced (ofFunctor (P.ι ⋙ Z.p)))
      (h_locallyNoetherian : IsLocallyNoetherian (ofFunctor (P.ι ⋙ Z.p)))
      (h_nonempty : Nonempty (Points (ofFunctor (P.ι ⋙ Z.p))))
      (h_subsingleton : Subsingleton (Points (ofFunctor (P.ι ⋙ Z.p))))
      (h_strictlyFull : IsStrictlyFull (inclusionOf Z P)),
      ∀ (Q : ObjectProperty Z.total)
        (hQ_fibered : Functor.IsFibered.InGroupoids (Q.ι ⋙ Z.p))
        (hQ_algebraicStack : AlgebraicStack (ofFunctor (Q.ι ⋙ Z.p)))
        (hQ_reduced : IsReduced (ofFunctor (Q.ι ⋙ Z.p)))
        (hQ_locallyNoetherian : IsLocallyNoetherian (ofFunctor (Q.ι ⋙ Z.p)))
        (hQ_nonempty : Nonempty (Points (ofFunctor (Q.ι ⋙ Z.p))))
        (hQ_subsingleton : Subsingleton (Points (ofFunctor (Q.ι ⋙ Z.p))))
        (hQ_strictlyFull : IsStrictlyFull (inclusionOf Z Q)),
        (toFunctor (inclusionOf Z Q)).essImage =
          (toFunctor (inclusionOf Z P)).essImage :=
  sorry

/-- Any two strictly full inclusions of algebraic stacks satisfying the
equivalent conditions of Lemma 100.11.3 into an ambient algebraic stack
satisfying the equivalent conditions of Lemma 100.11.2 have the same essential
image. -/
theorem unique_locallyNoetherian_strictlyFull {S : Scheme.{u}}
    {Z Z' Z'' : GroupoidsOver S}
    [AlgebraicStack Z] [AlgebraicStack Z'] [AlgebraicStack Z'']
    [IsReduced Z] [Nonempty (Points Z)] [Subsingleton (Points Z)]
    (ι' : Z' ⟶ Z) (ι'' : Z'' ⟶ Z)
    [IsStrictlyFull ι'] [IsStrictlyFull ι'']
    [IsReduced Z'] [IsReduced Z'']
    [IsLocallyNoetherian Z'] [IsLocallyNoetherian Z'']
    [Nonempty (Points Z')] [Nonempty (Points Z'')]
    [Subsingleton (Points Z')] [Subsingleton (Points Z'')] :
    (toFunctor ι').essImage = (toFunctor ι'').essImage :=
  sorry

/-- If `Z` itself satisfies the equivalent conditions of Lemma 100.11.3, then
the essential image of `𝟙 Z` is the unique strictly full subcategory of that
kind. -/
theorem unique_locallyNoetherian_strictlyFull_id {S : Scheme.{u}}
    {Z Z' : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack Z']
    [IsReduced Z] [IsLocallyNoetherian Z]
    [Nonempty (Points Z)] [Subsingleton (Points Z)]
    (ι : Z' ⟶ Z) [IsStrictlyFull ι]
    [IsReduced Z'] [IsLocallyNoetherian Z']
    [Nonempty (Points Z')] [Subsingleton (Points Z')] :
    (toFunctor ι).essImage = (toFunctor (𝟙 Z)).essImage :=
  sorry

/-- Lemma 100.11.5 (2): The inclusion of a strictly full subcategory `Z' ⟶ Z`
that is a reduced, locally Noetherian algebraic stack with singleton `Points`
is a monomorphism of algebraic stacks. -/
@[stacks 06MR]
theorem locallyNoetherian_strictlyFull_inclusion_mono {S : Scheme.{u}}
    {Z Z' : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack Z']
    (ι : Z' ⟶ Z) [IsStrictlyFull ι]
    [IsReduced Z'] [IsLocallyNoetherian Z']
    [Nonempty (Points Z')] [Subsingleton (Points Z')] :
    Groupoids.Hom.Mono ι :=
  sorry

end AlgebraicGeometry.AlgebraicStack
