module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe.Singleton
import StacksCheckRecall

/-!
# Reduced locally Noetherian singleton stacks are gerbes

A reduced, locally Noetherian algebraic stack whose space of points is a
singleton is a gerbe over a reduced, locally Noetherian algebraic space that
likewise has a singleton space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.28.12: Let `Z` be a reduced, locally Noetherian algebraic stack
such that `|Z|` is a singleton. Then `Z` is a gerbe over a reduced, locally
Noetherian algebraic space `A` with `|A|` a singleton. -/
@[stacks 06QK] #check
  (AlgebraicGeometry.AlgebraicStack.exists_gerbeOver_reduced_locallyNoetherian_singleton :
    ∀ {S : Scheme.{u}} (Z : GroupoidsOver S) [AlgebraicStack Z] [IsReduced Z]
      [IsLocallyNoetherian Z] [Nonempty (Points Z)] [Subsingleton (Points Z)],
    ∃ (A : AlgebraicSpace S) (π : Z ⟶ A.toGroupoids),
      Gerbe π ∧ IsReduced A.toGroupoids ∧ IsLocallyNoetherian A.toGroupoids ∧
        Nonempty (Points A.toGroupoids) ∧ Subsingleton (Points A.toGroupoids))

#check
  (AlgebraicGeometry.AlgebraicStack.instIsGerbe_of_isReduced_isLocallyNoetherian_singleton :
    ∀ {S : Scheme.{u}} (Z : GroupoidsOver S) [AlgebraicStack Z] [IsReduced Z]
      [IsLocallyNoetherian Z] [Nonempty (Points Z)] [Subsingleton (Points Z)],
    IsGerbe Z)

#check
  (AlgebraicGeometry.AlgebraicStack.isReduced_isLocallyNoetherian_singleton_points_of_gerbeOver :
    ∀ {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z] [IsReduced Z]
      [IsLocallyNoetherian Z] [Nonempty (Points Z)] [Subsingleton (Points Z)]
      {A : AlgebraicSpace S} (π : Z ⟶ A.toGroupoids) [Gerbe π],
    IsReduced A.toGroupoids ∧ IsLocallyNoetherian A.toGroupoids ∧
      Nonempty (Points A.toGroupoids) ∧ Subsingleton (Points A.toGroupoids))

end AlgebraicGeometry.AlgebraicStack
