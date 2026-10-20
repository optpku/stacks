module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreserving.Counterexamples
import StacksCheckRecall

/-!
# Limit preserving on objects, not limit preserving
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
universe u

/- Lemma 110.54.1: for a nonempty scheme `S` there exists a stack in groupoids
`p : 𝒳 ⟶ (Sch/S)_fppf` that is limit preserving on objects, while `𝒳` is not
limit preserving. -/
@[stacks 07Z1] #check
  (AlgebraicGeometry.Groupoids.exists_limitPreservingOnObjects_not_limitPreserving :
    ∀ {S : Scheme.{u}} [Nonempty S],
    ∃ (𝒳 : StackOver.Groupoids.{u + 1, u, u + 1, u}
        (Scheme.fppfTopology.over S)),
      AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects
          (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1}
            𝒳.toGroupoids) ∧
        ¬ AlgebraicGeometry.Groupoids.LimitPreserving 𝒳.toGroupoids)
