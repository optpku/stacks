module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.LocalCompleteIntersection
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.62.9 (1): A regular immersion of schemes is a local complete intersection
morphism. -/
@[stacks 069L] #check
  (AlgebraicGeometry.IsRegularImmersion.isLocalCompleteIntersection :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X), [IsRegularImmersion i] →
      LocallyOfType RingHom.IsLocalCompleteIntersection i)

/- Lemma 37.62.9 (2): A Koszul-regular immersion of schemes is a local complete intersection
morphism. -/
@[stacks 069L] #check
  (AlgebraicGeometry.IsKoszulRegularImmersion.isLocalCompleteIntersection :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X), [IsKoszulRegularImmersion i] →
      LocallyOfType RingHom.IsLocalCompleteIntersection i)
