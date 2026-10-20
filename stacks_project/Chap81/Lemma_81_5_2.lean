module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesModification
import StacksCheckRecall

/-!
# Étale gluing along a proper modification

The source statement is recorded using the canonical base-change comparison.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 81.5.2: A proper morphism that is an isomorphism outside a closed
subspace induces an equivalence from étale spaces over the base to compatible
pairs over the modification and the closed subspace. -/
@[stacks 0GG1] #check
  (AlgebraicGeometry.AlgebraicSpace.spacesEtaleGlueFunctor_isEquivalence :
    ∀ {S : Scheme.{u}} {Y' Y Z E : AlgebraicSpace S}
      (f : Y' ⟶ Y) (i : Z ⟶ Y) (j : E ⟶ Y') (g : E ⟶ Z)
      (h_cart : IsPullback j g f i) [Proper f] [IsClosedImmersion i]
      (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)),
      (spacesEtaleGlueFunctor f i j g h_cart).IsEquivalence)

#check
  (AlgebraicGeometry.AlgebraicSpace.spacesEtaleGlueFunctor_isEquivalence_of_hasPullback :
    ∀ {S : Scheme.{u}} {Y' Y Z : AlgebraicSpace S}
      (f : Y' ⟶ Y) (i : Z ⟶ Y) [Proper f] [IsClosedImmersion i]
      (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)),
      (spacesEtaleGlueFunctor f i (Limits.pullback.snd i f) (Limits.pullback.fst i f)
        (IsPullback.of_hasPullback i f).flip).IsEquivalence)
