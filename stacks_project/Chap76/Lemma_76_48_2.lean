module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection.Smooth
import StacksCheckRecall

/-!
# Koszul-regular immersions from étale charts into a smooth space

An étale-local immersion of algebraic spaces into a space smooth over `Y` is
Koszul-regular when the structure morphism `X ⟶ Y` is a local complete
intersection.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.48.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a local complete
intersection morphism of algebraic spaces over `S`. Let `P` be an algebraic
space smooth over `Y`. Let `U ⟶ X` be an étale morphism of algebraic spaces
and let `i : U ⟶ P` be an immersion of algebraic spaces over `Y`. Then `i` is
a Koszul-regular immersion of algebraic spaces. -/
@[stacks 06C5] #check
  (AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion.of_localCompleteIntersection_over_smooth :
    ∀ {S : Scheme.{u}} {X Y P U : AlgebraicSpace S}
      (f : X ⟶ Y) (p : P ⟶ Y) (u : U ⟶ X) (i : U ⟶ P)
      [IsLocalCompleteIntersection f] [Smooth p] [Etale u] [IsImmersion i],
      (i ≫ p = u ≫ f) → IsKoszulRegularImmersion i)
