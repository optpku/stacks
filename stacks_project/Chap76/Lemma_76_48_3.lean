module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection.Finiteness
import StacksCheckRecall

/-!
# Finiteness properties of local complete intersection morphisms of algebraic spaces

A local complete intersection morphism of algebraic spaces is locally of
finite presentation, pseudo-coherent, and perfect.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.48.3 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a local complete
intersection morphism of algebraic spaces over `S`. Then `f` is locally of
finite presentation. -/
@[stacks 06C6] #check
  (AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection.locallyOfFinitePresentation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [IsLocalCompleteIntersection f] → LocallyOfFinitePresentation f)

/- Lemma 76.48.3 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a local complete
intersection morphism of algebraic spaces over `S`. Then `f` is
pseudo-coherent. -/
@[stacks 06C6] #check
  (AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection.pseudoCoherent :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [IsLocalCompleteIntersection f] → PseudoCoherent f)

/- Lemma 76.48.3 (3): Let `S` be a scheme. Let `f : X ⟶ Y` be a local complete
intersection morphism of algebraic spaces over `S`. Then `f` is perfect. -/
@[stacks 06C6] #check
  (AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection.perfect :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [IsLocalCompleteIntersection f] → Perfect f)

end AlgebraicGeometry.AlgebraicSpace
