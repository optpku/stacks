module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.Finiteness
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 37.62.4 (1): a local complete-intersection morphism of schemes is locally of finite
presentation. -/
@[stacks 069H] #check
  (AlgebraicGeometry.LocallyOfType.locallyOfFinitePresentation_of_isLocalCompleteIntersection :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      [LocallyOfType RingHom.IsLocalCompleteIntersection f] →
        LocallyOfFinitePresentation f)

/- Lemma 37.62.4 (2): a local complete-intersection morphism of schemes is pseudo-coherent. -/
@[stacks 069H] #check
  (AlgebraicGeometry.LocallyOfType.pseudoCoherent_of_isLocalCompleteIntersection :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      [LocallyOfType RingHom.IsLocalCompleteIntersection f] → PseudoCoherent f)

/- Lemma 37.62.4 (3): a local complete-intersection morphism of schemes is perfect. -/
@[stacks 069H] #check
  (AlgebraicGeometry.LocallyOfType.isPerfect_of_isLocalCompleteIntersection :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      [LocallyOfType RingHom.IsLocalCompleteIntersection f] →
        LocallyOfType RingHom.IsPerfectRingMap f)
