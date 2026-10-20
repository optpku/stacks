module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.FiniteType
import StacksCheckRecall

/-!
# Étale morphisms of algebraic spaces are locally of finite type
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.39.9: An étale morphism of algebraic spaces is locally of finite type. -/
@[stacks 06LT] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyOfFiniteType_of_etale :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [AlgebraicGeometry.AlgebraicSpace.Etale f] →
        AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f)
