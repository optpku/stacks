module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.FiniteType

/-!
# Unramified morphisms of algebraic spaces are locally of finite type
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.38.6: An unramified morphism of algebraic spaces is locally of finite type. -/
@[stacks 05VZ] #check (AlgebraicGeometry.AlgebraicSpace.locallyOfFiniteType_of_unramified :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Unramified f],
    LocallyOfFiniteType f)

end AlgebraicGeometry.AlgebraicSpace
