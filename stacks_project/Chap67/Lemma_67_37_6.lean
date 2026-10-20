module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
import StacksCheckRecall

/-!
# Smooth morphisms of algebraic spaces are locally of finite type
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.37.6: A smooth morphism of algebraic spaces is locally of finite type. -/
@[stacks 06MH] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyOfFiniteType_of_smooth :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Smooth f],
      LocallyOfFiniteType f)

end AlgebraicGeometry.AlgebraicSpace
