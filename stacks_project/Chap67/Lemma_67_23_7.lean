module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Immersion
import StacksCheckRecall

/-!
# Immersions of algebraic spaces are locally of finite type
-/

open CategoryTheory

universe u

/- Lemma 67.23.7: An immersion of algebraic spaces is locally of finite type. -/
@[stacks 06ED] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyOfFiniteType_of_isImmersion :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.IsImmersion f],
      AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f)
