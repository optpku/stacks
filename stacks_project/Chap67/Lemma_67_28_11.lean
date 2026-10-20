module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
import StacksCheckRecall

/-!
# Open immersions of algebraic spaces are locally of finite presentation
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.28.11: An open immersion of algebraic spaces is locally of finite
presentation. -/
@[stacks 06CN] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyOfFinitePresentation_of_isOpenImmersion :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsOpenImmersion f],
      LocallyOfFinitePresentation f)

end AlgebraicGeometry.AlgebraicSpace
