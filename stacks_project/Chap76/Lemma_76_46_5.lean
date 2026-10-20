module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.PseudoCoherent.Flat
import StacksCheckRecall

/-!
# Flat morphisms of algebraic spaces that are locally of finite presentation
are pseudo-coherent
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.46.5: A flat morphism of algebraic spaces which is locally of
finite presentation is pseudo-coherent. -/
@[stacks 06BV] #check
  (AlgebraicGeometry.AlgebraicSpace.pseudoCoherent_of_flat_of_locallyOfFinitePresentation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Flat f]
      [LocallyOfFinitePresentation f], PseudoCoherent f)

end AlgebraicGeometry.AlgebraicSpace
