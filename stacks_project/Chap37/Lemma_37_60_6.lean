module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Lemma 37.60.6: a flat morphism which is locally of finite presentation is
pseudo-coherent. -/
@[stacks 0695] #check
  (AlgebraicGeometry.pseudoCoherent_of_flat_of_locallyOfFinitePresentation :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f],
      PseudoCoherent f)

end AlgebraicGeometry
