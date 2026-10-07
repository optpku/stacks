module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.FinitePresentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Lemma 38.13.9: a flat morphism locally of finite type over an integral target scheme is
locally of finite presentation. -/
@[stacks 05IN] #check
  (AlgebraicGeometry.instLocallyOfFinitePresentationOfFlatOfIsIntegral :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [Flat f] [IsIntegral S],
      LocallyOfFinitePresentation f)

end AlgebraicGeometry
