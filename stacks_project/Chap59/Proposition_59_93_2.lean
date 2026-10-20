module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocalAcyclicity.Smooth
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/- Proposition 59.93.2: a smooth morphism of schemes is universally locally acyclic. -/
@[stacks 0GJQ] #check (AlgebraicGeometry.Scheme.UniversallyLocallyAcyclic.of_smooth :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f], UniversallyLocallyAcyclic f)

end AlgebraicGeometry.Scheme
