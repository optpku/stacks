module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.Flat
import StacksCheckRecall

/-!
# Étale morphisms of algebraic spaces are flat
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.39.7: An étale morphism of algebraic spaces is flat. -/
@[stacks 0467] #check (AlgebraicGeometry.AlgebraicSpace.flat_of_etale :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f], Flat f)

end AlgebraicGeometry.AlgebraicSpace
