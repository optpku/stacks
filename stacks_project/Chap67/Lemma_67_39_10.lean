module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Etale.Unramified
import StacksCheckRecall

/-!
# Étale morphisms of algebraic spaces are unramified
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.39.10: An étale morphism of algebraic spaces is unramified. -/
@[stacks 06CR] #check (AlgebraicGeometry.AlgebraicSpace.unramified_of_etale :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f], Unramified f)

end AlgebraicGeometry.AlgebraicSpace
