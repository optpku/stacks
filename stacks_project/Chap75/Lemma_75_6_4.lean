module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.Conservative
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/- Lemma 75.6.4: derived pushforward along an affine morphism of algebraic spaces
reflects isomorphisms. -/
@[stacks 08II] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforward.reflectsIsomorphisms_of_affine :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f],
      (pushforwardCohomologyIn f).ReflectsIsomorphisms)

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
