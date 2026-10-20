module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.QuasiFinite
import StacksCheckRecall

/-!
# Unramified morphisms of algebraic spaces are locally quasi-finite
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.38.7 (1): If `f` is unramified at `x` then `f` is quasi-finite at
`x`. -/
@[stacks 05W0]
#check (AlgebraicGeometry.AlgebraicSpace.UnramifiedAt.quasiFiniteAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {x : Points X},
    UnramifiedAt f x → FiniteType.QuasiFiniteAt f x)

/- Lemma 67.38.7 (2): An unramified morphism of algebraic spaces is locally
quasi-finite. -/
@[stacks 05W0]
#check (AlgebraicGeometry.AlgebraicSpace.locallyQuasiFinite_of_unramified :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Unramified f],
    LocallyQuasiFinite f)

end AlgebraicGeometry.AlgebraicSpace
