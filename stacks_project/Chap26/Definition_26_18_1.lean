module

public import Mathlib.AlgebraicGeometry.Pullbacks
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable {S S' : Scheme.{u}} (g : S' ⟶ S)
variable (X Y : Over S) (f : X ⟶ Y)

/- Definition 26.18.1: schemes over `S`, their morphisms, and base change are modeled by the
slice category `Over S` and its canonical pullback functor. -/
@[stacks 01JX] #check (Over S)
@[stacks 01JX] #check (X ⟶ Y)
@[stacks 01JX] #check X.hom
@[stacks 01JX] #check Over.pullback g
@[stacks 01JX] #check (Over.pullback g).obj X
@[stacks 01JX] #check (Over.pullback g).map f

variable (R R' : Type u) [CommRing R] [CommRing R'] (φ : R →+* R')

@[stacks 01JX] #check (Over (Spec (CommRingCat.of R)))
@[stacks 01JX] #check Over.pullback (Spec.map (CommRingCat.ofHom φ))

end AlgebraicGeometry
