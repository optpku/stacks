module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsImmersion f]

/- Lemma 67.10.7 (1): an immersion of algebraic spaces is a monomorphism. -/
@[stacks 042R]
#check (AlgebraicGeometry.AlgebraicSpace.IsImmersion.mono (f := f) : Mono f)

/- Lemma 67.10.7 (2): an immersion of algebraic spaces is separated. -/
@[stacks 042R]
#check (AlgebraicGeometry.AlgebraicSpace.IsImmersion.separated (f := f) : Separated f)

end AlgebraicGeometry.AlgebraicSpace
