module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Pair
import StacksCheckRecall

open CategoryTheory

universe u

/- 79.12.0.1: For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`,
and for an algebraic space or a scheme `T` over `S`, a pair `(a, Z)` consists of
a morphism `a : T ⟶ Y` over `S` together with an open subspace
`Z : OpenSubspace (pullback a f)` of `T ×_Y X` such that
`IsFinite (Z.ι ≫ pullback.fst a f)`, i.e. `pr₀|_Z : Z ⟶ T` is finite. -/
@[stacks 04PC] #check (AlgebraicGeometry.AlgebraicSpace.FinitePart :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → AlgebraicGeometry.AlgebraicSpace S → Type (u + 1))
