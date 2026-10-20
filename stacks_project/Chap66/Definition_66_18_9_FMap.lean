module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.FMap
import StacksCheckRecall

/-! # Maps of étale sheaves indexed by geometric squares

@stack 03G3

The public owner retains the actual square-indexed components and their naturality.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 66.18.9: an `f`-map consists of section maps on every commutative square of
étale scheme charts over `f`, compatible with restriction in both charts. -/
@[stacks 03G3] #check (AlgebraicGeometry.AlgebraicSpace.FMap :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (𝒢 : Sheaf (AlgebraicSpace.smallEtaleTopology Y) (Type (u + 1)))
    (ℱ : Sheaf (AlgebraicSpace.smallEtaleTopology X) (Type (u + 1))), Type (u + 1))
