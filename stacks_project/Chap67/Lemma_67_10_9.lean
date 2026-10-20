module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Monomorphism

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.10.9: Let `S` be a scheme. A monomorphism `X ⟶ Y` of algebraic spaces
over `S` induces an injective map `|X| → |Y|`. -/
@[stacks 06RV] #check
  (AlgebraicGeometry.AlgebraicSpace.Points.map_injective_of_mono :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Mono f],
      Function.Injective (AlgebraicGeometry.AlgebraicSpace.Points.map f))
