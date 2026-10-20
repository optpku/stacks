module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing.Unit
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory

universe u

/- Lemma 81.6.5: In the situation of Lemma 81.6.3, with a thickening `i : X ⟶ X'`
and an affine morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`, the
composite of source `G` (`glue i f`) with source `F` (`baseChange i f`) is
isomorphic to the identity on compatible pairs over `Y` and `X'`. Equivalently,
the unit of `glue i f ⊣ baseChange i f` is an isomorphism. -/
@[stacks 07W0]
#check (AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing.unitIsIso :
  ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
    (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f],
    IsIso (AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing.adjunction i f).unit)
