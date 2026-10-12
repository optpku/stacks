/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap81.Lemma_81_6_3_Gluing

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Pushout
namespace Gluing

/-- Lemma 81.6.5: In the situation of Lemma 81.6.3, with a thickening `i : X ⟶ X'`
and an affine morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`, the
composite of source `G` (`glue i f`) with source `F` (`baseChange i f`) is
isomorphic to the identity on compatible pairs over `Y` and `X'`. Equivalently,
the unit of `glue i f ⊣ baseChange i f` is an isomorphism. -/
@[stacks 07W0]
instance unitIsIso {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
    (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f] :
    IsIso (adjunction i f).unit :=
  sorry

end Gluing
end AlgebraicGeometry.AlgebraicSpace.Pushout
