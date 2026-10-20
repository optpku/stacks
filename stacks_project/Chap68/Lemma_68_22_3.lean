module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Birational.GenericPointPullback

/-!
# Base change of a birational morphism along a generic stalk

A birational morphism of decent algebraic spaces with finitely many irreducible
components becomes an isomorphism after base change to `Spec(𝒪_{Y, y})` at a
generic point of an irreducible component of the target.
-/

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.22.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a birational morphism of
algebraic spaces over `S` which are decent and have finitely many irreducible
components. If `y ∈ genericPoints Y`, then the base-change projection
`pullback.snd f (fromSpecStalk ιY v)` is an isomorphism, where `ιY` is a
schematic open immersion chart of `y`. -/
@[stacks 0BBD] #check
  (AlgebraicGeometry.AlgebraicSpace.isIso_pullbackSnd_fromSpecStalk_of_isBirational :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] {y : Points Y} (hy : y ∈ genericPoints Y)
    {V : Over S} {ιY : ofOver V ⟶ Y} [IsOpenImmersion ιY] {v : V.left}
    (hv : Points.map ιY (ofOver.pointsEquiv V v) = y),
    IsIso (pullback.snd f (fromSpecStalk ιY v)))

end AlgebraicGeometry.AlgebraicSpace
