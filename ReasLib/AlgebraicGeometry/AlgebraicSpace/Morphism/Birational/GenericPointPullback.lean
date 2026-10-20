module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Birational
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.SpecStalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Base change of a birational morphism along a generic stalk

A birational morphism of decent algebraic spaces with finitely many irreducible
components becomes an isomorphism after base change to the local scheme at a
generic point of an irreducible component of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A birational morphism between decent algebraic spaces with finitely many
irreducible components becomes an isomorphism after base change to the stalk
spectrum of a schematic open chart at a generic point of the target. -/
theorem isIso_pullbackSnd_fromSpecStalk_of_isBirational
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] {y : Points Y} (hy : y ∈ genericPoints Y)
    {V : Over S} {ιY : ofOver V ⟶ Y} [IsOpenImmersion ιY] {v : V.left}
    (hv : Points.map ιY (ofOver.pointsEquiv V v) = y) :
    IsIso (pullback.snd f (fromSpecStalk ιY v)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
