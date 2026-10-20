module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocalAt
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open Scheme.Germ.MorphismProperty

/- Definition 67.22.6: let `Q` be a property of morphisms of germs of schemes
which is étale local on the source-and-target. Let `S` be a scheme. Given a
morphism `f : X ⟶ Y` of algebraic spaces over `S` and a point `x` of `|X|`, we
say that `f` has property `Q` at `x` if `existsEtaleSquareAt Q f x` holds,
equivalently if the conditions of Lemma 67.22.5 hold. -/
@[stacks 04RE] #check (AlgebraicGeometry.AlgebraicSpace.existsEtaleSquareAt :
  ∀ {S : Scheme.{u}} (Q : MorphismProperty Scheme.Germ.{u})
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.forallEtaleSquareAt_iff_existsEtaleSquareAt :
  ∀ {S : Scheme.{u}} {Q : MorphismProperty Scheme.Germ.{u}}
    (_hQ : IsEtaleLocal Q) {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X),
    forallEtaleSquareAt Q f x ↔ existsEtaleSquareAt Q f x)

#check (AlgebraicGeometry.AlgebraicSpace.existsEtaleSquareAt_ofOverMap_iff :
  ∀ {S : Scheme.{u}} {Q : MorphismProperty Scheme.Germ.{u}}
    (_hQ : IsEtaleLocal Q) {U V : Over S} (h : U ⟶ V) (u : U.left),
    existsEtaleSquareAt Q (ofOverMap h) (ofOver.pointsEquiv U u) ↔
      Q (ofOverGermHom h u))

end AlgebraicGeometry.AlgebraicSpace
