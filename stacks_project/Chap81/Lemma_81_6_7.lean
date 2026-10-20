module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing.MorphismProperties
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing.Flat
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing
open AlgebraicGeometry.AlgebraicSpace.PushoutAlongThickening
open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 81.6.7 (1): an algebraic space obtained by pushout gluing is locally of
finite type over `pushout i f` exactly when both components are locally of finite
type. -/
@[stacks 07W3] #check
  (AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing.locallyOfFiniteType_iff :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [Affine f]
      (P : CategoricalPullback (Over.pullback f) (Over.pullback i)),
      LocallyOfFiniteType ((glue i f).obj P).hom ↔
        LocallyOfFiniteType P.fst.hom ∧ LocallyOfFiniteType P.snd.hom)

/- Lemma 81.6.7 (2): an algebraic space obtained by pushout gluing is flat over
`pushout i f` exactly when both components are flat. -/
@[stacks 07W3] #check
  (AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing.flat_iff :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [Affine f]
      (P : CategoricalPullback (Over.pullback f) (Over.pullback i)),
      AlgebraicGeometry.AlgebraicSpace.Flat ((glue i f).obj P).hom ↔
        AlgebraicGeometry.AlgebraicSpace.Flat P.fst.hom ∧
          AlgebraicGeometry.AlgebraicSpace.Flat P.snd.hom)

/- Lemma 81.6.7 (3): an algebraic space obtained by pushout gluing is flat and
locally of finite presentation exactly when both components have these two
properties. -/
@[stacks 07W3] #check
  (AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing.flatLocallyOfFinitePresentation_iff :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [Affine f]
      (P : CategoricalPullback (Over.pullback f) (Over.pullback i)),
      (AlgebraicGeometry.AlgebraicSpace.Flat ((glue i f).obj P).hom ∧
          LocallyOfFinitePresentation ((glue i f).obj P).hom) ↔
        (AlgebraicGeometry.AlgebraicSpace.Flat P.fst.hom ∧
            LocallyOfFinitePresentation P.fst.hom) ∧
          (AlgebraicGeometry.AlgebraicSpace.Flat P.snd.hom ∧
            LocallyOfFinitePresentation P.snd.hom))

/- Lemma 81.6.7 (4): an algebraic space obtained by pushout gluing is smooth over
`pushout i f` exactly when both components are smooth. -/
@[stacks 07W3] #check
  (AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing.smooth_iff :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [Affine f]
      (P : CategoricalPullback (Over.pullback f) (Over.pullback i)),
      Smooth ((glue i f).obj P).hom ↔ Smooth P.fst.hom ∧ Smooth P.snd.hom)

/- Lemma 81.6.7 (5): an algebraic space obtained by pushout gluing is étale over
`pushout i f` exactly when both components are étale. -/
@[stacks 07W3] #check
  (AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing.etale_iff :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [Affine f]
      (P : CategoricalPullback (Over.pullback f) (Over.pullback i)),
      Etale ((glue i f).obj P).hom ↔ Etale P.fst.hom ∧ Etale P.snd.hom)

/- Lemma 81.6.7 (6): on an algebraic space flat over `pushout i f`, the counit
from gluing its two base changes back to the original algebraic space is an
isomorphism. -/
@[stacks 07W3] #check
  (AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing.counitIsIsoOfFlat :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [Affine f] (Z : Over (pushout i f))
      [AlgebraicGeometry.AlgebraicSpace.Flat Z.hom],
      IsIso ((adjunction i f).counit.app Z))

/- Lemma 81.6.7 (7): the restricted gluing and base-change functors form the
specified adjunction between componentwise-flat triples and algebraic spaces
flat over the pushout. -/
@[stacks 07W3] #check
  (AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing.Flat.adjunction :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [Affine f],
      Flat.glue i f ⊣ Flat.baseChange i f)

/- Lemma 81.6.7 (8): every component of the unit of the restricted adjunction is
an isomorphism. -/
@[stacks 07W3] #check
  (AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing.Flat.unitAppIsIso :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [Affine f] (P : Flat.Triple i f),
      IsIso ((Flat.adjunction i f).unit.app P))

/- Lemma 81.6.7 (9): every component of the counit of the restricted adjunction
is an isomorphism. -/
@[stacks 07W3] #check
  (AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing.Flat.counitAppIsIso :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [Affine f]
      (Z : AlgebraicGeometry.AlgebraicSpace.FlatOver (pushout i f)),
      IsIso ((Flat.adjunction i f).counit.app Z))

/- Lemma 81.6.7 (10): restricted base change is an equivalence from algebraic
spaces flat over the pushout to compatible triples whose two components are
flat. -/
@[stacks 07W3] #check
  (AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing.Flat.baseChangeIsEquivalence :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [Affine f],
      Functor.IsEquivalence (Flat.baseChange i f))

/- Lemma 81.6.7 (11): restricted gluing is the specified quasi-inverse
equivalence to restricted base change. -/
@[stacks 07W3] #check
  (AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing.Flat.glueIsEquivalence :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [Affine f],
      Functor.IsEquivalence (Flat.glue i f))
