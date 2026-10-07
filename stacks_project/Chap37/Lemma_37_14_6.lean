module

public import ReasLib.AlgebraicGeometry.Scheme.Pushout.Gluing.Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Pushout.Gluing

/- Lemma 37.14.6 (1): a scheme obtained by pushout gluing is locally of finite type over
`pushout i f` exactly when both components are locally of finite type. -/
@[stacks 07RX] #check
  (AlgebraicGeometry.Scheme.Pushout.Gluing.locallyOfFiniteType_iff :
    ∀ {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [IsAffineHom f]
      (P : CategoricalPullback (Over.pullback f) (Over.pullback i)),
      LocallyOfFiniteType ((Gluing.glue i f).obj P).hom ↔
        LocallyOfFiniteType P.fst.hom ∧ LocallyOfFiniteType P.snd.hom)

/- Lemma 37.14.6 (2): a scheme obtained by pushout gluing is flat over `pushout i f`
exactly when both components are flat. -/
@[stacks 07RX] #check
  (AlgebraicGeometry.Scheme.Pushout.Gluing.flat_iff :
    ∀ {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [IsAffineHom f]
      (P : CategoricalPullback (Over.pullback f) (Over.pullback i)),
      AlgebraicGeometry.Flat ((Gluing.glue i f).obj P).hom ↔
        AlgebraicGeometry.Flat P.fst.hom ∧ AlgebraicGeometry.Flat P.snd.hom)

/- Lemma 37.14.6 (3): a scheme obtained by pushout gluing is flat and locally of finite
presentation exactly when both components have these two properties. -/
@[stacks 07RX] #check
  (AlgebraicGeometry.Scheme.Pushout.Gluing.flatLocallyOfFinitePresentation_iff :
    ∀ {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [IsAffineHom f]
      (P : CategoricalPullback (Over.pullback f) (Over.pullback i)),
      (AlgebraicGeometry.Flat ((Gluing.glue i f).obj P).hom ∧
          LocallyOfFinitePresentation ((Gluing.glue i f).obj P).hom) ↔
        (AlgebraicGeometry.Flat P.fst.hom ∧ LocallyOfFinitePresentation P.fst.hom) ∧
          (AlgebraicGeometry.Flat P.snd.hom ∧ LocallyOfFinitePresentation P.snd.hom))

/- Lemma 37.14.6 (4): a scheme obtained by pushout gluing is smooth over `pushout i f`
exactly when both components are smooth. -/
@[stacks 07RX] #check
  (AlgebraicGeometry.Scheme.Pushout.Gluing.smooth_iff :
    ∀ {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [IsAffineHom f]
      (P : CategoricalPullback (Over.pullback f) (Over.pullback i)),
      Smooth ((Gluing.glue i f).obj P).hom ↔ Smooth P.fst.hom ∧ Smooth P.snd.hom)

/- Lemma 37.14.6 (5): a scheme obtained by pushout gluing is étale over `pushout i f`
exactly when both components are étale. -/
@[stacks 07RX] #check
  (AlgebraicGeometry.Scheme.Pushout.Gluing.etale_iff :
    ∀ {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [IsAffineHom f]
      (P : CategoricalPullback (Over.pullback f) (Over.pullback i)),
      Etale ((Gluing.glue i f).obj P).hom ↔ Etale P.fst.hom ∧ Etale P.snd.hom)

/- Lemma 37.14.6 (6): on a scheme flat over `pushout i f`, the counit from gluing its two
base changes back to the original scheme is an isomorphism. -/
@[stacks 07RX] #check
  (AlgebraicGeometry.Scheme.Pushout.Gluing.counitIsIsoOfFlat :
    ∀ {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [IsAffineHom f] (Z : Over (pushout i f))
      [AlgebraicGeometry.Flat Z.hom],
      IsIso ((Gluing.adjunction i f).counit.app Z))

/- Lemma 37.14.6 (7): the restricted gluing and base-change functors form the specified
adjunction between componentwise-flat triples and schemes flat over the pushout. -/
@[stacks 07RX] #check
  (AlgebraicGeometry.Scheme.Pushout.Gluing.Flat.adjunction :
    ∀ {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [IsAffineHom f],
      Gluing.Flat.glue i f ⊣ Gluing.Flat.baseChange i f)

/- Lemma 37.14.6 (7): every component of the unit of the restricted adjunction is an
isomorphism. -/
@[stacks 07RX] #check
  (AlgebraicGeometry.Scheme.Pushout.Gluing.Flat.unitAppIsIso :
    ∀ {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [IsAffineHom f] (P : Gluing.Flat.Triple i f),
      IsIso ((Gluing.Flat.adjunction i f).unit.app P))

/- Lemma 37.14.6 (7): every component of the counit of the restricted adjunction is an
isomorphism. -/
@[stacks 07RX] #check
  (AlgebraicGeometry.Scheme.Pushout.Gluing.Flat.counitAppIsIso :
    ∀ {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [IsAffineHom f]
      (Z : AlgebraicGeometry.FlatOver (pushout i f)),
      IsIso ((Gluing.Flat.adjunction i f).counit.app Z))

/- Lemma 37.14.6 (7): restricted base change is an equivalence from schemes flat over the
pushout to compatible triples whose two components are flat. -/
@[stacks 07RX] #check
  (AlgebraicGeometry.Scheme.Pushout.Gluing.Flat.baseChangeIsEquivalence :
    ∀ {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [IsAffineHom f],
      Functor.IsEquivalence (Gluing.Flat.baseChange i f))

/- Lemma 37.14.6 (7): restricted gluing is the specified quasi-inverse equivalence to
restricted base change. -/
@[stacks 07RX] #check
  (AlgebraicGeometry.Scheme.Pushout.Gluing.Flat.glueIsEquivalence :
    ∀ {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [IsAffineHom f],
      Functor.IsEquivalence (Gluing.Flat.glue i f))

end AlgebraicGeometry.Scheme.Pushout.Gluing
