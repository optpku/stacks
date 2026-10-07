module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Pushout.ClosedImmersion.MorphismProperties

@[expose] public section

open CategoryTheory

universe u

noncomputable section

/- Lemma 37.67.9 (1): the induced morphism of pushouts is locally of finite
type exactly when both component morphisms are locally of finite type. -/
@[stacks 0CYY]
#check (AlgebraicGeometry.Scheme.Pushout.ClosedImmersion.inducedMap_locallyOfFiniteType_iff :
  ∀ {Z X Y : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsClosedImmersion j]
    (P : CategoryTheory.Limits.CategoricalPullback
      (CategoryTheory.Over.pullback i) (CategoryTheory.Over.pullback j)),
    AlgebraicGeometry.LocallyOfFiniteType
        (AlgebraicGeometry.Scheme.Pushout.ClosedImmersion.inducedMap i j P) ↔
      AlgebraicGeometry.LocallyOfFiniteType P.fst.hom ∧
        AlgebraicGeometry.LocallyOfFiniteType P.snd.hom)

/- Lemma 37.67.9 (2): the induced morphism of pushouts is flat exactly when
both component morphisms are flat. -/
@[stacks 0CYY]
#check (AlgebraicGeometry.Scheme.Pushout.ClosedImmersion.inducedMap_flat_iff :
  ∀ {Z X Y : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsClosedImmersion j]
    (P : CategoryTheory.Limits.CategoricalPullback
      (CategoryTheory.Over.pullback i) (CategoryTheory.Over.pullback j)),
    AlgebraicGeometry.Flat
        (AlgebraicGeometry.Scheme.Pushout.ClosedImmersion.inducedMap i j P) ↔
      AlgebraicGeometry.Flat P.fst.hom ∧ AlgebraicGeometry.Flat P.snd.hom)

/- Lemma 37.67.9 (3): the induced morphism of pushouts is flat and locally of
finite presentation exactly when both component morphisms have both properties. -/
@[stacks 0CYY]
#check (AlgebraicGeometry.Scheme.Pushout.ClosedImmersion.inducedMap_flat_locallyOfFinitePresentation_iff :
  ∀ {Z X Y : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsClosedImmersion j]
    (P : CategoryTheory.Limits.CategoricalPullback
      (CategoryTheory.Over.pullback i) (CategoryTheory.Over.pullback j)),
    (AlgebraicGeometry.Flat
          (AlgebraicGeometry.Scheme.Pushout.ClosedImmersion.inducedMap i j P) ∧
        AlgebraicGeometry.LocallyOfFinitePresentation
          (AlgebraicGeometry.Scheme.Pushout.ClosedImmersion.inducedMap i j P)) ↔
      (AlgebraicGeometry.Flat P.fst.hom ∧
          AlgebraicGeometry.LocallyOfFinitePresentation P.fst.hom) ∧
        (AlgebraicGeometry.Flat P.snd.hom ∧
          AlgebraicGeometry.LocallyOfFinitePresentation P.snd.hom))

/- Lemma 37.67.9 (4): the induced morphism of pushouts is smooth exactly when
both component morphisms are smooth. -/
@[stacks 0CYY]
#check (AlgebraicGeometry.Scheme.Pushout.ClosedImmersion.inducedMap_smooth_iff :
  ∀ {Z X Y : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsClosedImmersion j]
    (P : CategoryTheory.Limits.CategoricalPullback
      (CategoryTheory.Over.pullback i) (CategoryTheory.Over.pullback j)),
    AlgebraicGeometry.Smooth
        (AlgebraicGeometry.Scheme.Pushout.ClosedImmersion.inducedMap i j P) ↔
      AlgebraicGeometry.Smooth P.fst.hom ∧ AlgebraicGeometry.Smooth P.snd.hom)

/- Lemma 37.67.9 (5): the induced morphism of pushouts is étale exactly when
both component morphisms are étale. -/
@[stacks 0CYY]
#check (AlgebraicGeometry.Scheme.Pushout.ClosedImmersion.inducedMap_etale_iff :
  ∀ {Z X Y : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsClosedImmersion j]
    (P : CategoryTheory.Limits.CategoricalPullback
      (CategoryTheory.Over.pullback i) (CategoryTheory.Over.pullback j)),
    AlgebraicGeometry.Etale
        (AlgebraicGeometry.Scheme.Pushout.ClosedImmersion.inducedMap i j P) ↔
      AlgebraicGeometry.Etale P.fst.hom ∧ AlgebraicGeometry.Etale P.snd.hom)
