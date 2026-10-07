module

public import stacks_project.Chap74.Lemma_74_10_2_BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

universe u

/- Lemma 74.10.2 (1): an fpqc-local property of morphisms of algebraic spaces
over a scheme `S` is preserved by base change along a flat morphism. -/
@[stacks 06EM] #check
  (AlgebraicGeometry.AlgebraicSpace.IsLocalAtTarget.of_isPullback_fpqc :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
      {X Y X' Y' : AlgebraicSpace S}
      {f : X ⟶ Y} {g : Y' ⟶ Y} {i : X' ⟶ X} {f' : X' ⟶ Y'}
      [P.IsLocalAtTarget (fpqcPrecoverage S)] [Flat g],
      IsPullback i f' f g → P f → P f')

/- Lemma 74.10.2 (2): an fppf-local property of morphisms of algebraic spaces
over a scheme `S` is preserved by base change along a flat, locally finitely
presented morphism. -/
@[stacks 06EM] #check
  (AlgebraicGeometry.AlgebraicSpace.IsLocalAtTarget.of_isPullback_fppf :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
      {X Y X' Y' : AlgebraicSpace S}
      {f : X ⟶ Y} {g : Y' ⟶ Y} {i : X' ⟶ X} {f' : X' ⟶ Y'}
      [P.IsLocalAtTarget (fppfPrecoverage S)] [Flat g]
      [LocallyOfFinitePresentation g],
      IsPullback i f' f g → P f → P f')

/- Lemma 74.10.2 (3): a syntomic-local property of morphisms of algebraic spaces
over a scheme `S` is preserved by base change along a syntomic morphism. -/
@[stacks 06EM] #check
  (AlgebraicGeometry.AlgebraicSpace.IsLocalAtTarget.of_isPullback_syntomic :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
      {X Y X' Y' : AlgebraicSpace S}
      {f : X ⟶ Y} {g : Y' ⟶ Y} {i : X' ⟶ X} {f' : X' ⟶ Y'}
      [P.IsLocalAtTarget (syntomicPrecoverage S)] [Syntomic g],
      IsPullback i f' f g → P f → P f')

/- Lemma 74.10.2 (4): a smooth-local property of morphisms of algebraic spaces
over a scheme `S` is preserved by base change along a smooth morphism. -/
@[stacks 06EM] #check
  (AlgebraicGeometry.AlgebraicSpace.IsLocalAtTarget.of_isPullback_smooth :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
      {X Y X' Y' : AlgebraicSpace S}
      {f : X ⟶ Y} {g : Y' ⟶ Y} {i : X' ⟶ X} {f' : X' ⟶ Y'}
      [P.IsLocalAtTarget (smoothPrecoverage S)] [Smooth g],
      IsPullback i f' f g → P f → P f')

/- Lemma 74.10.2 (5): an étale-local property of morphisms of algebraic spaces
over a scheme `S` is preserved by base change along an étale morphism. -/
@[stacks 06EM] #check
  (AlgebraicGeometry.AlgebraicSpace.IsLocalAtTarget.of_isPullback_etale :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
      {X Y X' Y' : AlgebraicSpace S}
      {f : X ⟶ Y} {g : Y' ⟶ Y} {i : X' ⟶ X} {f' : X' ⟶ Y'}
      [P.IsLocalAtTarget etalePrecoverage] [Etale g],
      IsPullback i f' f g → P f → P f')
