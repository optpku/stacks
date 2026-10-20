/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.BaseChange

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 35.22.2 (1): an fpqc-local property on the target is preserved by
base change along a flat morphism. -/
@[stacks 04QU] #check
  (CategoryTheory.MorphismProperty.IsLocalAtTarget.of_isPullback_fpqc :
    ∀ {P : MorphismProperty Scheme.{u}} {X Y X' Y' : Scheme.{u}}
      {f : X ⟶ Y} {g : Y' ⟶ Y} {i : X' ⟶ X} {f' : X' ⟶ Y'}
      [P.IsLocalAtTarget Scheme.fpqcPrecoverage] [Flat g],
      IsPullback i f' f g → P f → P f')

/- Lemma 35.22.2 (2): an fppf-local property on the target is preserved by
base change along a flat, locally finitely presented morphism. -/
@[stacks 04QU] #check
  (CategoryTheory.MorphismProperty.IsLocalAtTarget.of_isPullback_fppf :
    ∀ {P : MorphismProperty Scheme.{u}} {X Y X' Y' : Scheme.{u}}
      {f : X ⟶ Y} {g : Y' ⟶ Y} {i : X' ⟶ X} {f' : X' ⟶ Y'}
      [P.IsLocalAtTarget Scheme.fppfPrecoverage] [Flat g]
      [LocallyOfFinitePresentation g],
      IsPullback i f' f g → P f → P f')

/- Lemma 35.22.2 (3): a syntomic-local property on the target is preserved by
base change along a syntomic morphism. -/
@[stacks 04QU] #check
  (CategoryTheory.MorphismProperty.IsLocalAtTarget.of_isPullback_syntomic :
    ∀ {P : MorphismProperty Scheme.{u}} {X Y X' Y' : Scheme.{u}}
      {f : X ⟶ Y} {g : Y' ⟶ Y} {i : X' ⟶ X} {f' : X' ⟶ Y'}
      [P.IsLocalAtTarget Scheme.bigSyntomicPrecoverage] [Syntomic g],
      IsPullback i f' f g → P f → P f')

/- Lemma 35.22.2 (4): a smooth-local property on the target is preserved by
base change along a smooth morphism. -/
@[stacks 04QU] #check
  (CategoryTheory.MorphismProperty.IsLocalAtTarget.of_isPullback_smooth :
    ∀ {P : MorphismProperty Scheme.{u}} {X Y X' Y' : Scheme.{u}}
      {f : X ⟶ Y} {g : Y' ⟶ Y} {i : X' ⟶ X} {f' : X' ⟶ Y'}
      [P.IsLocalAtTarget Scheme.bigSmoothPrecoverage] [Smooth g],
      IsPullback i f' f g → P f → P f')

/- Lemma 35.22.2 (5): an étale-local property on the target is preserved by
base change along an étale morphism. -/
@[stacks 04QU] #check
  (CategoryTheory.MorphismProperty.IsLocalAtTarget.of_isPullback_etale :
    ∀ {P : MorphismProperty Scheme.{u}} {X Y X' Y' : Scheme.{u}}
      {f : X ⟶ Y} {g : Y' ⟶ Y} {i : X' ⟶ X} {f' : X' ⟶ Y'}
      [P.IsLocalAtTarget Scheme.etalePrecoverage] [Etale g],
      IsPullback i f' f g → P f → P f')

/- Lemma 35.22.2 (6): a Zariski-local property on the target is preserved by
base change along an open immersion. -/
@[stacks 04QU] #check
  (CategoryTheory.MorphismProperty.IsLocalAtTarget.of_isPullback_zariski :
    ∀ {P : MorphismProperty Scheme.{u}} {X Y X' Y' : Scheme.{u}}
      {f : X ⟶ Y} {g : Y' ⟶ Y} {i : X' ⟶ X} {f' : X' ⟶ Y'}
      [P.IsLocalAtTarget Scheme.zariskiPrecoverage] [IsOpenImmersion g],
      IsPullback i f' f g → P f → P f')
