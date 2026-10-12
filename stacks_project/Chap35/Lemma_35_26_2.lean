/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtSource.Composition
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 35.26.2 (1): an fpqc-local property on the source is preserved by
precomposition with a flat morphism. -/
@[stacks 04QV] #check
  (CategoryTheory.MorphismProperty.IsLocalAtSource.respectsLeft_flat_of_fpqc :
    ∀ {P : MorphismProperty Scheme.{u}}
        [P.IsLocalAtSource Scheme.fpqcPrecoverage],
      P.RespectsLeft (@Flat : MorphismProperty Scheme.{u}))

/- Lemma 35.26.2 (2): an fppf-local property on the source is preserved by
precomposition with a flat morphism locally of finite presentation. -/
@[stacks 04QV] #check
  (CategoryTheory.MorphismProperty.IsLocalAtSource.respectsLeft_flat_finitePresentation_of_fppf :
    ∀ {P : MorphismProperty Scheme.{u}}
        [P.IsLocalAtSource Scheme.fppfPrecoverage],
      P.RespectsLeft
        ((@Flat : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFinitePresentation))

/- Lemma 35.26.2 (3): a syntomic-local property on the source is preserved by
precomposition with a syntomic morphism. -/
@[stacks 04QV] #check
  (CategoryTheory.MorphismProperty.IsLocalAtSource.respectsLeft_syntomic :
    ∀ {P : MorphismProperty Scheme.{u}}
        [P.IsLocalAtSource Scheme.bigSyntomicPrecoverage],
      P.RespectsLeft (@Syntomic : MorphismProperty Scheme.{u}))

/- Lemma 35.26.2 (4): a smooth-local property on the source is preserved by
precomposition with a smooth morphism. -/
@[stacks 04QV] #check
  (CategoryTheory.MorphismProperty.IsLocalAtSource.respectsLeft_smooth :
    ∀ {P : MorphismProperty Scheme.{u}}
        [P.IsLocalAtSource Scheme.bigSmoothPrecoverage],
      P.RespectsLeft (@Smooth : MorphismProperty Scheme.{u}))

/- Lemma 35.26.2 (5): an étale-local property on the source is preserved by
precomposition with an étale morphism. -/
@[stacks 04QV] #check
  (CategoryTheory.MorphismProperty.IsLocalAtSource.respectsLeft_etale :
    ∀ {P : MorphismProperty Scheme.{u}}
        [P.IsLocalAtSource Scheme.etalePrecoverage],
      P.RespectsLeft (@Etale : MorphismProperty Scheme.{u}))

/- Lemma 35.26.2 (6): a Zariski-local property on the source is preserved by
precomposition with an open immersion. -/
@[stacks 04QV] #check
  (CategoryTheory.MorphismProperty.IsLocalAtSource.respectsLeft_isOpenImmersion_of_zariski :
    ∀ {P : MorphismProperty Scheme.{u}}
        [P.IsLocalAtSource Scheme.zariskiPrecoverage],
      P.RespectsLeft (@IsOpenImmersion : MorphismProperty Scheme.{u}))
