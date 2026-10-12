/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap74.Lemma_74_14_2_Composition
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

/- Lemma 74.14.2 (1): an fpqc-local property on the source is preserved by
precomposition with a flat morphism. -/
@[stacks 06EQ] #check
  (CategoryTheory.MorphismProperty.IsLocalAtSource.respectsLeft_flat_of_fpqc :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
        [P.IsLocalAtSource (fpqcPrecoverage S)],
      P.RespectsLeft (@Flat S : MorphismProperty (AlgebraicSpace S)))

/- Lemma 74.14.2 (2): an fppf-local property on the source is preserved by
precomposition with a morphism that is flat and locally of finite presentation. -/
@[stacks 06EQ] #check
  (CategoryTheory.MorphismProperty.IsLocalAtSource.respectsLeft_flat_finitePresentation_of_fppf :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
        [P.IsLocalAtSource (fppfPrecoverage S)],
      P.RespectsLeft
        ((@Flat S : MorphismProperty (AlgebraicSpace S)) ⊓
          @LocallyOfFinitePresentation S))

/- Lemma 74.14.2 (3): a syntomic-local property on the source is preserved by
precomposition with a syntomic morphism. -/
@[stacks 06EQ] #check
  (CategoryTheory.MorphismProperty.IsLocalAtSource.respectsLeft_syntomic :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
        [P.IsLocalAtSource (AlgebraicSpace.precoverage (@Syntomic S))],
      P.RespectsLeft (@Syntomic S : MorphismProperty (AlgebraicSpace S)))

/- Lemma 74.14.2 (4): a smooth-local property on the source is preserved by
precomposition with a smooth morphism. -/
@[stacks 06EQ] #check
  (CategoryTheory.MorphismProperty.IsLocalAtSource.respectsLeft_smooth :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
        [P.IsLocalAtSource (AlgebraicSpace.precoverage (@Smooth S))],
      P.RespectsLeft (@Smooth S : MorphismProperty (AlgebraicSpace S)))

/- Lemma 74.14.2 (5): an étale-local property on the source is preserved by
precomposition with an étale morphism. -/
@[stacks 06EQ] #check
  (CategoryTheory.MorphismProperty.IsLocalAtSource.respectsLeft_etale :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
        [P.IsLocalAtSource etalePrecoverage],
      P.RespectsLeft (@Etale S : MorphismProperty (AlgebraicSpace S)))
