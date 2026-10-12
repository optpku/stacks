/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Noetherian
import StacksCheckRecall

@[expose] public section

universe u

/-!
# Lemma 28.13.8

The Noetherian and universally Japanese characterization of `Scheme.Nagata`
lives in `ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Noetherian`.
-/

/- Lemma 28.13.8

A scheme is Nagata if and only if it is locally Noetherian and universally Japanese.
-/
@[stacks 033Z]
#check (AlgebraicGeometry.Scheme.nagata_iff_isLocallyNoetherian_and_universallyJapanese :
  ∀ X : AlgebraicGeometry.Scheme.{u}, AlgebraicGeometry.Scheme.Nagata X ↔
    AlgebraicGeometry.IsLocallyNoetherian X ∧
      AlgebraicGeometry.Scheme.UniversallyJapanese X)
#check @AlgebraicGeometry.Scheme.universallyJapanese_of_nagata
#check @AlgebraicGeometry.Scheme.instIsLocallyNoetherianOfNagata
#check @AlgebraicGeometry.Scheme.instUniversallyJapaneseOfNagata
