/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stein.Etale
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 58.15.1 (1): under the hypotheses of the lemma, the structural morphism
from the Stein factorization, represented by `f.fromNormalization`, is finite. -/
@[stacks 0BUN] #check
  (AlgebraicGeometry.Scheme.Hom.instIsFiniteFromNormalizationOfFlatGeometricallyReduced :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [IsProper f]
      [AlgebraicGeometry.Scheme.Hom.FinitePresentation f] [Flat f]
      [AlgebraicGeometry.GeometricallyReduced f],
      AlgebraicGeometry.IsFinite f.fromNormalization)

/- Lemma 58.15.1 (2): under the hypotheses of the lemma, the structural morphism
from the Stein factorization, represented by `f.fromNormalization`, is étale. -/
@[stacks 0BUN] #check
  (AlgebraicGeometry.Scheme.Hom.instEtaleFromNormalizationOfFlatGeometricallyReduced :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [IsProper f]
      [AlgebraicGeometry.Scheme.Hom.FinitePresentation f] [Flat f]
      [AlgebraicGeometry.GeometricallyReduced f],
      AlgebraicGeometry.Etale f.fromNormalization)
