/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Normalization.Reduction

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.54.2

Let `X` be a scheme such that every quasi-compact open has finitely many
irreducible components. The normalization morphism factors through the
reduction of `X`.
-/
@[stacks 035O] #check
  (AlgebraicGeometry.Scheme.Normalization.factorsThroughReduction :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X],
      ∃ νred : X.normalization ⟶ X.reduction,
        νred ≫ X.reductionι = X.normalizationTo)

#check
  (AlgebraicGeometry.Scheme.Normalization.reductionFactorIsNormalization :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
      {νred : X.normalization ⟶ X.reduction},
      νred ≫ X.reductionι = X.normalizationTo →
        ∃ e : X.normalization ≅ X.reduction.normalization,
          νred = e.hom ≫ X.reduction.normalizationTo)
