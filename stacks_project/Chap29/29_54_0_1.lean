/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Coproduct

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- 29.54.0.1: the canonical morphism from the coproduct of the spectra of the residue fields
at the generic points of `X` to `X`. -/
@[stacks 035M] #check
  (AlgebraicGeometry.genericPointSpectrumCoproductTo :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      (∐ fun η : genericPoints X ↦ AlgebraicGeometry.Spec (X.residueField η.1)) ⟶ X)
