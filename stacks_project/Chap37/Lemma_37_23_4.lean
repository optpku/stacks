/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay.Slicing

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 37.23.4: a locally finitely presented morphism that is Cohen--Macaulay
at a fibrewise closed point admits a regular immersion through that point whose
composite to the base is flat, locally finitely presented, and locally
quasi-finite, with set-theoretic fibre equal to that point. -/
@[stacks 0570]
#check
  (AlgebraicGeometry.Scheme.Hom.CohenMacaulayAt.exists_regularImmersion_flat_locallyQuasiFinite :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
      (x : X), f.CohenMacaulayAt x →
        f.asFiber x ∈ closedPoints (f.fiber (f x)) →
          ∃ Z : Scheme.{u},
            ∃ i : Z ⟶ X,
              ∃ _ : x ∈ Set.range i,
                ∃ _ : IsRegularImmersion i,
                  ∃ _ : Flat (i ≫ f),
                    ∃ _ : LocallyOfFinitePresentation (i ≫ f),
                      ∃ _ : LocallyQuasiFinite (i ≫ f),
                        Set.range ((i ≫ f).fiberι (f x) ≫ i) = {x})
