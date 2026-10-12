/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.QuasiFinite

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Flat

/- Lemma 37.23.5: a flat, locally finitely presented morphism can be factored over any
point in its image through a morphism whose composite is also locally quasi-finite. -/
@[stacks 0571] #check
  (AlgebraicGeometry.Flat.exists_locallyQuasiFinite_factorization :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
      (s : S), s ∈ Set.range f →
      ∃ (S' : Scheme.{u}) (h : S' ⟶ X),
        ∃ _ : Flat (h ≫ f),
          ∃ _ : LocallyOfFinitePresentation (h ≫ f),
            ∃ _ : LocallyQuasiFinite (h ≫ f),
              s ∈ Set.range (h ≫ f))

end AlgebraicGeometry.Flat
