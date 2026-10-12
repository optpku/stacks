/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.UniversallyOpen
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.75.6: a locally finite-type, locally quasi-finite scheme morphism with an
everywhere strictly positive integer-valued weighting is universally open. -/
@[stacks 0F3C] #check
  (AlgebraicGeometry.Scheme.Hom.IsWeighting.universallyOpen :
    ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} [LocallyOfFiniteType f] [LocallyQuasiFinite f]
      {w : X → ℤ}, f.IsWeighting w → (∀ x : X, 0 < w x) → UniversallyOpen f)

end AlgebraicGeometry.Scheme.Hom
