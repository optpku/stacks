/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.K0.Support.Comparison

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.K0'

/- Lemma 42.56.9: Let `X` be a Noetherian regular scheme and let `Z` be a closed
subscheme of `X`. The maps from supported coherent and perfect `K₀` are mutually inverse. -/
@[stacks 0FER] #check (AlgebraicGeometry.Scheme.K0'.equivK0WithSupport :
  ∀ {X Z : Scheme.{u}} [IsNoetherian X] [Scheme.Regular X]
    (i : Z ⟶ X) [IsClosedImmersion i],
    @K0' Z (LocallyOfFiniteType.isLocallyNoetherian i) ≃+
      K0WithSupport X (Set.range i.base))

end AlgebraicGeometry.Scheme.K0'
