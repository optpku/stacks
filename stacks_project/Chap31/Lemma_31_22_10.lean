module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Syntomic
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 31.22.10: in a commutative triangle `Y -i-> X -f-> S` and `Y -p-> S`,
if `p` is syntomic, `f` is smooth, and `i` is an immersion, then `i` is a regular immersion. -/
@[stacks 067T] #check
  (AlgebraicGeometry.isRegularImmersion_of_syntomic_of_smooth_of_isImmersion :
    ∀ {Y X S : Scheme.{u}} (i : Y ⟶ X) (p : Y ⟶ S) (f : X ⟶ S) [IsImmersion i],
      i ≫ f = p → Syntomic p → Smooth f → IsRegularImmersion i)
